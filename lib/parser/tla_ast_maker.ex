defmodule ElixirToTlaGenerator.Parser.TlaAstMaker do
  def make_ast(elixir_data) do
    [tlagen_name, parameters, full_guards, function_groups] = elixir_data

    module = %Tla.Ast.Module{
      name: Atom.to_string(tlagen_name),
      # For now, the extensions are hardcoded, as all the ones needed for fibonacciare already
      # covered by those needed for creating the stack memory representation it self
      extends: ["Naturals", "TLC", "Sequences"],
      constants:
        parameters
        |> Enum.map(
          &(&1
            |> get_atom
            |> Atom.to_string()
            |> ElixirToTlaGenerator.Utils.String.snake_to_camel()
            |> make_constant)
        ),
      # Variables hardcoded to fit the stack implementation of the specification
      variables: [%Tla.Ast.Variable{name: "stack"}, %Tla.Ast.Variable{name: "return"}],
      operators: make_operators(elixir_data)
    }

    IO.chardata_to_string(Tla.Ast.to_tla(module))
    # module
  end

  def make_constant(name), do: %Tla.Ast.Constant{name: name}
  def get_atom({atom, _, _}), do: atom

  def make_operators(elixir_data) do
    # Spec and Init opperators remain the same for all cases as well
    append = %Tla.Ast.Operator{
      name: "AppendToStart",
      parameters: ["item", "list"],
      expression:
        {:concat, {:set, [%Tla.Ast.LocalVariable{name: "item"}]},
         %Tla.Ast.LocalVariable{name: "list"}}
    }

    spec = %Tla.Ast.Operator{
      name: "Spec",
      expression: {
        :and,
        [
          %Tla.Ast.Operator{name: "Init"},
          {:stutter, {:always, %Tla.Ast.Operator{name: "Next"}},
           {:set, [%Tla.Ast.Variable{name: "stack"}]}}
        ]
      }
    }

    [_tlagen_name, parameters, full_guards, function_groups] = elixir_data

    blocks_per_case = Enum.map(function_groups, &length/1)

    steps_per_casse =
      Enum.map(function_groups, fn x ->
        x
        |> List.flatten()
        |> Enum.reject(fn
          {_, [:__block__, _]} -> true
          _ -> false
        end)
        |> length()
      end)

    init = make_init(parameters, steps_per_casse)
    next = make_next(full_guards, function_groups)

    [init, append, spec, next]
  end

  def make_init(parameters, steps_per_casse) do
    variables =
      parameters
      |> Enum.map(fn x ->
        x
        |> get_atom()
        |> Atom.to_string()
        |> (fn name ->
              {:assign, %Tla.Ast.LocalVariable{name: name},
               %Tla.Ast.Constant{name: ElixirToTlaGenerator.Utils.String.snake_to_camel(name)}}
            end).()
      end)

    case_results =
      steps_per_casse
      |> Enum.with_index()
      |> Enum.map(fn {x, index} ->
        {:assign, %Tla.Ast.LocalVariable{name: "res_case_#{index + 1}"},
         {:set, List.duplicate("-1", x)}}
      end)

    case_counter = {:assign, %Tla.Ast.LocalVariable{name: "case_counter"}, "1"}
    block_counter = {:assign, %Tla.Ast.LocalVariable{name: "block_counter"}, "1"}

    %Tla.Ast.Operator{
      name: "Init",
      expression:
        {:and,
         [
           {:=, %Tla.Ast.LocalVariable{name: "stack"},
            {
              :set,
              [
                {:arr, variables ++ case_results ++ [case_counter, block_counter]}
              ]
            }},
           {:=, %Tla.Ast.LocalVariable{name: "return"}, "-1"}
         ]}
    }
  end

  def make_next(full_guards, function_groups) do
    case_value_returns =
      function_groups
      |> Enum.with_index()
      |> Enum.map(fn {x, index} -> make_case_value_returns(index, x) end)

    case_blocks =
      function_groups
      |> Enum.with_index()
      |> Enum.map(fn {x, index} ->
        make_case_block(Enum.at(full_guards, index), x, index, length(x) - 1)
      end)

    or_blocks = case_value_returns ++ List.flatten(case_blocks)

    %Tla.Ast.Operator{
      name: "Next",
      expression: {:or, or_blocks}
    }
  end

  def make_case_value_returns(case_number, function) do
    # Guards for checking if the correct case return is being handled
    case_counter_condition =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "case_counter"}}, Integer.to_string(case_number + 1)}

    block_counter_condition =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "block_counter"}},
       Integer.to_string(length(function) + 1)}

    # Hardcoded "pop" operation
    next_stack =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       %Tla.Ast.Operator{
         name: "SubSeq",
         parameters: [
           %Tla.Ast.Variable{name: "stack"},
           "2",
           %Tla.Ast.Operator{
             name: "Len",
             parameters: [
               %Tla.Ast.Variable{name: "stack"}
             ]
           }
         ]
       }}

    # Defines what will be the return of the case
    next_return =
      {:=, {:next, %Tla.Ast.Variable{name: "return"}},
       {
         :access,
         {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
         get_case_return(function |> List.flatten(), case_number)
       }}

    {:and, [case_counter_condition, block_counter_condition, next_stack, next_return]}
  end

  def get_case_return(steps, index) do
    case List.last(steps) do
      {_, [:__block__, operation]} ->
        {return_var, _, nil} = List.last(operation)

        last_step =
          steps
          |> Enum.filter(fn
            {_, [:=, [{atom, _, _}, _]]} -> atom == return_var
            _ -> false
          end)
          |> List.last()

        {last_step_index, _} = last_step

        {:index, %Tla.Ast.LocalVariable{name: "res_case_#{index + 1}"},
         Integer.to_string(last_step_index + 1)}

      {_, {_atom, _, nil}} ->
        # Need to fix this eventually
        {:index, %Tla.Ast.LocalVariable{name: "res_case_#{index + 1}"}, "1"}
    end
  end

  def make_exception_val_return(steps) do
    steps =
      steps
      |> Enum.reject(fn
        {_, [:__block__, _]} -> true
        _ -> false
      end)

    case List.last(steps) do
      {_, {atom, _, _}} ->
        {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
         %Tla.Ast.LocalVariable{name: Atom.to_string(atom)}}
    end
  end

  def guard_to_tla({atom, _, [e1, e2]}) do
    {atom, process_param(e1), process_param(e2)}
  end

  def process_param({atom, _, _})
      when atom == :< or atom == :> or atom == := or atom == :+ or atom == :-,
      do: atom

  def process_param({atom, _, _}) do
    {
      :access,
      {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
      %Tla.Ast.Variable{name: Atom.to_string(atom)}
    }
  end

  def process_param(value) when is_binary(value), do: value
  def process_param(value) when is_number(value), do: Integer.to_string(value)

  def make_case_block(guards, function, case_index, 0) do
    [true_guards, false_guards] = guards

    true_guards_tla = Enum.map(true_guards, &guard_to_tla/1)
    false_guards_tla = Enum.map(false_guards, &guard_to_tla/1)

    case_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "case_counter"}}, Integer.to_string(case_index + 1)}

    block_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "block_counter"}}, "1"}

    stack_if_true =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        [
          {:=, {:exception, "1", %Tla.Ast.LocalVariable{name: "res_case_1"}},
           make_exception_val_return(List.flatten(function))},
          {:=, {:exception, "1", %Tla.Ast.LocalVariable{name: "block_counter"}}, "2"}
        ]}}

    stack_if_false =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        [
          {:=, {:exception, "1", %Tla.Ast.LocalVariable{name: "case_counter"}},
           Integer.to_string(case_index + 2)},
          {:=, {:exception, "1", %Tla.Ast.LocalVariable{name: "block_counter"}}, "1"}
        ]}}

    return =
      {:=, {:next, %Tla.Ast.Variable{name: "return"}}, "-1"}

    case_true =
      {:and,
       [case_counter, block_counter] ++
         true_guards_tla ++
         (false_guards_tla |> Enum.map(fn x -> {:not, x} end)) ++ [stack_if_true, return]}

    case_false =
      {:and,
       [case_counter, block_counter] ++
         (true_guards_tla |> Enum.map(fn x -> {:not, x} end)) ++
         false_guards_tla ++ [stack_if_false, return]}

    [case_true, case_false]
  end

  def make_case_block(guards, function, case_index, recursion_count) do
    # IO.inspect(function |> List.flatten())

    assignment_map =
      function
      |> List.flatten()
      |> Enum.reject(fn
        {index, [:=, [{atom, _, _}, _]]} -> false
        _ -> true
      end)
      |> Enum.map(fn {index, [:=, [{atom, _, _}, _]]} -> {atom, index} end)
      |> Enum.into(%{})

    # IO.inspect(assignment_map)

    {last_block, recursive_blocks} = List.pop_at(function, -1)

    [true_guards, false_guards] = guards

    true_guards_tla = Enum.map(true_guards, &guard_to_tla/1)
    false_guards_tla = Enum.map(false_guards, &guard_to_tla/1)
    guards_ast = true_guards_tla ++ (false_guards_tla |> Enum.map(fn x -> {:not, x} end))

    step_count =
      function
      |> List.flatten()
      |> Enum.reject(fn
        {_, [:__block__, _]} -> true
        _ -> false
      end)
      |> length()

    recursive_steps_ast =
      recursive_blocks
      |> Enum.with_index()
      |> Enum.map(fn {x, index} ->
        make_recursive_block(
          x,
          index,
          case_index,
          recursion_count,
          guards_ast,
          assignment_map,
          step_count
        )
      end)

    last_step_ast =
      make_last_block(last_block, case_index, recursion_count, guards_ast, assignment_map)

    [recursive_steps_ast, last_step_ast]
  end

  def make_recursive_block(
        block,
        block_index,
        case_index,
        recursion_count,
        guards_ast,
        assignment_map,
        step_count
      ) do
    {recursion, assignments} = List.pop_at(block, -1)
    {_, [_, [{:fn_nr, recursive_param_nr}]]} = recursion

    case_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "case_counter"}}, Integer.to_string(case_index + 1)}

    block_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "block_counter"}}, Integer.to_string(block_index + 1)}

    current_return =
      {:=, %Tla.Ast.Variable{name: "return"}, "-1"}

    next_return =
      {:=, {:next, %Tla.Ast.Variable{name: "return"}}, "-1"}

    except_recursive_call =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       %Tla.Ast.Operator{
         name: "AppendToStart",
         parameters: [
           {:except, %Tla.Ast.Variable{name: "stack"},
            [
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "n"}},
               "fn_nr_#{recursive_param_nr + 1}"},
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "case_counter"}}, "1"},
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "block_counter"}}, "1"},
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "res_case#{case_index + 1}"}},
               {:set, List.duplicate("-1", step_count)}}
            ]},
           %Tla.Ast.Variable{name: "stack"}
         ]
       }}

    {recursion_index, _} = List.last(assignments)

    block_results =
      assignments |> Enum.map(fn x -> make_results(x, case_index, assignment_map) end)

    except_return_assign =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        (assignments
         |> Enum.map(fn {step_index, _} ->
           {:=,
            {:exception, "1",
             {:index, %Tla.Ast.LocalVariable{name: "res_case_#{case_index + 1}"},
              Integer.to_string(step_index + 1)}},
            %Tla.Ast.Variable{name: "fn_nr_#{step_index + 1}"}}
         end)) ++
          [
            {:=,
             {:exception, "1",
              {:index, %Tla.Ast.LocalVariable{name: "res_case_#{case_index + 1}"},
               Integer.to_string(recursion_index + 2)}}, %Tla.Ast.Variable{name: "return"}},
            {:=, {:exception, "1", %Tla.Ast.LocalVariable{name: "block_counter"}},
             Integer.to_string(block_index + 2)}
          ]}}

    [
      {:and,
       [case_counter, block_counter] ++
         guards_ast ++ block_results ++ [current_return, except_recursive_call, next_return]},
      {:and,
       [case_counter, block_counter] ++
         guards_ast ++
         block_results ++ [{:not, current_return}, except_return_assign, next_return]}
    ]
  end

  def make_last_block(block, case_index, recursion_count, guards_ast, assignment_map) do
    case_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "case_counter"}}, Integer.to_string(case_index + 1)}

    block_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.LocalVariable{name: "block_counter"}}, Integer.to_string(recursion_count + 2)}

    current_return =
      {:=, %Tla.Ast.Variable{name: "return"}, "-1"}

    next_return =
      {:=, {:next, %Tla.Ast.Variable{name: "return"}}, "-1"}

    block =
      block
      |> Enum.reject(fn
        {_, [:__block__, _]} -> true
        _ -> false
      end)

    block_results = block |> Enum.map(fn x -> make_results(x, case_index, assignment_map) end)

    stack_except =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        block
        |> Enum.map(fn {step_index, _} ->
          {:=,
           {:exception, "1",
            {:index, %Tla.Ast.LocalVariable{name: "res_case_#{case_index + 1}"},
             Integer.to_string(step_index + 1)}},
           %Tla.Ast.Variable{name: "fn_nr_#{step_index + 1}"}}
        end)}}

    {:and,
     [case_counter, block_counter] ++
       guards_ast ++ block_results ++ [current_return, stack_except, next_return]}
  end

  def get_param({val, _, _}), do: val
  def get_param(val), do: val

  def make_results(
        {step_index, [:=, [{atom, _, _}, {:fn_nr, fn_nr}]]},
        case_index,
        _assignment_map
      ) do
    {:=, %Tla.Ast.LocalVariable{name: "fn_nr_#{step_index + 1}"},
     {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
      {:index, %Tla.Ast.LocalVariable{name: "res_case_#{case_index + 1}"},
       Integer.to_string(fn_nr + 1)}}}
  end

  def make_results({step_index, [atom, [e1, e2]]}, case_index, assignment_map) do
    val1 = get_param(e1)
    val2 = get_param(e2)

    val1 =
      case Map.get(assignment_map, val1) do
        nil ->
          case val1 do
            :n ->
              {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
               %Tla.Ast.Variable{name: "n"}}

            atom ->
              case is_integer(atom) do
                true -> Integer.to_string(atom)
                false -> atom
              end
          end

        fn_nr ->
          {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
           {:index, %Tla.Ast.LocalVariable{name: "res_case_#{case_index + 1}"},
            Integer.to_string(fn_nr + 1)}}
      end

    val2 =
      case Map.get(assignment_map, val2) do
        nil ->
          case val2 do
            :n ->
              {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
               %Tla.Ast.Variable{name: "n"}}

            atom ->
              case is_integer(atom) do
                true -> Integer.to_string(atom)
                false -> atom
              end
          end

        fn_nr ->
          {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
           {:index, %Tla.Ast.LocalVariable{name: "res_case_#{case_index + 1}"},
            Integer.to_string(fn_nr + 1)}}
      end

    {:=, %Tla.Ast.LocalVariable{name: "fn_nr_#{step_index + 1}"}, {atom, val1, val2}}
  end
end

"---- MODULE fibonacci ----\n
EXTENDS Naturals,TLC,Sequences\n
CONSTANT N\n
VARIABLE stack\n
VARIABLE return\n
Init == (stack = <<[n |-> N,res_case_1 |-> <<-1>>,res_case_2 |-> <<-1,-1,-1,-1,-1,-1,-1,-1>>,case_counter |-> 1,block_counter |-> 1]>>) /\\ (return = -1)\nAppendToStart(item, list) == <<item>> \\o list\n
Spec == (Init) /\\ ([][Next]_<<stack>>)\n
Next ==
        ((stack[1].case_counter = 1) /\\ (stack[1].block_counter = 2) /\\ (stack' = SubSeq(stack2Len(stack))) /\\ (return' = stack[1].res_case_1[1]))
    \\/ ((stack[1].case_counter = 2) /\\ (stack[1].block_counter = 4) /\\ (stack' = SubSeq(stack2Len(stack))) /\\ (return' = stack[1].res_case_2[8]))
    \\/ ((stack[1].case_counter = 1) /\\ (stack[1].block_counter = 1) /\\ (stack[1].n < 2) /\\ (stack' = [stack EXCEPT ![1].res_case_1 = stack[1].n,![1].block_counter = 2]) /\\ (return' = -1))
    \\/ ((stack[1].case_counter = 1) /\\ (stack[1].block_counter = 1) /\\ (~(stack[1].n < 2)) /\\ (stack' = [stack EXCEPT ![1].case_counter = 2,![1].block_counter = 1]) /\\ (return' = -1))
    \\/ ((stack[1].case_counter = 2) /\\ (stack[1].block_counter = 1) /\\ (~(stack[1].n < 2)) /\\ (fn_nr_1 = stack[1].n - 1) /\\ (return = -1) /\\ (stack' = AppendToStart([stack EXCEPT !.n = fn_nr_1,!.case_counter = 1,!.block_counter = 1,!.res_case2 = <<-1,-1,-1,-1,-1,-1,-1,-1>>]stack)) /\\ (return' = -1))
    \\/ ((stack[1].case_counter = 2) /\\ (stack[1].block_counter = 1) /\\ (~(stack[1].n < 2)) /\\ (fn_nr_1 = stack[1].n - 1) /\\ (~(return = -1)) /\\ (stack' = [stack EXCEPT ![1].res_case_2[1] = fn_nr_1,![1].res_case_2[2] = return,![1].block_counter = 2]) /\\ (return' = -1))
    \\/ ((stack[1].case_counter = 2) /\\ (stack[1].block_counter = 2) /\\ (~(stack[1].n < 2)) /\\ (fn_nr_3 = stack[1].res_case_2[2]) /\\ (fn_nr_4 = stack[1].n - 2) /\\ (return = -1) /\\ (stack' = AppendToStart([stack EXCEPT !.n = fn_nr_4,!.case_counter = 1,!.block_counter = 1,!.res_case2 = <<-1,-1,-1,-1,-1,-1,-1,-1>>]stack)) /\\ (return' = -1))
    \\/ ((stack[1].case_counter = 2) /\\ (stack[1].block_counter = 2) /\\ (~(stack[1].n < 2)) /\\ (fn_nr_3 = stack[1].res_case_2[2]) /\\ (fn_nr_4 = stack[1].n - 2) /\\ (~(return = -1)) /\\ (stack' = [stack EXCEPT ![1].res_case_2[3] = fn_nr_3,![1].res_case_2[4] = fn_nr_4,![1].res_case_2[5] = return,![1].block_counter = 3]) /\\ (return' = -1))
    \\/ ((stack[1].case_counter = 2) /\\ (stack[1].block_counter = 4) /\\ (~(stack[1].n < 2)) /\\ (fn_nr_6 = stack[1].res_case_2[5]) /\\ (fn_nr_7 = stack[1].res_case_2[3] + stack[1].res_case_2[6]) /\\ (fn_nr_8 = stack[1].res_case_2[7]) /\\ (return = -1) /\\ (stack' = [stack EXCEPT ![1].res_case_2[6] = fn_nr_6,![1].res_case_2[7] = fn_nr_7,![1].res_case_2[8] = fn_nr_8]) /\\ (return' = -1))\n
====\n"
