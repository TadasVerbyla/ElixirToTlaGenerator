defmodule ElixirToTlaGenerator.Parser.TlaAstMaker do
  defmodule Context do
    @type t() ::
            String.t()
            | [integer()]
            | [atom()]
            | %{}
    defstruct module_name: nil,
              steps_per_case: nil,
              parameters: nil,
              assignment_maps: nil,
              full_guards: nil,
              function_groups: nil
  end

  def make_ast([tlagen_name, parameters, full_guards, function_groups]) do
    context = %Context{
      module_name: tlagen_name,
      steps_per_case:
        Enum.map(function_groups, fn x ->
          x
          |> List.flatten()
          |> Enum.reject(fn
            {_, [:__block__, _]} -> true
            _ -> false
          end)
          |> length()
        end),
      parameters: parameters |> Enum.map(fn {atom, _, _} -> atom end),
      assignment_maps:
        function_groups
        |> Enum.map(fn x ->
          x
          |> List.flatten()
          |> Enum.reject(fn
            {_index, [:=, [{_atom, _, _}, _]]} -> false
            _ -> true
          end)
          |> Enum.map(fn {index, [:=, [{atom, _, _}, _]]} -> {atom, index} end)
          |> Enum.into(%{})
        end),
      full_guards: full_guards,
      function_groups: function_groups
    }

    module = %Tla.Ast.Module{
      name: Atom.to_string(tlagen_name),
      # For now, the extensions are hardcoded, as all the ones needed for fibonacciare already
      # covered by those needed for creating the stack memory representation it self
      extends: ["Naturals", "Integers", "TLC", "Sequences"],
      constants:
        context.parameters
        |> Enum.map(fn x ->
          x
          |> Atom.to_string()
          |> ElixirToTlaGenerator.Utils.String.snake_to_camel()
          |> make_constant
        end),
      # Variables hardcoded to fit the stack implementation of the specification
      variables: [%Tla.Ast.Variable{name: "stack"}, %Tla.Ast.Variable{name: "return"}],
      operators: make_operators(context)
    }

    File.write(
      "C:\\Users\\tadas\\Documents\\GitHub\\ElixirToTlaGenerator\\generated_tla\\#{Atom.to_string(tlagen_name)}.tla",
      IO.chardata_to_string(Tla.Ast.to_tla(module))
    )
  end

  def make_constant(name), do: %Tla.Ast.Constant{name: name}
  def get_atom({atom, _, _}), do: atom

  def make_operators(context) do
    # Spec and Init operators remain the same for all cases as well
    append = %Tla.Ast.Operator{
      name: "AppendToSequenceStart",
      parameters: ["item", "list"],
      expression:
        {:concat, {:set, [%Tla.Ast.BoundVariable{name: "item"}]},
         %Tla.Ast.BoundVariable{name: "list"}}
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

    init = make_init(context)
    next = make_next(context)

    [init, append, next, spec]
  end

  def make_init(context) do
    variables =
      context.parameters
      |> Enum.map(fn x ->
        x
        |> Atom.to_string()
        |> (fn name ->
              {:assign, %Tla.Ast.BoundVariable{name: name},
               %Tla.Ast.Constant{name: ElixirToTlaGenerator.Utils.String.snake_to_camel(name)}}
            end).()
      end)

    case_results =
      context.steps_per_case
      |> Enum.with_index()
      |> Enum.map(fn {x, index} ->
        {:assign, %Tla.Ast.BoundVariable{name: "res_case_#{index + 1}"},
         {:set, List.duplicate("-1", x)}}
      end)

    case_counter = {:assign, %Tla.Ast.BoundVariable{name: "case_counter"}, "1"}
    block_counter = {:assign, %Tla.Ast.BoundVariable{name: "block_counter"}, "1"}

    %Tla.Ast.Operator{
      name: "Init",
      expression:
        {:and,
         [
           {:=, %Tla.Ast.BoundVariable{name: "stack"},
            {
              :set,
              [
                {:arr, variables ++ case_results ++ [case_counter, block_counter]}
              ]
            }},
           {:=, %Tla.Ast.BoundVariable{name: "return"}, "-1"}
         ]}
    }
  end

  def make_next(context) do
    case_value_returns =
      context.function_groups
      |> Enum.with_index()
      |> Enum.map(fn {x, index} -> make_case_value_returns(index, x) end)

    case_blocks =
      context.function_groups
      |> Enum.with_index()
      |> Enum.map(fn {x, index} ->
        make_case_block(index, length(x) - 1, context)
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
        }, %Tla.Ast.BoundVariable{name: "case_counter"}}, Integer.to_string(case_number + 1)}

    block_counter_condition =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.BoundVariable{name: "block_counter"}},
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

        {:index, %Tla.Ast.BoundVariable{name: "res_case_#{index + 1}"},
         Integer.to_string(last_step_index + 1)}

      {_, {_atom, _, nil}} ->
        # Need to fix this eventually
        {:index, %Tla.Ast.BoundVariable{name: "res_case_#{index + 1}"}, "1"}
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
         %Tla.Ast.BoundVariable{name: Atom.to_string(atom)}}
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

  def make_case_block(case_index, 0, context) do
    guards = context.full_guards |> Enum.at(case_index)
    function = context.function_groups |> Enum.at(case_index)
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
        }, %Tla.Ast.BoundVariable{name: "case_counter"}}, Integer.to_string(case_index + 1)}

    block_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.BoundVariable{name: "block_counter"}}, "1"}

    stack_if_true =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        [
          {:=, {:exception, "1", {:index, %Tla.Ast.BoundVariable{name: "res_case_1"}, "1"}},
           make_exception_val_return(List.flatten(function))},
          {:=, {:exception, "1", %Tla.Ast.BoundVariable{name: "block_counter"}}, "2"}
        ]}}

    stack_if_false =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        [
          {:=, {:exception, "1", %Tla.Ast.BoundVariable{name: "case_counter"}},
           Integer.to_string(case_index + 2)},
          {:=, {:exception, "1", %Tla.Ast.BoundVariable{name: "block_counter"}}, "1"}
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

  def make_case_block(case_index, recursion_count, context) do
    guards = context.full_guards |> Enum.at(case_index)
    function = context.function_groups |> Enum.at(case_index)
    assignment_map = context.assignment_maps |> Enum.at(case_index)

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
          guards_ast,
          assignment_map,
          step_count,
          context.parameters
        )
      end)

    last_step_ast =
      make_last_block(
        last_block,
        case_index,
        recursion_count,
        guards_ast,
        assignment_map,
        context.parameters
      )

    [recursive_steps_ast, last_step_ast]
  end

  def make_recursive_block(
        block,
        block_index,
        case_index,
        guards_ast,
        assignment_map,
        step_count,
        parameters
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
        }, %Tla.Ast.BoundVariable{name: "case_counter"}}, Integer.to_string(case_index + 1)}

    block_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.BoundVariable{name: "block_counter"}}, Integer.to_string(block_index + 1)}

    current_return =
      {:=, %Tla.Ast.Variable{name: "return"}, "-1"}

    next_return =
      {:=, {:next, %Tla.Ast.Variable{name: "return"}}, "-1"}

    except_recursive_call =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       %Tla.Ast.Operator{
         name: "AppendToSequenceStart",
         parameters: [
           {:except, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
            [
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "n"}},
               "fn_nr_#{recursive_param_nr + 1}"},
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "case_counter"}}, "1"},
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "block_counter"}}, "1"},
              {:=, {:exception, {}, %Tla.Ast.Variable{name: "res_case_#{case_index + 1}"}},
               {:set, List.duplicate("-1", step_count)}}
            ]},
           %Tla.Ast.Variable{name: "stack"}
         ]
       }}

    {recursion_index, _} = List.last(assignments)

    except_return_assign =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        (assignments
         |> Enum.map(fn {step_index, _} ->
           {:=,
            {:exception, "1",
             {:index, %Tla.Ast.BoundVariable{name: "res_case_#{case_index + 1}"},
              Integer.to_string(step_index + 1)}},
            %Tla.Ast.Variable{name: "fn_nr_#{step_index + 1}"}}
         end)) ++
          [
            {:=,
             {:exception, "1",
              {:index, %Tla.Ast.BoundVariable{name: "res_case_#{case_index + 1}"},
               Integer.to_string(recursion_index + 2)}}, %Tla.Ast.Variable{name: "return"}},
            {:=, {:exception, "1", %Tla.Ast.BoundVariable{name: "block_counter"}},
             Integer.to_string(block_index + 2)}
          ]}}

    {block_first_step, _} = Enum.at(block, 0)

    recursive_call_with_let =
      {:let,
       assignments
       |> Enum.map(fn x -> make_results(x, case_index, assignment_map, parameters, block_first_step) end),
       except_recursive_call}

    return_assign_with_let =
      {:let,
       assignments
       |> Enum.map(fn x -> make_results(x, case_index, assignment_map, parameters, block_first_step) end),
       except_return_assign}

    [
      {:and,
       [case_counter, block_counter, current_return] ++
         guards_ast ++ [recursive_call_with_let, next_return]},
      {:and,
       [case_counter, block_counter, {:not, current_return}] ++
         guards_ast ++ [return_assign_with_let, next_return]}
    ]
  end

  def make_last_block(block, case_index, recursion_count, guards_ast, assignment_map, parameters) do
    case_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.BoundVariable{name: "case_counter"}}, Integer.to_string(case_index + 1)}

    block_counter =
      {:=,
       {:access,
        {
          :index,
          %Tla.Ast.Variable{name: "stack"},
          "1"
        }, %Tla.Ast.BoundVariable{name: "block_counter"}}, Integer.to_string(recursion_count + 1)}

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

    res_case_exceptions =
      block
      |> Enum.map(fn {step_index, _} ->
        {:=,
         {:exception, "1",
          {:index, %Tla.Ast.BoundVariable{name: "res_case_#{case_index + 1}"},
           Integer.to_string(step_index + 1)}},
         %Tla.Ast.Variable{name: "fn_nr_#{step_index + 1}"}}
      end)

    stack_except =
      {:=, {:next, %Tla.Ast.Variable{name: "stack"}},
       {:except, %Tla.Ast.Variable{name: "stack"},
        res_case_exceptions ++
          [
            {:=, {:exception, "1", %Tla.Ast.BoundVariable{name: "block_counter"}},
             {:access, {:index, %Tla.Ast.BoundVariable{name: "stack"}, "1"},
              {:+, %Tla.Ast.BoundVariable{name: "block_counter"}, "1"}}}
          ]}}

    {block_first_step, _} = Enum.at(block, 0)

    except_with_let =
      {:let,
       block
       |> Enum.map(fn x ->
         make_results(x, case_index, assignment_map, parameters, block_first_step)
       end), stack_except}

    {:and,
     [case_counter, block_counter, current_return] ++
       guards_ast ++ [except_with_let, next_return]}
  end

  def get_param({val, _, _}), do: val
  def get_param(val), do: val

  def make_results(
        {step_index, [:=, [{_, _, _}, {:fn_nr, fn_nr}]]},
        case_index,
        _assignment_map,
        _parameters,
        block_first_step
      ) do
    case block_first_step > fn_nr do
      true ->
        {:==, %Tla.Ast.BoundVariable{name: "fn_nr_#{step_index + 1}"},
         {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
          {:index, %Tla.Ast.BoundVariable{name: "res_case_#{case_index + 1}"},
           Integer.to_string(fn_nr + 1)}}}

      false ->
        {:==, %Tla.Ast.BoundVariable{name: "fn_nr_#{step_index + 1}"},
         %Tla.Ast.BoundVariable{name: "fn_nr_#{fn_nr + 1}"}}
    end
  end

  def make_results(
        {step_index, [atom, [e1, e2]]},
        case_index,
        assignment_map,
        parameters,
        block_first_step
      ) do
    val1 = get_param(e1)
    val2 = get_param(e2)

    val1 = get_value(val1, parameters, case_index, assignment_map, block_first_step)

    val2 = get_value(val2, parameters, case_index, assignment_map, block_first_step)

    {:==, %Tla.Ast.BoundVariable{name: "fn_nr_#{step_index + 1}"}, {atom, val1, val2}}
  end

  def get_value(value, parameters, case_index, assignment_map, block_first_step) do
    case Map.get(assignment_map, value) do
      nil ->
        case Enum.member?(parameters, value) do
          true ->
            {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
             %Tla.Ast.Variable{name: Atom.to_string(value)}}

          false ->
            case is_integer(value) do
              true -> Integer.to_string(value)
              false -> value
            end
        end

      fn_nr ->
        case block_first_step > fn_nr + 1 do
          true ->
            {:access, {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
             {:index, %Tla.Ast.BoundVariable{name: "res_case_#{case_index + 1}"},
              Integer.to_string(fn_nr + 1)}}

          false ->
            %Tla.Ast.BoundVariable{name: "fn_nr_#{fn_nr + 1}"}
        end
    end
  end
end
