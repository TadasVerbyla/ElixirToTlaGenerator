defmodule ElixirToTlaGenerator.Parser.AstParser do
  def parse_ast(ast) do
    [_tlagen_name, clauses] = ast

    headers = get_headers(clauses)
    all_parameters = get_all_parameters(headers)
    guards = get_all_guards(headers)
    clause_names = get_all_clause_names(headers)

    f = fn {atom, _, nil}, acc ->
      case Enum.member?(acc, {atom, [], nil}) do
        true ->
          acc

        false ->
          acc ++ [{atom, [], nil}]
      end
    end

    unique_paramteres =
      Enum.flat_map(all_parameters, & &1)
      |> Enum.reduce([], f)

    full_guards = add_guard_negation(guards)
    unique_clause_names = Enum.uniq(clause_names)
    clause_expressions = get_expressions(clauses)

    flattened_clause_expressions =
      Enum.map(clause_expressions, fn clause ->
        flatten_expression_wrapper(clause)
      end)

    function_groups =
      Enum.map(flattened_clause_expressions, fn flattened_clause ->
        group_flattened_wrapper(flattened_clause, unique_clause_names)
      end)

    # TODO: FIX NUMBERING OF GROUPED ELEMENTS
    [unique_paramteres, full_guards, function_groups]
  end

  # ----------------------------------------------------------------------------

  # Handles headers with multiple conds
  def get_headers([{:defp, _, [{:when, _, header}, _do_block]} | []]) do
    header
  end

  def get_headers([{:defp, _, [{:when, _, header}, _do_block]} | rest]) do
    [header, get_headers(rest)]
  end

  # Handles headers with single cond
  def get_headers([{:defp, _, [header, _do_block]} | []]) do
    [header]
  end

  def get_headers([{:defp, _, [header, _do_block]} | rest]) do
    [[header], get_headers(rest)]
  end

  # ----------------------------------------------------------------------------

  # Gets clause parameters (variables) from headers
  def get_all_parameters([[{_name, _, parameters} | _guards]]) do
    [parameters]
  end

  def get_all_parameters([[{_name, _, parameters} | _guards] | rest]) do
    [parameters | get_all_parameters(rest)]
  end

  # ----------------------------------------------------------------------------

  # Gets clause guards from headers
  def get_all_guards([[_parameters | guards]]) do
    [guards]
  end

  def get_all_guards([[_parameters | guards] | rest]) do
    [guards | get_all_guards(rest)]
  end

  # ----------------------------------------------------------------------------

  # Gets names of each function clause
  def get_all_clause_names([[{name, _, _parameters} | _guards]]) do
    [name]
  end

  def get_all_clause_names([[{name, _, _parameters} | _guards] | rest]) do
    [name | get_all_clause_names(rest)]
  end

  # ----------------------------------------------------------------------------

  def add_guard_negation(guards) do
    Enum.map(guards, fn guard ->
      [guard | Enum.filter(guards, &(&1 != guard))]
    end)
  end

  # ----------------------------------------------------------------------------

  def get_expressions([{_def, _, [_header, [do: body]]} | []]) do
    [body]
  end

  def get_expressions([{_def, _, [_header, [do: body]]} | rest]) do
    [body | get_expressions(rest)]
  end

  # ----------------------------------------------------------------------------

  def flatten_expression({atom, _, parameters}, fn_counter, functions) when is_list(parameters) do
    f = fn parameter, {acc_parameters, acc_counter, acc_functions} ->
      {flattened_parameter, new_fn_counter, new_functions} =
        flatten_expression(parameter, acc_counter, acc_functions)

      {[flattened_parameter] ++ acc_parameters, new_fn_counter, new_functions}
    end

    {new_parameters, new_counter, new_functions} =
      Enum.reduce(
        parameters,
        {[], fn_counter, functions},
        f
      )

    function_parameters = Enum.reverse(new_parameters)
    function = {new_counter, [atom, function_parameters]}
    function_id = {:fn_nr, new_counter}

    {function_id, new_counter + 1, new_functions ++ [function]}
  end

  def flatten_expression(constant, fn_counter, functions)
      when is_number(constant) or is_binary(constant) do
    {constant, fn_counter, functions}
  end

  def flatten_expression(constant, 0, functions)
      when is_number(constant) or is_binary(constant) do
    {constant, 0, functions ++ [{0, constant}]}
  end

  def flatten_expression(constant = {_atom, _, _}, fn_counter, functions) do
    {constant, fn_counter, functions}
  end

  def flatten_expression(constant = {_atom, _, _}, 0, functions) do
    {constant, 0, functions ++ [{0, constant}]}
  end

  # ----------------------------------------------------------------------------

  # @spec flatten_expression_wrapper(list(any())) :: list(any())
  def flatten_expression_wrapper(expressions) do
    {last_func, _, result} = flatten_expression(expressions, 0, [])

    case length(result) == 0 do
      true ->
        [{0, last_func}]

      false ->
        result
    end
  end

  # ----------------------------------------------------------------------------

  def group_flattened([], _recursive_operators, _groups, _current_group) do
    []
  end

  def group_flattened([function], _recursive_operators, groups, current_group) do
    groups ++ [current_group ++ [function]]
  end

  def group_flattened([function | rest], recursive_operators, groups, current_group) do
    {_, [operator, _]} = function

    case Enum.member?(recursive_operators, operator) do
      true ->
        group_flattened(rest, recursive_operators, groups ++ [current_group ++ [function]], [])

      false ->
        group_flattened(rest, recursive_operators, groups, current_group ++ [function])
    end
  end

  def group_flattened_wrapper(flattened, recursive_operators) do
    group_flattened(flattened, recursive_operators, [], [])
  end
end
