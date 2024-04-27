defmodule ElixirToTlaGenerator.Parser.AstParser do

  def parse_ast(simplified_ast) do
    [_tlagen_name, clauses] = simplified_ast

    headers = get_headers(clauses)
    all_parameters = get_all_parameters(headers)
    guards = get_all_guards(headers)
    clause_names = get_all_clause_names(headers)
    unique_paramteres = Enum.uniq(all_parameters)
    full_guards = add_guard_negation(guards)
    unique_clause_names = Enum.uniq(clause_names)

    expresions = get_expresions(clauses)
    expresions
  end

  def get_headers([[header, _body] | []]) do
    header
  end

  def get_headers([[header, _body] | rest]) do
    [header | get_headers(rest)]
  end


  def get_all_parameters([_name, [parameters, _guards]]) do
    [parameters]
  end

  def get_all_parameters([_name, parameters]) do
    [parameters]
  end

  def get_all_parameters([[_name, [parameters, _guards]] | rest]) do
    [parameters | get_all_parameters(rest)]
  end

  def get_all_parameters([[_name, parameters] | rest]) do
    [parameters | get_all_parameters(rest)]
  end


  def get_all_guards([_name, [_parameters, guards]]) do
    [guards]
  end

  def get_all_guards([_name, _parameters]) do
    [[]]
  end

  def get_all_guards([[_name, [_parameters, guards]] | rest]) do
    [guards | get_all_guards(rest)]
  end

  def get_all_guards([[_name, _parameters] | rest]) do
    [[] | get_all_guards(rest)]
  end


  def get_all_clause_names([name, _body]) do
    [name]
  end

  def get_all_clause_names([[name, _body] | rest]) do
    [name | get_all_clause_names(rest)]
  end


  def add_guard_negation(guards) do
    Enum.map(guards, fn(guard) ->
      [guard | Enum.filter(guards, &(&1 != guard))]
    end)
  end


  def get_expresions([[_header, body] | []]) do
    [body]
  end

  def get_expresions([[_header, body] | rest]) do
    [body | get_expresions(rest)]
  end


  @spec flatten_expression(number() | binary(), number(), list(any())) :: {number() | atom() | binary(), number(), list(any())}
  def flatten_expression(constant, fn_counter, functions) when is_number(constant) or is_binary(constant) do
    {constant, fn_counter, functions}
  end

  @spec flatten_expression({atom(), any()}, number(), list(any())) :: {list(atom()), number(), list(any())}
  def flatten_expression([atom, nil], fn_counter, functions) do
    {[atom, nil], fn_counter, functions}
  end

  @spec flatten_expression({atom(), list(any())}, number(), list(any())) :: {list(any()), number(), list(any())}
  def flatten_expression([atom, parameters], fn_counter, functions) do

    f = fn(parameter, {acc_parameters, acc_counter, acc_functions}) ->
      {flattened_parameter, new_fn_counter, new_functions} = flatten_expression(parameter, acc_counter, acc_functions)
      {[flattened_parameter] ++ acc_parameters, new_fn_counter, new_functions}
    end

    {new_parameters, new_counter, new_functions} = Enum.reduce(
      parameters,
      {[], fn_counter, functions},
      f)

    function_parameters = Enum.reverse(new_parameters)
    function = {new_counter, [atom, function_parameters]}
    function_id = {:fn_nr, new_counter}

    {function_id, new_counter + 1, new_functions ++ [function]}
  end

  @spec flatten_expression_wrapper(list(any()), number(), list(any())) :: list(any())
  def flatten_expression_wrapper(ast, fn_counter, functions) do
    {_, _, result} = flatten_expression(ast, fn_counter, functions)
    result
  end
end
