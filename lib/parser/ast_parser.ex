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




  def flatten_expresion([operator, parameters]) do

  end
end
