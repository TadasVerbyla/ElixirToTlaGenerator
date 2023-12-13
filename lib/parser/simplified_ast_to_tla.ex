defmodule ElixirToTlaGenerator.Parser.SimplifiedAstToTla do
  def parse_simplified_tla(simple_ast) do
    [function_name, [function | _rest]] = simple_ast
    [[variables, conditions], body] = function
    tla_extensions = find_extensions(simple_ast)
    tla_from_name = Atom.to_string(function_name)
    tla_from_variables = parse_variables(variables)
    tla_from_conditions = parse_conditions(conditions)
    tla_from_body = parse_body(body, function_name)
    [tla_from_name, tla_extensions, tla_from_variables, tla_from_conditions, tla_from_body]
  end

  defp find_extensions(ast) do
    atoms = extract_atoms(ast)
    [check_integers(atoms), check_sequences(atoms)]


  end

  defp check_sequences(atoms) do
    if  Enum.member?(atoms, :|)
    do
      "Sequences"
    end
  end

  defp check_integers(atoms) do
    if  Enum.member?(atoms, :>) or
        Enum.member?(atoms, :<) or
        Enum.member?(atoms, :>=) or
        Enum.member?(atoms, :<=) or
        Enum.member?(atoms, :+) or
        Enum.member?(atoms, :-) or
        Enum.member?(atoms, :*)
    do
      "Naturals"
    end
  end

  def extract_atoms(data) when is_atom(data) and data != nil do
    [data]
  end

  def extract_atoms(data) when is_list(data) do
    Enum.flat_map(data, &extract_atoms/1)
  end

  def extract_atoms(_), do: []



  defp parse_variables([[variable, nil] | []]) do
    [Atom.to_string(variable)]
  end

  defp parse_variables([[variable, nil] | rest]) do
    [Atom.to_string(variable) | parse_variables(rest)]
  end

  defp parse_conditions([when_block | []]) do
    string_when = parse_when(when_block)
    [string_when]
  end

  defp parse_conditions([when_block | rest]) do
    string_when = parse_when(when_block)
    [string_when | parse_conditions(rest)]
  end

  defp parse_when([[opperator, val1, val2] | []]) do
    string_val1 = val_to_string(val1)
    string_val2 = val_to_string(val2)
    ["#{string_val1} #{Atom.to_string(opperator)} #{string_val2}"]
  end

  defp parse_when([[opperator, val1, val2] | rest]) do
    string_val1 = val_to_string(val1)
    string_val2 = val_to_string(val2)
    ["#{string_val1} #{Atom.to_string(opperator)} #{string_val2}" | parse_when(rest)]
  end

  defp val_to_string([atom, nil]) do
    Atom.to_string(atom)
  end

  defp val_to_string(val) do
    Integer.to_string(val)
  end


  defp parse_body([[:|, [head, tail]]], function_name) do
    head_string = expression_to_string(head)
    tail_string = parse_body(tail, function_name)
    ["result' = Append(result, #{head_string})", tail_string]
  end

  defp parse_body([function_name, [head | tail]], function_name) do
    head_string = expression_to_string(head)
    [head_string | parse_body(tail)]
  end

  defp parse_body([[element, nil] | []]) do
    [Atom.to_string(element)]
  end

  defp parse_body([[element, nil] | rest]) do
    [Atom.to_string(element) | parse_body(rest)]
  end


  defp expression_to_string([[[:., [[function_name, nil]]]], [[var, nil]]]) do
    "#{Atom.to_string(function_name)}[#{Atom.to_string(var)}]"
  end

  defp expression_to_string([expression, [[var1, nil], [var2, nil]]]) do
    "#{Atom.to_string(var1)}#{Atom.to_string(expression)}#{Atom.to_string(var2)}"
  end

end
