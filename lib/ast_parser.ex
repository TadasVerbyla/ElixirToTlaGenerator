defmodule ElixirToAstGenerator do
  def generate do
    get_function_info() |> parse_function() |> write_tla()

  end

  def write_tla([title: ttl, extends: ex, constants: con, variables: var, type_ok: _t_o, init: ini, next: nxt, stutter: stt]) do
    filename = Path.relative_to('generated_tla/#{ttl}.tla', Path.dirname(__DIR__))
    tla_text = [
      "---- MODULE #{ttl} ----\n",
      concat_to_label("EXTENDS ", ex),
      concat_to_label("CONSTANTS ", con),
      concat_to_label("VARIABLES ", var),
      #type_ok = concat_to_definition("TypeOk ==", t_o),
      concat_to_definition("Init ==\n\t", ini),
      concat_to_definition("Next ==\n\t", nxt),
      "Spec == Init /\\ [][Next]_#{stt}",
      "\n\n===="
    ]
    IO.puts(tla_text)
    File.write(filename, tla_text)
  end

  def concat_to_label(label, []), do: label <> "\n"
  def concat_to_label(label, [head | []]), do: concat_to_label(label <> head, [])
  def concat_to_label(label, [head | rest]), do: concat_to_label(label <> head <> ", ", rest)

  def concat_to_definition(definition, []), do: definition <> "\n"
  def concat_to_definition(definition, [head | rest]), do: concat_to_definition(definition <> head <> "\n\t",  rest)


  def parse_function([:Enum, :map, [{var_name, _, nil}, {_func_name, _, nil}]]) do
    ElixirToAstGenerator.Parser.ParseEnum.parse_map(var_name |> Atom.to_string)
  end

  def parse_function([_, _, _]) do
    IO.puts("Not Implemented")
  end

  def get_function_info do
    [_function_name, ast] = ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.relative_to('elixir_files/enum_functions.ex', Path.dirname(__DIR__)))
    {:def, _, [{_function_name, _, _global_variables_ast}, do_ast]} = ast
    [do: {{:., _, [{:__aliases__, _, [library]}, function]}, _, variable_ast}] = do_ast
    [library, function, variable_ast]
  end
end
