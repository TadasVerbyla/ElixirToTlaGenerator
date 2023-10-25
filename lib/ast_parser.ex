defmodule ElixirToAstGenerator do
  def generate do
    [_function_name, ast] = ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.relative_to('elixir_files/enum_functions.ex', Path.dirname(__DIR__)))
    {:def, _, [{_function_name, _, variables_ast}, do_ast]} = ast
    [variables_ast, do_ast]
  end
end

#[
#  :enum_map,
#  {:def, [line: 4],
#   [
#     {:enum_map, [line: 4], [{:l1, [line: 4], nil}, {:func, [line: 4], nil}]},
#     [
#       do: {{:., [line: 5], [{:__aliases__, [line: 5], [:Enum]}, :map]},
#        [line: 5], [{:l1, [line: 5], nil}, {:func, [line: 5], nil}]}
#     ]
#   ]}
#]
