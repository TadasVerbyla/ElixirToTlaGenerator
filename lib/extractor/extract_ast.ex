defmodule ElixirToAstGenerator.Extractor.ExtractAst do
  def extract_ast(file_path) do
    file_path
    |> get_ast
    |> get_body_ast
    |> get_function_ast
  end

  defp get_ast(file_path) do
    {_, ast} =
      file_path
      |> File.read!()
      |> Code.string_to_quoted()
    ast
  end

  defp get_body_ast({:defmodule, _, [_, [{:do, {:__block__, _, body_ast}}]]}) do
    body_ast
  end

  defp get_function_ast([_, {:@, _, [{:tlagen_function, _, [function_name]}]}, function_body]) do
    [function_name, function_body]
  end

end

# ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.join([__DIR__, 'elixir_files/enum_functions.ex']))
# ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.join([__DIR__, 'elixir_files/enum_functions_no_line.ex']))
# ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.join([__DIR__, 'elixir_files/enum_functions_multi_line.ex']))
# Application.put_env(:elixir, :ansi_enabled, true)