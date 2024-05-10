defmodule ElixirToTlaGenerator.Extractor.ExtractAst do
  def extract_ast(file_path) do
    [function_name, function_ast] = file_path
    |> get_ast
    |> get_module_ast
    |> get_functions_ast
    [function_name, function_ast]
  end

  defp get_ast(file_path) do
    {_, ast} =
      file_path
      |> File.read!()
      |> Code.string_to_quoted()
    ast
  end

  defp get_module_ast({:defmodule, _, [_, [{:do, {:__block__, _, body_ast}}]]}) do
    body_ast
  end

  defp get_functions_ast([{:@, _, [{:tlagen_function, _, [function_name]}]} | functions]) do
    [function_name, functions]
  end
end
