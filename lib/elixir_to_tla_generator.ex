defmodule ElixirToTlaGenerator do
  def generate(directory) do
    ElixirToTlaGenerator.Extractor.ExtractAst.extract_ast(directory) |>
    ElixirToTlaGenerator.Parser.SimplifiedAstToTla.parse_simplified_tla |>
    ElixirToTlaGenerator.Parser.TlaMaker.make_tla_file
  end
end
