defmodule ElixirToTlaGenerator do
  def generate(directory) do
    ElixirToTlaGenerator.Extractor.ExtractAst.extract_ast(directory) |>
    ElixirToTlaGenerator.Parser.SimplifiedAstToTla.parse_simplified_tla |>
    ElixirToTlaGenerator.Parser.TlaMaker.make_tla_file
  end
end

# ElixirToTlaGenerator.generate('c:/Users/tadas/Desktop/ElixirToTlaGenerator/elixir_files/map_range.ex')
