defmodule ElixirToTlaGenerator do
  def generate do
    ElixirToTlaGenerator.Extractor.ExtractAst.extract_ast('c:/Users/tadas/Desktop/ElixirToTlaGenerator/elixir_files/map_range.ex') |>
    ElixirToTlaGenerator.Parser.SimplifiedAstToTla.parse_simplified_tla |>
    ElixirToTlaGenerator.Parser.TlaMaker.make_tla_file
  end
end
