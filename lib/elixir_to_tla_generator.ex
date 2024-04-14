defmodule ElixirToTlaGenerator do
  def generate(directory) do
    ElixirToTlaGenerator.Extractor.ExtractAst.extract_ast(directory) |>
    ElixirToTlaGenerator.Parser.AstParser.parse_ast #|>
    #ElixirToTlaGenerator.Parser.TlaMaker.make_tla_file
  end
end

# ElixirToTlaGenerator.generate("C:\\Users\\tadas\\Documents\\GitHub\\ElixirToTlaGenerator\\elixir_files\\fibonacci.ex")
# ElixirToTlaGenerator.generate("C:\\Users\\tadas\\Documents\\GitHub\\ElixirToTlaGenerator\\elixir_files\\map_range.ex")
