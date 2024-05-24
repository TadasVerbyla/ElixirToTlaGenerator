defmodule ElixirToTlaGenerator do
  def generate(directory) do
    ElixirToTlaGenerator.Extractor.ExtractAst.extract_ast(directory)
    |> ElixirToTlaGenerator.Parser.AstParser.parse_ast()
    |> ElixirToTlaGenerator.Parser.TlaAstMaker.make_ast()
  end
end
