defmodule ElixirToAstGenerator.StringUtils.SnakeToCamel do
  def snake_to_camel(string) do
    string
    |> String.split("_", trim: true)
    |> Enum.map(&String.capitalize/1)
    |> Enum.join("")
  end
end
