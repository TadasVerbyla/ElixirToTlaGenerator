defmodule ElixirToAstGenerator.Parser.ParseEnum do
  def parse_map(input_name) do
    constant = input_name |> ElixirToAstGenerator.StringUtils.SnakeToCamel.snake_to_camel
    [constants: [constant],
    type_ok: [],
    init: [ "/\\ #{input_name} = #{constant}",
            "/\\ output = <<>>"],
    next: [ "/\\ #{input_name} # <<>>",
            "/\\ output' = Append(output, Head(#{input_name}) * 2)",
            "/\\ #{input_name}' = Tail(#{input_name})]]"]]
  end
end
