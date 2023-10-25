defmodule ElixirToAstGenerator.Parser.ParseEnum do
  def parse_map(input_name) do
    constant = input_name |> ElixirToAstGenerator.StringUtils.SnakeToCamel.snake_to_camel
    #output_name = ["output-", UUID.uuid4]
    output_name = "output"
    [title: "EnumMap",
    extends: ["Integers", "Sequences"],
    constants: [constant],
    variables: [input_name, output_name],
    type_ok: [],
    init: [ "/\\ #{input_name} = #{constant}",
            "/\\ #{output_name} = <<>>"],
    next: [ "/\\ #{input_name} # <<>>",
            "/\\ #{[output_name, "'"]} = Append(#{output_name}, Head(#{input_name}) * 2)",
            "/\\ #{input_name}' = Tail(#{input_name})"],
    stutter: "<<#{input_name}, #{output_name}>>"]
  end
end
