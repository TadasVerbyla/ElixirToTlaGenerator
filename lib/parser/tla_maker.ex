defmodule ElixirToTlaGenerator.Parser.TlaMaker do
  def make_tla_file([function_name, extensions, fun_variables, basic_variables, conditions, recursion]) do
    title = ElixirToAstGenerator.StringUtils.SnakeToCamel.snake_to_camel(function_name)
    filename = Path.relative_to('generated_tla/#{title}.tla', Path.dirname(__DIR__))
    constants = Enum.map(basic_variables, &ElixirToAstGenerator.StringUtils.SnakeToCamel.snake_to_camel/1)
    init = make_init(basic_variables, constants)
    [result, recursion_body] = recursion
    recursion_body = Enum.reject(recursion_body, fn string ->
      String.starts_with?(string, "fun")
    end)
    next = make_next(conditions, [result, recursion_body], basic_variables)
    finished = make_finished(conditions, basic_variables)
    stutter = Enum.join(basic_variables ++ ["result", "finished"], ", ")
    tla_text = [
      "---- MODULE #{title} ----\n",
      concat_to_label("EXTENDS ", extensions),
      concat_to_label("CONSTANTS ", constants ++ fun_variables),
      concat_to_label("VARIABLES ", basic_variables ++ ["result", "finished"]),
      concat_to_definition("Init ==\n\t", init),
      concat_to_definition2("Next ==\n\t\\/\n\t\t", next),
      concat_to_definition2("\t\\/\n\t\t", finished),
      "Spec == Init /\\ [][Next]_<<#{stutter}>>",
      "\n\n===="
    ]
    IO.puts(tla_text)
    File.write(filename, tla_text)
  end

  defp make_init([var | []], [const | []]) do
    ["/\\ #{var} = #{const}" | ["/\\ result = <<>>", "/\\ finished = FALSE"]]
  end

  defp make_init([h_var | t_var], [h_const | t_const]) do
    ["/\\ #{h_var} = #{h_const}" | make_init(t_var, t_const)]
  end

  defp make_next(conditions, [result, recursion], variables) do
    ["/\\ ((#{Enum.join(make_and(conditions), ") \\/ (")}))", "/\\ #{result}", "/\\ finished' = finished" | make_recursion(recursion, variables)]
  end

  defp make_finished(conditions, variables) do
    ["/\\ (~(#{Enum.join(make_and(conditions), ") \\/ (")}))", "/\\ result' = result" , "/\\ finished' = TRUE" | make_finished_variables(variables)]
  end

  defp make_finished_variables([var | []]) do
    ["/\\ #{var}' = #{var}"]
  end
  defp make_finished_variables([var | rest]) do
    ["/\\ #{var}' = #{var}" | make_finished_variables(rest)]
  end

  defp make_and([and_block | []]) do
    [Enum.join(and_block, " /\\ ")]
  end
  defp make_and([and_block | rest]) do
    condition = Enum.join(and_block, " /\\ ")
    [condition | make_and(rest)]
  end

  defp make_recursion([rec | []], [var | []]) do
    ["/\\ #{var}' = #{rec}"]
  end
  defp make_recursion([h_rec | t_rec], [h_var | t_var]) do
    ["/\\ #{h_var}' = #{h_rec}" | make_recursion(t_rec, t_var)]
  end

  def concat_to_label(label, []), do: label <> "\n"
  def concat_to_label(label, [head | []]), do: concat_to_label(label <> head, [])
  def concat_to_label(label, [head | rest]), do: concat_to_label(label <> head <> ", ", rest)

  def concat_to_definition(definition, []), do: definition <> "\n"
  def concat_to_definition(definition, [head | rest]), do: concat_to_definition(definition <> head <> "\n\t",  rest)

  def concat_to_definition2(definition, []), do: definition <> "\n"
  def concat_to_definition2(definition, [head | rest]), do: concat_to_definition2(definition <> head <> "\n\t\t",  rest)

end
