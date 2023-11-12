defmodule ElixirToTlaGenerator.Extractor.ExtractAst do
  def extract_ast(file_path) do
    [function_name, function_ast] = file_path
    |> get_ast
    |> get_module_ast
    |> get_functions_ast
    [function_name, function_ast |> translate_functions_ast]
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

  defp translate_functions_ast([]) do
    []
  end

  defp translate_functions_ast([{:defp, _, [conditions_block, [do: do_block]]} | rest]) do
    header_tla = process_header(conditions_block)
    do_tla = process_do_block(do_block)
    [[header_tla, do_tla] | translate_functions_ast(rest)]
  end

  defp process_header({:when, _, [{_function_name, _, parameter_block}, {:when, _, conditional_block}]}) do
    parameters = process_parameters(parameter_block)
    conditions = process_conditions(conditional_block)
    [parameters, conditions]
  end

  defp process_header({_function_name, _, parameter_block}) do
    parameters = process_parameters(parameter_block)
    parameters
  end

  defp process_parameters([{parameter, _, initial_value} | []]) do
    [[parameter, initial_value]]
  end

  defp process_parameters([{parameter, _, initial_value} | rest]) do
    [[parameter, initial_value] | process_parameters(rest)]
  end

  defp process_conditions([{:and, _, and_ast} | []]) do
    and_conditions = process_and(and_ast)
    [and_conditions]
  end

  defp process_conditions([{:and, _, and_ast} | rest]) do
    and_conditions = process_and(and_ast)
    [and_conditions | process_conditions(rest)]
  end

  defp process_and([{operator, _, [var1, var2]} | []]) do
    val1 = simplify_var(var1)
    val2 = simplify_var(var2)
    [[operator, val1, val2]]
  end

  defp process_and([{operator, _, [var1, var2]} | rest]) do
    val1 = simplify_var(var1)
    val2 = simplify_var(var2)
    [[operator, val1, val2] | process_and(rest)]
  end

  defp simplify_var({name, _, value}) do
    [name, value]
  end

  defp simplify_var(var) do
    var
  end

  defp process_do_block([]) do
    []
  end

  defp process_do_block([expression_ast | []]) do
    expression = process_expression(expression_ast)
    expression
  end

  defp process_do_block([expression_ast | rest]) do
    expression = process_expression(expression_ast)
    [expression | rest]
  end


  def process_expression({operator_ast, _, subexpressions_ast}) do
    operator = process_expression(operator_ast)
    subexpressions = process_expression(subexpressions_ast)
    [[operator, subexpressions]]
  end

  def process_expression([{opperator_ast, _, subexpressions_ast} | rest]) do
    operator = process_expression(opperator_ast)
    subexpressions = process_expression(subexpressions_ast)
    [[operator, subexpressions] | process_expression(rest)]
  end



  def process_expression([expression_ast | []]) do
    expression = process_expression(expression_ast)
    [expression]
  end

  def process_expression([expression_ast | rest]) do
    expression = process_expression(expression_ast)
    [expression, process_expression(rest)]
  end

  def process_expression(atom) do
    atom
  end




end
# ElixirToAstGenerator.Extractor.ExtractAst.process_expression([{{:., [line: 6], [{:fun, [line: 6], nil}]}, [line: 6],[{:first, [line: 6], nil}]},{:map_range, [line: 6],[{:+, [line: 6], [{:first, [line: 6], nil}, {:step, [line: 6], nil}]},{:last, [line: 6], nil},{:step, [line: 6], nil},{:fun, [line: 6], nil}]}])
# ElixirToAstGenerator.Extractor.ExtractAst.process_expression({:|, [line: 6],[{{:., [line: 6], [{:fun, [line: 6], nil}]}, [line: 6],[{:first, [line: 6], nil}]},{:map_range, [line: 6],[{:+, [line: 6], [{:first, [line: 6], nil}, {:step, [line: 6], nil}]},{:last, [line: 6], nil},{:step, [line: 6], nil},{:fun, [line: 6], nil}]}]})
# ElixirToAstGenerator.Extractor.ExtractAst.process_expression([{:first, [line: 6], nil}])
# ElixirToAstGenerator.Extractor.ExtractAst.process_expression({{:., [line: 6], [{:fun, [line: 6], nil}]}, [line: 6], [{:first, [line: 6], nil}]})
# ElixirToAstGenerator.Extractor.ExtractAst.process_expression({:map_range, [line: 6],[{:+, [line: 6], [{:first, [line: 6], nil}, {:step, [line: 6], nil}]},{:last, [line: 6], nil},{:step, [line: 6], nil},{:fun, [line: 6], nil}]})
# ElixirToAstGenerator.Extractor.ExtractAst.process_expression([{:+, [line: 6], [{:first, [line: 6], nil}, {:step, [line: 6], nil}]},{:last, [line: 6], nil},{:step, [line: 6], nil},{:fun, [line: 6], nil}])


# ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.join([__DIR__, 'elixir_files/enum_functions.ex']))
# ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.join([__DIR__, 'elixir_files/enum_functions_no_line.ex']))
# ElixirToAstGenerator.Extractor.ExtractAst.extract_ast(Path.join([__DIR__, 'elixir_files/enum_functions_multi_line.ex']))

# Application.put_env(:elixir, :ansi_enabled, true)
