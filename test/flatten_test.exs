defmodule FlattenTest do
  use ExUnit.Case
  doctest ElixirToTlaGenerator.Parser.AstParser



  test "flatten_constant_integer" do
    assert ElixirToTlaGenerator.Parser.AstParser.flatten_expression_wrapper(
      # 1
      (quote do: 1)
    ) == [{0, 1}]
  end

  test "flatten_constant_string" do
    assert ElixirToTlaGenerator.Parser.AstParser.flatten_expression_wrapper(
      # string
      (quote do: "string")
    ) == [{0, "string"}]
  end

  test "flatten_variable" do
    assert ElixirToTlaGenerator.Parser.AstParser.flatten_expression_wrapper(
      # n
      [:n, nil]
    ) == [{0, [:n, nil]}]
  end

  test "flatten_single_expression" do
    assert ElixirToTlaGenerator.Parser.AstParser.flatten_expression(
      # n - 1
      [:-, [[:n, nil], 1]],
      0,
      []
    ) == {{:fn_nr, 0}, 1, [
                            {0, [:-, [[:n, nil], 1]]}
                          ]}
    # Example of how return value for function is handled internally
    # First element is the last processed function id tag
  end

  test "flatten_double_expression" do
    assert ElixirToTlaGenerator.Parser.AstParser.flatten_expression_wrapper(
      # fib(n - 1)
      [:fib, [[:-, [[:n, nil], 1]]]]
    ) ==  [
            {0, [:-, [[:n, nil], 1]]},
            {1, [:fib, [{:fn_nr, 0}]]}
          ]
    # v0 = n - 1
    # v1 = fib [v0]
  end

  test "flatten_full" do
    assert ElixirToTlaGenerator.Parser.AstParser.flatten_expression_wrapper(
      # fib(n - 1) + fib(n - 2)
      [:+, [[:fib, [[:-, [[:n, nil], 1]]]], [:fib, [[:-, [[:n, nil], 2]]]]]]
    ) ==  [
            {0, [:-, [[:n, nil], 1]]},
            {1, [:fib, [{:fn_nr, 0}]]},
            {2, [:-, [[:n, nil], 2]]},
            {3, [:fib, [{:fn_nr, 2}]]},
            {4, [:+, [{:fn_nr, 1}, {:fn_nr, 3}]]}
          ]
    # v1 = n - 1
    # v2 = fib(v1)
    # v3 = n - 2
    # v4 = fib(v3)
    # v5 = v2 + v4
  end
end
