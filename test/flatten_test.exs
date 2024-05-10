defmodule FlattenTest do
  use ExUnit.Case
  doctest ElixirToTlaGenerator.Parser.AstParserUnsimplified

  test "flatten_constant_integer" do
    assert ElixirToTlaGenerator.Parser.AstParserUnsimplified.flatten_expression_wrapper(
      (quote do: 1)
    ) == [{0, 1}]
  end

  test "flatten_constant_string" do
    assert ElixirToTlaGenerator.Parser.AstParserUnsimplified.flatten_expression_wrapper(
      (quote do: "string")
    ) == [{0, "string"}]
  end

  test "flatten_variable" do
    assert ElixirToTlaGenerator.Parser.AstParserUnsimplified.flatten_expression_wrapper(
      (quote do: n)
    ) == [{0, {:n, [], FlattenTest}}]
  end

  test "flatten_single_expression" do
    assert ElixirToTlaGenerator.Parser.AstParserUnsimplified.flatten_expression(
      (quote do: n - 1),
      0,
      []
    ) == {{:fn_nr, 0}, 1, [
                            {0, [:-, [{:n, [], FlattenTest}, 1]]}
                          ]}
    # Example of how return value for function is handled internally
    # First element is the last processed function id tag
  end

  test "flatten_double_expression" do
    assert ElixirToTlaGenerator.Parser.AstParserUnsimplified.flatten_expression_wrapper(
      (quote do: fib(n - 1))
    ) ==  [
            {0, [:-, [{:n, [], FlattenTest}, 1]]},
            {1, [:fib, [fn_nr: 0]]}
          ]
    # v0 = n - 1
    # v1 = fib [v0]
  end

  test "flatten_full" do
    assert ElixirToTlaGenerator.Parser.AstParserUnsimplified.flatten_expression_wrapper(
      (quote do: fib(n - 1) + fib(n - 2))
    ) ==  [
            {0, [:-, [{:n, [], FlattenTest}, 1]]},
            {1, [:fib, [fn_nr: 0]]},
            {2, [:-, [{:n, [], FlattenTest}, 2]]},
            {3, [:fib, [fn_nr: 2]]},
            {4, [:+, [fn_nr: 1, fn_nr: 3]]}
          ]
    # v1 = n - 1
    # v2 = fib(v1)
    # v3 = n - 2
    # v4 = fib(v3)
    # v5 = v2 + v4
  end
end
