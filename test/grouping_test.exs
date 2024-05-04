defmodule GroupingTest do
  use ExUnit.Case
  doctest ElixirToTlaGenerator.Parser.AstParser

  test "no_recursion" do
    assert ElixirToTlaGenerator.Parser.AstParser.group_flattened_wrapper(
      [
        {0, [:-, [[:n, nil], 1]]}
      ],
      [:fib]

    ) ==  [[
            {0, [:-, [[:n, nil], 1]]}
          ]]
  end

  test "full_recursion" do
    assert ElixirToTlaGenerator.Parser.AstParser.group_flattened_wrapper(
      [
        {0, [:-, [[:n, nil], 1]]},
        {1, [:fib, [fn_nr: 0]]},
        {2, [:-, [[:n, nil], 2]]},
        {3, [:fib, [fn_nr: 2]]},
        {4, [:+, [fn_nr: 1, fn_nr: 3]]}
      ],
      [:fib]

    ) ==  [
            [{0, [:-, [[:n, nil], 1]]}, {1, [:fib, [fn_nr: 0]]}],
            [{2, [:-, [[:n, nil], 2]]}, {3, [:fib, [fn_nr: 2]]}],
            [{4, [:+, [fn_nr: 1, fn_nr: 3]]}]
          ]
  end

end
