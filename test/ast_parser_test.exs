defmodule AstParserTest do
  use ExUnit.Case
  doctest AstParser

  test "greets the world" do
    assert AstParser.hello() == :world
  end
end
