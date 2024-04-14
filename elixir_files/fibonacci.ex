defmodule Fibonacci do
  @tlagen_function :fibonacci
  defp fib(n) when n < 2 do
    n
  end

  defp fib(n) do
    fib(n - 1) + fib(n - 2)
  end
end
