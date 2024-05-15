defmodule Fibonacci do
  @tlagen_function :fibonacci
  defp fib(n) when n < 2 do
    n
  end

  defp fib(n) do
    a = fib(n - 1)
    b = fib(n - 2)
    c = a + b
    c
  end
end
