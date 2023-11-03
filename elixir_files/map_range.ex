defmodule MapRange do
  @tlagen_function :map_range
  defp map_range(first, last, step, fun)
       when step > 0 and first <= last
       when step < 0 and first >= last do
    [fun.(first) | map_range(first + step, last, step, fun)]
  end

  defp map_range(_first, _last, _step, _fun) do
    []
  end
end
