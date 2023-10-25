defmodule EnumFunctions2 do
  @spec enum_map(list(), function()) :: list()
  @tlagen_function :enum_map
  def enum_map(l1, func) do
    result1 = Enum.map(l1, func)
    result2 = Enum.map(result1, func)
    result3 = Enum.map(result2, func)
    result4 = result1 + result2 * result3
  end
end
