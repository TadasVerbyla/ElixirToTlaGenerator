defmodule EnumFunctions3 do
  @spec enum_map(list(), function()) :: list()
  @tlagen_function :enum_map
  def enum_map(l1, func), do: Enum.map(l1, func)
end
