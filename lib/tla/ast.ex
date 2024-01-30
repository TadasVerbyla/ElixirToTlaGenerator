defmodule Tla.Ast do
  defmodule Constant do
    @type t() :: %__MODULE__{name: String.t()}
    defstruct name: String
  end

  defmodule Operator do
    @type t() :: %__MODULE__{
            name: String.t(),
            parameters: [String.t()],
            expression: Expr.t()
          }
    defstruct name: nil, parameters: [], expression: nil
  end

  defmodule Expr do
    @type t() ::
            Constant.t()
            | {:par, t()}
            | {:and, t(), t()}
            | {:or, t(), t()}
            | {:cap, t(), t()}
  end

  defmodule Module do
    @type t() :: %__MODULE__{
            name: String.t(),
            constants: [Constant.t()],
            operators: [Operator.t()],
            submodules: [t()]
          }
    defstruct name: nil, constants: [], operators: [], submodules: []
  end

  def to_tla(m = %Module{}) do
    Enum.concat([
      with_eol([
        ["---- MODULE ", m.name, " ----"]
      ]),
      Enum.map(m.constants, &to_tla/1),
      Enum.map(m.operators, &to_tla/1),
      Enum.map(m.submodules, &indent_lines(to_tla(&1), "  ")),
      with_eol([
        ["===="]
      ])
    ])
  end

  def to_tla(%Constant{name: name}) do
    with_eol([
      ["CONSTANT ", name]
    ])
  end

  def to_tla(%Operator{name: n, parameters: p, expression: e}) do
    pars =
      case p do
        [] -> []
        _ -> ["(", Enum.join(Enum.map(p, & &1.name), ", "), ")"]
      end

    with_eol([
      [n, pars, " == ", to_tla_expr(e)]
    ])
  end

  defp to_tla_expr(%Constant{name: name}), do: [name]
  defp to_tla_expr({:par, e}), do: ["(", to_tla_expr(e), ")"]
  defp to_tla_expr({:and, e1, e2}), do: [to_tla_expr(e1), " /\\ ", to_tla_expr(e2)]
  defp to_tla_expr({:or, e1, e2}), do: [to_tla_expr(e1), " \\/ ", to_tla_expr(e2)]
  defp to_tla_expr({:cap, e1, e2}), do: [to_tla_expr(e1), " \\cap ", to_tla_expr(e2)]

  defp indent_lines(lines, indent), do: Enum.map(lines, &[indent, &1])
  defp with_eol(lines), do: Enum.map(lines, &[&1, "\n"])

  defmodule Example do
    use ExUnit.Case

    test "example" do
      # The transformation from the Elixir will build a data structure like this:
      m = %Module{
        name: "Ex1",
        constants: [%Constant{name: "Nodes"}, %Constant{name: "Values"}],
        operators: [
          %Operator{
            name: "Op",
            expression: {:cap, %Constant{name: "Nodes"}, %Constant{name: "Values"}}
          }
        ],
        submodules: [%Module{name: "Sub1"}, %Module{name: "Sub2"}]
      }

      # Then we will write out the TLA+ file using the to_tla function.
      """
      ---- MODULE Ex1 ----
      CONSTANT Nodes
      CONSTANT Values
      Op == Nodes \\cap Values
        ---- MODULE Sub1 ----
        ====
        ---- MODULE Sub2 ----
        ====
      ====
      """ = IO.chardata_to_string(Tla.Ast.to_tla(m))
    end
  end
end
