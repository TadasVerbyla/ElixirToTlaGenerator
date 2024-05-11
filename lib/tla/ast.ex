defmodule Tla.Ast do

  defmodule Constant do
    @type t() :: %__MODULE__{name: String.t()}
    defstruct name: String
  end

  defmodule Variable do
    @type t() :: %__MODULE__{name: String.t()}
    defstruct name: String
  end

  defmodule LocalVariable do
    @type t() :: %__MODULE__{name: String.t()}
    defstruct name: String
  end

  defmodule Expr do
    @type t() ::
            Constant.t()
            | Variable.t()
            | {:par, t()}
            | {:set, t()}
            | {:arr, t()}
            | {:not, t()}
            | {:and, t(), t()}
            | {:or, t(), t()}
            | {:cap, t(), t()}
            | {:concat, t(), t()}
            | {:assign, t(), t()}
            | {:=, t(), t()}
            | {:and_block, t(), t()}
            | {:or_block, t(), t()}
            | {:block, t(), t()}
            | {:always, t(), t()}
            | {:stutter, t(), t()}
            | {:next, t(), t()}
            | {:access, t(), t()}
            | {:index, t(), t()}
  end

  defmodule Operator do
    @type t() :: %__MODULE__{
            name: String.t(),
            parameters: [String.t()],
            expression: Expr.t()
          }
    defstruct name: nil, parameters: [], expression: nil
  end

  defmodule Module do
    @type t() :: %__MODULE__{
            name: String.t(),
            extends: [String.t()],
            constants: [Constant.t()],
            variables: [Variable.t()],
            operators: [Operator.t()],
            submodules: [t()]
          }
    defstruct name: nil, extends: [], constants: [], variables: [], operators: [], submodules: []
  end

  def to_tla(m = %Module{}) do
    Enum.concat([
      with_eol([
        ["---- MODULE ", m.name, " ----"]
      ]),
      with_eol([
        ["EXTENDS "] ++ m.extends
      ]),
      Enum.map(m.constants, &to_tla/1),
      Enum.map(m.variables, &to_tla/1),
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

  def to_tla(%Variable{name: name}) do
    with_eol([
      ["VARIABLE ", name]
    ])
  end

  def to_tla(%Operator{name: n, parameters: p, expression: e}) do
    pars =
      case p do
        [] -> []
        _ -> ["(", Enum.join(Enum.map(p, & &1), ", "), ")"]
      end

    with_eol([
      [n, pars, " == ", to_tla_expr(e)]
    ])
  end


  def insert_commas_wrapper(list) do
    IO.inspect(list)
    insert_commas(list, [])
  end
  defp insert_commas([string], result) do
    result ++ [string]
  end
  defp insert_commas([string | rest], result) do
    insert_commas(rest, result ++ [string] ++ [","])
  end


  defp to_tla_expr(value) when is_number(value) or is_binary(value), do: value
  defp to_tla_expr(%Constant{name: name}), do: [name]
  defp to_tla_expr(%Variable{name: name}), do: [name]
  defp to_tla_expr(%LocalVariable{name: name}), do: [name]
  defp to_tla_expr(%Operator{name: name, parameters: [], expression: nil}), do: [name]
  defp to_tla_expr(%Operator{name: name, parameters: parameters, expression: nil}), do: [name, "(", Enum.map(parameters, &to_tla_expr/1), ")"]

  defp to_tla_expr({:set, e}), do: ["<<", Enum.map(e, &to_tla_expr/1) |> insert_commas_wrapper, ">>"]
  defp to_tla_expr({:arr, e}), do: ["[", Enum.map(e, &to_tla_expr/1) |> insert_commas_wrapper, "]"]
  defp to_tla_expr({:par, e}), do: ["(", Enum.map(e, &to_tla_expr/1), ")"]
  defp to_tla_expr({:not, e}), do: ["~", to_tla_expr(e)]
  defp to_tla_expr({:next, e}), do: [to_tla_expr(e), "'"]

  defp to_tla_expr({:access, e1, e2}), do: [to_tla_expr(e1), ".", to_tla_expr(e2)]
  defp to_tla_expr({:index, e1, e2}), do: [to_tla_expr(e1), "[", to_tla_expr(e2), "]"]

  defp to_tla_expr({:always, e}), do: ["[][", to_tla_expr(e), "]"]
  defp to_tla_expr({:and, e1, e2}), do: [to_tla_expr(e1), " /\\ ", to_tla_expr(e2)]
  defp to_tla_expr({:or, e1, e2}), do: [to_tla_expr(e1), " \\/ ", to_tla_expr(e2)]
  defp to_tla_expr({:cap, e1, e2}), do: [to_tla_expr(e1), " \\cap ", to_tla_expr(e2)]
  defp to_tla_expr({:concat, e1, e2}), do: [to_tla_expr(e1), " \\o ", to_tla_expr(e2)]
  defp to_tla_expr({:assign, e1, e2}), do: [to_tla_expr(e1), " |-> ", to_tla_expr(e2)]

  defp to_tla_expr({:=, e1, e2}), do: [to_tla_expr(e1), " = ", to_tla_expr(e2)]
  defp to_tla_expr({:+, e1, e2}), do: [to_tla_expr(e1), " + ", to_tla_expr(e2)]

  defp to_tla_expr({:stutter, e1, e2}), do: [to_tla_expr(e1), "_", to_tla_expr(e2)]
  defp to_tla_expr({:and_block, e}), do: ["/\\ ", to_tla_expr(e), "\n"]
  defp to_tla_expr({:or_block, e}), do: ["\\/ ", to_tla_expr(e), "\n"]
  defp to_tla_expr({:block, e}), do: ["\n", Enum.map(e, &to_tla_expr/1) |> Enum.map(fn x -> ["\t" | x] end), "\n"]

  defp to_tla_expr({:except, e1, e2}), do: ["[", to_tla_expr(e1), " EXCEPT ", Enum.map(e2, &to_tla_expr/1) |> insert_commas_wrapper, "]"]
  defp to_tla_expr({:exception, {}, e2}), do: ["!", ".", to_tla_expr(e2)]
  defp to_tla_expr({:exception, e1, e2}), do: ["![", to_tla_expr(e1), "].", to_tla_expr(e2)]



  defp indent_lines(lines, indent), do: Enum.map(lines, &[indent, &1])
  defp with_eol(lines), do: Enum.map(lines, &[&1, "\n"])

  def example() do
    # Pavyzdinis modulis, demonstruojantis visus TLA+ AST elementus, kurie yra implementuoti.
    m = %Tla.Ast.Module{
      name: "Fib",
      extends: ["Naturals", "Integers", "TLC", "Sequences"],
      constants: [%Tla.Ast.Constant{name: "N"}],
      variables: [%Tla.Ast.Variable{name: "stack"}, %Tla.Ast.Variable{name: "return"}],
      operators: [
        %Tla.Ast.Operator{
          name: "Init",
          expression: {
            :block, [
              {:and_block,
              {:=, %Tla.Ast.LocalVariable{name: "stack"}, {
                  :set, [{:arr, [
                    {:assign, %Tla.Ast.LocalVariable{name: "n"}, %Tla.Ast.Constant{name: "N"}},
                    {:assign, %Tla.Ast.LocalVariable{name: "res_case_1"}, {:set, ["-1"]}},
                    {:assign, %Tla.Ast.LocalVariable{name: "res_case_2"}, {:set, ["-1", "-1", "-1"]}},
                    {:assign, %Tla.Ast.LocalVariable{name: "case_counter"}, "1"},
                    {:assign, %Tla.Ast.LocalVariable{name: "block_counter"}, "1"},
                  ]}]
                }
              }},
              {:and_block,
              {:=, %Tla.Ast.LocalVariable{name: "return"}, "-1"}}
            ]
          }
        },
        %Tla.Ast.Operator{
          name: "AppendToStart",
          parameters: ["item", "list"],
          expression: {:concat, {:set, [%Tla.Ast.LocalVariable{name: "item"}]}, %Tla.Ast.LocalVariable{name: "list"}}
        },
        %Tla.Ast.Operator{
          name: "Next",
          expression: {
            :block, [
              {:and_block, {:par, [
                {:or_block,
                  {:=,
                    {:access,
                      {
                        :index, %Tla.Ast.Variable{name: "stack"}, "1"}, %Tla.Ast.LocalVariable{name: "case_counter"
                      },
                    },
                    "1"
                  }
                },
                {:or_block,
                  {:=,
                    {:access,
                      {
                        :index, %Tla.Ast.Variable{name: "stack"}, "1"}, %Tla.Ast.LocalVariable{name: "block_counter"
                      },
                    },
                    "2"
                  }
                },
                {:or_block,
                  {:=,
                    {:next, %Tla.Ast.Variable{name: "stack"}},
                    %Tla.Ast.Operator{name: "SubSeq", parameters: [
                      %Tla.Ast.Variable{name: "stack"},
                      "2",
                      %Tla.Ast.Operator{name: "Len", parameters: [
                        %Tla.Ast.Variable{name: "stack"}
                      ]}
                    ]}
                  }
                },
                {:or_block,
                  {:=,
                    {:next, %Tla.Ast.Variable{name: "return"}},
                    {
                      :access,
                      {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
                      {:index, %Tla.Ast.LocalVariable{name: "res_case_1"}, "1"}
                    }
                  }
                }
              ]}},
              {:and_block, {:par, [
                {:or_block,
                  {:=,
                    {:next, %Tla.Ast.Variable{name: "stack"}},
                    {:except, %Tla.Ast.Variable{name: "stack"}, [
                      {:=,
                        {:exception, "1", %Tla.Ast.LocalVariable{name: "res_case_1"}},
                        {:access,
                          {:index, %Tla.Ast.Variable{name: "stack"}, "1"},
                          %Tla.Ast.LocalVariable{name: "n"}
                        }
                      },
                      {:=,
                        {:exception, "1", %Tla.Ast.LocalVariable{name: "block_counter"}},
                        "2"
                      }
                    ]}
                  }
              }
              ]}}
            ]
          }
        },
        %Tla.Ast.Operator{
          name: "Spec",
          expression: {
            :and,
            %Tla.Ast.Operator{name: "Init"},
            {:stutter,
              {:always, %Tla.Ast.Operator{name: "Next"}},
              {:set, [%Tla.Ast.Variable{name: "stack"}]}
            }
          }
        }
      ]
    }

    to_tla(m)
  end

end

"---- MODULE Fib ----\n
EXTENDS NaturalsIntegersTLCSequences\n
CONSTANT N\n
VARIABLE stack\n
VARIABLE return\n
Init == \n
  \t/\\ stack = <<[n |-> N,res_case_1 |-> <<-1>>,res_case_2 |-> <<-1,-1,-1>>,case_counter |-> 1,block_counter |-> 1]>>\n
  \t/\\ return = -1\n
\n\n
AppendToStart(item, list) == <<item>> \\o list\n
Next == \n
  \t/\\ (\\/ stack[1].case_counter = 1\n
\\/ stack[1].block_counter = 2\n
\\/ stack' = SubSeq(stack2Len(stack))\n
\\/ return' = stack[1].res_case_1[1]\n
\n)\n
  \t/\\ (\\/ stack' = [stack EXCEPT ![1].res_case_1 = stack[1].n,![1].block_counter = 2]\n
)\n
\n\n
Spec == Init /\\ [][Next]_<<stack>>\n
====\n"
