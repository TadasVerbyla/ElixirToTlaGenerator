---- MODULE MapRangeMC ----
EXTENDS TLC, Naturals, Sequences
CONSTANTS First, Last, Step, Max
VARIABLES first, last, step, result, finished

F == [x \in 1..Max |-> x + 1]
X == INSTANCE MapRange WITH fun <- F
Init == X!Init
Next == X!Next
Spec == Init /\ Next

value_by_index(i) == First + Step * (i - 1)
OrderInvariant ==
    \A res_index \in 1..Len(result): result[res_index] = F[value_by_index(res_index)]

FirstValues == {First + i * Step : i \in 0..(Last - First) \div Step}
ResultInvariant ==
    \A res_index \in 1..Len(result) :
        \E val \in FirstValues : result[res_index] = F[val]

EndInvariant ==
    \/ finished = FALSE
    \/  /\ finished = TRUE
        /\ ResultInvariant
        /\ OrderInvariant
====