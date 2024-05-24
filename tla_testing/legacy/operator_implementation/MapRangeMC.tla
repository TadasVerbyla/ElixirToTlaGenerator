---- MODULE MapRangeMC ----
EXTENDS TLC, Naturals, Sequences
CONSTANTS First, Last, Step, Max
VARIABLES first, last, step, result, finished

my_f(i) == i + 1
X == INSTANCE MapRange WITH fun <- my_f
Init == X!Init
Next == X!Next
Spec == Init /\ Next

value_by_index(i) == First + Step * (i - 1)
OrderInvariant ==
    \A res_index \in 1..Len(result): result[res_index] = my_f(value_by_index(res_index))
        
FirstValues == {First + i * Step : i \in 0..(Last - First) \div Step}
ResultInvariant ==
    \A val \in FirstValues :
        \E res_index \in 1..Len(result) : result[res_index] = my_f(val)

EndInvariant ==
    \/ finished = FALSE
    \/  /\ finished = TRUE
        /\ ResultInvariant
        /\ OrderInvariant
====