---- MODULE MapRangeMC ----
EXTENDS TLC, Naturals, Sequences
CONSTANTS First, Last, Step, Max
VARIABLES first, last, step, result, finished

F == [x \in 1..Max |-> x + 1]
X == INSTANCE MapRange WITH fun <- F
Init == X!Init
Next == X!Next
Spec == Init /\ Next


FirstInvariant == 
    Head(result) = F[First]

LengthInvariant ==
    Len(result) = (Last - First) \div Step + 1

FirstValues == {First + i * Step : i \in 0..(Last - First) \div Step}
ResultInvariant ==
    \A res_index \in 1..Len(result) :
        \E val \in FirstValues : result[res_index] = F[val]

EndInvariant ==
    \/ finished = FALSE
    \/  /\ finished = TRUE
        /\ FirstInvariant
        /\ LengthInvariant
        /\ ResultInvariant
====