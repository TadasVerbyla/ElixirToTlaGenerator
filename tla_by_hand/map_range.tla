---- MODULE map_range ----
EXTENDS Naturals, Sequences

CONSTANTS First, Last, Step, Fun
VARIABLES first, last, step, fun, res

Init == 
    /\ first = First
    /\ last = Last
    /\ step = Step
    /\ fun = Fun
    /\ res = <<>>

Next ==
    \/
        /\  ((step > 0 /\ first <= last) \/ (step < 0 /\ first >= last))
        /\ res' = Append(res, fun[first])
        /\ first' = first + step
        /\ last' = last
        /\ step' = step
        /\ fun' = fun
    \/
        res = nil

Spec == Init /\ [][Next]_<<first, last, step, fun, res>>

====