---- MODULE MapRange ----
EXTENDS Naturals, Sequences
CONSTANTS First, Last, Step, fun
VARIABLES first, last, step, result, finished
ASSUME Step # 0



Init ==
	/\ first = First
	/\ last = Last
	/\ step = Step
	/\ result = <<>>
    /\ finished = FALSE
	
Next ==
    \/
        /\ ((step > 0 /\ first <= last) \/ (step < 0 /\ first >= last))
        /\ result' = Append(result, fun[first])
        /\ first' = first + step
        /\ last' = last
        /\ step' = step
        /\ finished' = finished
    \/
        /\ ((step > 0 /\ first > last) \/ (step < 0 /\ first < last))
        /\ result' = result
        /\ first' = first
        /\ last' = last
        /\ step' = step
        /\ finished' = TRUE

Spec == Init /\ [][Next]_<<first, last, step, finished>>

====