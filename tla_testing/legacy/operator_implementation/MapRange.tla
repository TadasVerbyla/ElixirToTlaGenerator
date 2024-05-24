---- MODULE MapRange ----
EXTENDS Naturals, Sequences
CONSTANTS First, Last, Step, fun(_)
VARIABLES first, last, step, result, finished
Init ==
	/\ first = First
	/\ last = Last
	/\ step = Step
	/\ result = <<>>
	/\ finished = FALSE
	
Next ==
	\/
		/\ ((step > 0 /\ first <= last) \/ (step < 0 /\ first >= last))
		/\ result' = Append(result, fun(first))
		/\ finished' = finished
		/\ first' = first+step
		/\ last' = last
		/\ step' = step
		
	\/
		/\ (~(step > 0 /\ first <= last) \/ (step < 0 /\ first >= last))
		/\ result' = result
		/\ finished' = TRUE
		/\ first' = first
		/\ last' = last
		/\ step' = step
		
Spec == Init /\ [][Next]_<<first, last, step, result, finished>>

====