---- MODULE MapRange ----
EXTENDS Naturals, Sequences
CONSTANTS First, Last, Step, Fun
VARIABLES first, last, step, fun, result, finished
Init ==
	/\ first = First
	/\ last = Last
	/\ step = Step
	/\ fun = Fun
	/\ result = <<>>
	/\ finished = FALSE
	
Next ==
	\/
		/\ ((step > 0 /\ first <= last) \/ (step < 0 /\ first >= last))
		/\ result' = Append(result, fun[first])
		/\ finished' = finished
		/\ first' = first+step
		/\ last' = last
		/\ step' = step
		/\ fun' = fun
		
	\/
		/\ (~(step > 0 /\ first <= last) \/ (step < 0 /\ first >= last))
		/\ result' = result
		/\ finished' = TRUE
		/\ first' = first
		/\ last' = last
		/\ step' = step
		/\ fun' = fun
		
Spec == Init /\ [][Next]_<<first, last, step, fun, result, finished>>

====