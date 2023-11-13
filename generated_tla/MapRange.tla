---- MODULE MapRange ----
EXTENDS Integers, Sequences
CONSTANTS First, Last, Step, Fun
VARIABLES first, last, step, fun, result
Init ==
	/\ first = First
	/\ last = Last
	/\ step = Step
	/\ fun = Fun
	/\ result = <<>>
	
Next ==
	/\ ((step > 0 /\ first <= last) \/ (step < 0 /\ first >= last))
	/\ result' = Append(result, fun[first])
	/\ first' = first+step
	/\ last' = last
	/\ step' = step
	/\ fun' = fun
	
Spec == Init /\ [][Next]_<<first, last, step, fun>>

====