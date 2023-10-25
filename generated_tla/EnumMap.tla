---- MODULE EnumMap ----
EXTENDS Integers, Sequences
CONSTANTS L1
VARIABLES l1, output
Init ==
	/\ l1 = L1
	/\ output = <<>>
	
Next ==
	/\ l1 # <<>>
	/\ output' = Append(output, Head(l1) * 2)
	/\ l1' = Tail(l1)
	
Spec == Init /\ [][Next]_<<l1, output>>

====