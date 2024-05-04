---- MODULE FibCopy ----
EXTENDS Naturals, Integers, TLC, Sequences
CONSTANT N
VARIABLES stack, return

Init == 
    
    /\  stack = <<[
            n |-> N,
            res_func_1 |-> -1,
            res_func_2 |-> -1,
            program_counter |-> 1
        ]>>
    /\  return = -1

AppendToStart(item, list) == <<item>> \o list
  
Next == 

    \* Disjunktas, nusakantis elgsena, kai surandami visi rekursyviu kvietimu rezultatai
    \/  /\ stack[1].program_counter = 3
        /\ stack' = SubSeq(stack, 2, Len(stack))
        \* /\ return' = stack[1].res_func_1 + stack[1].res_func_2
        /\ LET fc = stack[1].res_func_1 + stack[1].res_func_2 IN
        /\ return' = fc
        
    \* Disjunktai, nusakantys rezultato is zemesnio lygmens priskyrima einamajam rekursyvaus kvietimo rezultatui
    \/  /\ return > -1
        /\ stack[1].program_counter = 1
        /\ stack' = [stack EXCEPT ![1].res_func_1 = return, ![1].program_counter = stack[1].program_counter + 1]
        /\ return' = -1

    \/  /\ return > -1
        /\ stack[1].program_counter = 2
        /\ stack' = [stack EXCEPT ![1].res_func_2 = return, ![1].program_counter = stack[1].program_counter + 1]
        /\ return' = -1

    \* Disjunktai paieskai i gyli, kai nera imanoma gauti rekursyvaus kvietimo rezultato, atskiri, priklausomai nuo einamojo kvietimo
    \/  /\ ~stack[1].n < 2
        /\ stack[1].program_counter = 1
        /\ return = -1
        /\ stack' = AppendToStart([stack[1] EXCEPT !.n = stack[1].n - 1, !.program_counter = 1], stack)
        /\ return' = return

    \/  /\ ~stack[1].n < 2
        /\ stack[1].program_counter = 2
        /\ return = -1
        /\ stack' = AppendToStart([stack[1] EXCEPT !.n = stack[1].n - 2, !.program_counter = 1], stack)
        /\ return' = return

    \* Disjunktai, surandantys base case rekursyviems kvietimams, kiekviena rek funkcija turi atskira
    \/  /\ stack[1].n < 2
        /\ stack' = SubSeq(stack, 2, Len(stack))
        /\ return' = stack[1].n

Spec == Init /\ [][Next]_<<stack>>


====