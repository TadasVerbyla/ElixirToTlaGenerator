---- MODULE Fib ----
EXTENDS Naturals, Integers, TLC, Sequences
CONSTANT N
VARIABLES stack

Init == 
    
    /\  stack = <<[
            n |-> N,
            result |-> 0,
            res_func_1 |-> -1,
            res_func_2 |-> -1, 
            finished |-> FALSE
        ]>>

AppendToStart(item, list) == <<item>> \o list
  
Next == 

    \/  /\ Len(stack) > 1
        /\ stack[1].res_func_1 > -1
        /\ stack[1].res_func_2 > -1
        /\ stack[2].res_func_1 = -1
        /\ LET new_first == [stack[2] EXCEPT !.res_func_1 = stack[1].res_func_1 + stack[1].res_func_2]
            IN  stack' = AppendToStart(new_first, SubSeq(stack, 3, Len(stack)))

    \/  /\ Len(stack) > 1
        /\ stack[1].res_func_1 > -1
        /\ stack[1].res_func_2 > -1
        /\ stack[2].res_func_1 > -1
        /\ stack[2].res_func_2 = -1
        /\ LET new_first == [stack[2] EXCEPT !.res_func_2 = stack[1].res_func_1 + stack[1].res_func_2]
            IN  stack' = AppendToStart(new_first, SubSeq(stack, 3, Len(stack)))

    \/  /\ Len(stack) = 1
        /\ stack[1].res_func_1 > -1
        /\ stack[1].res_func_2 > -1
        /\ stack' = <<[stack[1] EXCEPT !.result = stack[1].res_func_1 + stack[1].res_func_2, !.finished = TRUE]>>
        


    \/  /\ stack[1].n > 1
        /\ stack[1].res_func_1 = -1
        /\ stack[1].res_func_2 = -1
        /\ stack' = AppendToStart([stack[1] EXCEPT !.n = stack[1].n - 1], stack)

    \/  /\ stack[1].n > 1
        /\ stack[1].res_func_1 > -1
        /\ stack[1].res_func_2 = -1
        /\ stack' = AppendToStart([stack[1] EXCEPT !.n = stack[1].n - 2, !.res_func_1 = -1], stack)



    \/  /\ stack[1].n < 2
        /\ Len(stack) > 1
        /\ stack[2].res_func_1 = -1
        /\ LET new_first == [stack[2] EXCEPT !.res_func_1 = stack[1].n]
            IN  stack' = AppendToStart(new_first, SubSeq(stack, 3, Len(stack)))

    \/  /\ stack[1].n < 2
        /\ Len(stack) > 1
        /\ stack[2].res_func_1 > -1
        /\ stack[2].res_func_2 = -1
        /\ LET new_first == [stack[2] EXCEPT !.res_func_2 = stack[1].n]
            IN  stack' = AppendToStart(new_first, SubSeq(stack, 3, Len(stack)))

EndInvariant ==
    \/  /\ stack[1].finished = FALSE
    \/  /\ stack[1].result < 0 
        /\ stack[1].finished = TRUE

Spec == Init /\ [][Next]_<<stack>> /\ <>[]EndInvariant


====