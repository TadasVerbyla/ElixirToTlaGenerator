---- MODULE FibFromAST ----
EXTENDS Naturals, Integers, TLC, Sequences
CONSTANT N
VARIABLES stack, return

Init == 
    
    \* Inputs:
    \* [
    \*     [[[:n, nil]]],   # kintamasis n
    \* [
    \*     [
    \*         [[[:<, [:n, nil], 2]]], # pirmo atvejo salygos, pirmas sarasas nurodo tas, kurias turi tenkinti, antras nurodo neiginius. 
    \*         []
    \*     ], 
    \*     [
    \*         [],                     # antro atvejo salygos, turi tik pirmo atvejo salygos paneigima
    \*         [[[:<, [:n, nil], 2]]]
    \*     ]
    \* ],
    \*     [
    \*         [[{0, [:n, nil]}]], # pirmo atvejo funkcijos blokas (tik vienas)
    \*         [
    \*              [{0, [:-, [[:n, nil], 1]]}, {1, [:fib, [fn_nr: 0]]}], # antro atvejo blokai
    \*              [{2, [:-, [[:n, nil], 2]]}, {3, [:fib, [fn_nr: 2]]}],
    \*              [{4, [:+, [fn_nr: 1, fn_nr: 3]]}]
    \*         ]
    \*     ]
    \* ]

    /\  stack = <<[
            n |-> N,
            res_case_1 |-> <<-1>>,
            res_case_2 |-> <<-1, -1, -1>>,
            case_counter |-> 1,
            block_counter |-> 1
        ]>>
    /\  return = -1

AppendToStart(item, list) == <<item>> \o list
  
Next ==
    
    \* ================================ VALUE RETURNS =====================================

    \* ==== CASE 1 =====

    \* Jei pasiektas pirmojo atvejo vykdymo galas, grazina atvejo reiksme
    \* Kadangi atveji sudaro 1 blokas, bus validu, kai bloko reiksme bus 1 + 1
    \/  /\ stack[1].case_counter = 1
        /\ stack[1].block_counter = 2
        /\ stack' = SubSeq(stack, 2, Len(stack))
        \* /\ LET clause_result = stack[1].res_case_1[1] IN
        /\ return' = stack[1].res_case_1[1]

    \* ==== CASE 2 =====

    \* Tas pats su antru atveju
    \/  /\ stack[1].case_counter = 2
        /\ stack[1].block_counter = 4
        /\ stack' = SubSeq(stack, 2, Len(stack))
        \* /\ LET clause_result = stack[1].res_case_2[1] + stack[1].res_case_2[2] IN
        /\ return' = stack[1].res_case_2[1] + stack[1].res_case_2[2]


    \* ================================== CASE 1 ==========================================

    \* ==== BLOCK 1 =====

    \* Pirma tikrinamas pirmos salygos pirmas (ir vienintelis) blokas
    \/  /\ stack[1].case_counter = 1
        /\ stack[1].block_counter = 1
        /\ stack[1].n < 2
        /\ stack' = [stack EXCEPT ![1].res_case_1[1] = stack[1].n, ![1].block_counter = 2]
        /\ return' = -1

    \* Jei pirmas atvejis salygos netenkina, pereinama prie antros salygos
    \/  /\ stack[1].case_counter = 1
        /\ stack[1].block_counter = 1
        /\ ~stack[1].n < 2
        /\ stack' = [stack EXCEPT ![1].case_counter = 2, ![1].block_counter = 1]
        /\ return' = -1

    \* ================================== CASE 2 ==========================================

    \* ==== BLOCK 1 =====

    \* Toliau tikrinami antros salygos blokai. Kiekviena tikrinima sudaro paieskos ir priskyrimo busenos
    \/  /\ stack[1].case_counter = 2
        /\ stack[1].block_counter = 1
        /\ ~stack[1].n < 2
        /\ return = -1
        /\ stack' = AppendToStart([stack[1] EXCEPT !.n = stack[1].n - 1, !.case_counter = 1, !.block_counter = 1, !.res_case_2 = <<-1, -1, -1>>], stack)
        /\ return' = -1

    \/  /\ stack[1].case_counter = 2
        /\ stack[1].block_counter = 1
        /\ ~stack[1].n < 2
        /\ ~return = -1
        /\ stack' = [stack EXCEPT ![1].res_case_2[1] = return, ![1].block_counter = 2]
        /\ return' = -1

    \* ==== BLOCK 2 =====
    \* Beveik identiskas pirmam blokui
    \/  /\ stack[1].case_counter = 2
        /\ stack[1].block_counter = 2
        /\ ~stack[1].n < 2
        /\ return = -1
        /\ stack' = AppendToStart([stack[1] EXCEPT !.n = stack[1].n - 2, !.case_counter = 1, !.block_counter = 1, !.res_case_2 = <<-1, -1, -1>>], stack)
        /\ return' = -1

    \/  /\ stack[1].case_counter = 2
        /\ stack[1].block_counter = 2
        /\ ~stack[1].n < 2
        /\ ~return = -1
        /\ stack' = [stack EXCEPT ![1].res_case_2[2] = return, ![1].block_counter = 3]
        /\ return' = -1

    \* ==== BLOCK 3 =====
    \* Paskutinis blokas neturi rekursijos, tik apdoroja buvusiu bloku reiksmes
    \/  /\ stack[1].case_counter = 2
        /\ stack[1].block_counter = 3
        /\ ~stack[1].n < 2
        /\ return = -1
        /\ stack' = [stack EXCEPT ![1].res_case_2[3] = stack[1].res_case_2[1] + stack[1].res_case_2[3], ![1].block_counter = 4]
        /\ return' = -1

Spec == Init /\ [][Next]_<<stack>>

====