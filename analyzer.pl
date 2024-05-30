:- ensure_loaded(library(lists)).

initProcs(0, []).
initProcs(N, [1 | T]) :- 
  N > 0, K is N - 1, initProcs(K, T).

initVars([], []).
initVars([Ident | T1], [var(Ident, 0)|T2]) :- initVars(T1, T2).

initArray(0, []).
initArray(N, [0 | R]) :- 
  N > 0, K is N - 1, initArray(K, R).

initArrays([], _, []).
initArrays([Ident | T1], N, [arr(Ident, A)|T2]) :- initArray(N, A), initArrays(T1, N, T2).

initState(VarNames, ArrayNames, _, N, state(Vars, Arrays, Procs, [])) :-
  initVars(VarNames, Vars),
  initArrays(ArrayNames, N, Arrays),
  initProcs(N, Procs).

lookupVar(Ident, [var(Ident, Value) | _], Value).
lookupVar(Ident, [_ | T], Value) :- lookupVar(Ident, T, Value).

evalBoth(E1, E2, State, Pid, Value1, Value2) :-
  eval(E1, State, Pid, Value1),
  eval(E2, State, Pid, Value2).
eval(E1 + E2, State, Pid, Value) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  Value is V1 + V2.
eval(E1 - E2, State, Pid, Value) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  Value is V1 - V2.
eval(E1 * E2, State, Pid, Value) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  Value is V1 * V2.
eval(E1 / E2, State, Pid, Value) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  Value is V1 / V2.
eval(pid, _, Pid, Pid).
eval(Num, _, _, Num) :- number(Num).

% assumes all used variables were previously defined
eval(Ident, state(Vars, _, _, _), _, Value) :- member(var(Ident, Value), Vars).

eval(array(Ident, Expr), State, Pid, Value) :- 
  eval(Expr, State, Pid, I),
  getArrays(State, Arrays),
  member(arr(Ident, Data), Arrays),
  nth0(I, Data, Value).

isTrue(E1 = E2, State, Pid) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  V1 = V2.
isTrue(E1 \= E2, State, Pid) :-
  \+isTrue(E1 = E2, State, Pid).
isTrue(E1 < E2, State, Pid) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  V1 < V2.

replace0(I, L, E, R) :- nth0(I, L, _, L0), nth0(I, R, E, L0).
replace1(I, L, E, R) :- nth1(I, L, _, L0), nth1(I, R, E, L0).

getVars(state(Vars, _, _, _), Vars).
getArrays(state(_, Arrays, _, _), Arrays).
getProcs(state(_, _, Procs, _), Procs).
getCrit(state(_, _, _, Crit), Crit).

setVars(state(_, A, P, C), V1, state(V1, A, P, C)).
setArrays(state(V, _, P, C), A1, state(V, A1, P, C)).
setProcs(state(V, A, _, C), P1, state(V, A, P1, C)).
setCrit(state(V, A, P, _), C1, state(V, A, P, C1)).

execute(assign(Ident, Expr), S0, Pid, S1) :-
  getVars(S0, Vars0),
  eval(Expr, S0, Pid, Value),
  selectchk(var(Ident, _), Vars0, T),   % semi-deterministically remove Ident from Vars0
  setVars(S0, [var(Ident, Value) | T], S1).
execute(assign(array(Ident, IExpr), Expr), S0, Pid, S1) :-
  getArrays(S0, Arrays0),
  eval(Expr, S0, Pid, Value),
  eval(IExpr, S0, Pid, I),
  member(arr(Ident, Data0), Arrays0),
  replace0(I, Data0, Value, Data1),
  selectchk(arr(Ident, _), Arrays0, T),   % semi-deterministically remove arr from Vars0
  setArrays(S0, [arr(Ident, Data1) | T], S1).
execute(sekcja, S0, _, S1) :- setCrit(S0, [], S1).

stepInstr(S0, _, goto(NextInstrNum), _, S0, NextInstrNum).
stepInstr(S0, InstrNum, condGoto(BExpr, JumpTo), Pid, S0, NextInstrNum) :-
  (  isTrue(BExpr, S0, Pid) -> NextInstrNum is JumpTo
  ;  NextInstrNum is InstrNum + 1
  ).
stepInstr(S0, InstrNum, Instr, Pid, S1, NextInstrNum) :-
  execute(Instr, S0, Pid, S1),
  NextInstrNum is InstrNum + 1.

checkSafety(Program, S0, Pid, InstrNum, S1) :-
  nth1(InstrNum, Program, sekcja) -> (
  getCrit(S0, Crit),
  (  Crit = [] -> setCrit(S0, [Pid], S1)
  ;  throw(unsafe(S0, [Pid|Crit]))
  ))
  ; S0 = S1.

step(Program, S0, Pid, S3) :-
  getProcs(S0, Procs0),
  nth0(Pid, Procs0, InstrNum),    % find instruction number to execute by process
  nth1(InstrNum, Program, Instr), % get program instruction from its number
  stepInstr(S0, InstrNum, Instr, Pid, S1, NextInstrNum),
  replace0(Pid, Procs0, NextInstrNum, Procs1),
  setProcs(S1, Procs1, S2),
  checkSafety(Program, S2, Pid, NextInstrNum, S3).

init(K) :- empty(K).

get(E, [E|X]-Y, X-Y).

put(E, X-[E|Y], X-Y).

empty(X - X) :- var(X).

justProcs([S | T1], [Procs | T2]) :- getProcs(S, Procs), justProcs(T1, T2).
justProcs([], []).

catchUnsafe(Goal, PrevSs) :-
  catch(Goal, unsafe(SN, Unsafe),
    (
    justProcs([SN | PrevSs], ProcHis),
    reverse(ProcHis, RevProcHis),
    format('Program jest niepoprawny.\nNiepoprawny przeplot: ~p\nProcesy w sekcji: ~p',
    [RevProcHis, Unsafe]),
    fail % fail immediately to print just one bad interleaving
    )
  ).

stepForEachProc(_, _, N, Pid, Q0, Q0) :- Pid is N.

stepForEachProc(Program, (S0, PrevSs), N, Pid, Q0, Q2) :- Pid < N,
  catchUnsafe(step(Program, S0, Pid, S1), [S0 | PrevSs]),
  put((S1, [S0 | PrevSs]), Q0, Q1),
  NextPid is Pid + 1,
  stepForEachProc(Program, (S0, PrevSs), N, NextPid, Q1, Q2).

search(_, _, Q0, _) :- empty(Q0), !.

search(Program, N, Q0, Visited) :-
  get((S0, PrevSs), Q0, Q1), 
  (member(S0, Visited) ->
  search(Program, N, Q1, Visited); % skip S0, checked already
  stepForEachProc(Program, (S0, PrevSs), N, 0, Q1, Q2), % else: step through S0
  search(Program, N, Q2, [S0 | Visited])).

verifyT(N, Vars, Arrays, Program) :-
  initState(Vars, Arrays, Program, N, State),
  init(Q0),
  put((State, []), Q0, Q1),
  search(Program, N, Q1, []),
  format('Program jest poprawny (bezpieczny).', []).

verify(N, File) :-
  N < 1 -> format('Error: parametr ~p powinien byc liczba > 0', [N]), fail;
  catch(see(File), _, (format('Error: brak pliku o nazwie - ~p', [File]), fail)),
  read(variables(VarNames)),
  read(arrays(ArrNames)),
  read(program(Program)),
  seen,
  verifyT(N, VarNames, ArrNames, Program).
