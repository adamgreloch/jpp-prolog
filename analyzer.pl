% :- ensure loaded(library(lists)).

variables([k]).
arrays([chce]).
program([assign(array(chce, pid), 1),
  assign(k, pid),
  condGoto(array(chce, 1-pid) = 0, 5),
  condGoto(k = pid, 3),
  sekcja,
  assign(array(chce, pid), 0),
  goto(1)]).

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

initState(_, N, state(Vars, Arrays, Procs, [])) :-
  variables(VarNames), initVars(VarNames, Vars),
  arrays(ArrayNames), initArrays(ArrayNames, N, Arrays),
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

isTrue(E1 = E2, State, Pid) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  V1 = V2.
isTrue(E1 \= E2, State, Pid) :-
  \+isTrue(E1 = E2, State, Pid).
isTrue(E1 < E2, State, Pid) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  V1 < V2.

execute(assign(Ident, Expr), S0, Pid, S1) :-
  getVars(S0, Vars0),
  eval(Expr, S0, Pid, Value),
  selectchk(var(Ident, _), Vars0, T),   % semi-deterministically remove Ident from Vars0
  getVars(S1, [var(Ident, Value) | T]).
execute(assign(array(Ident, IExpr), Expr), S0, Pid, S1) :-
  getArrays(S0, Arrays0),
  eval(Expr, S0, Pid, Value),
  eval(IExpr, S0, Pid, I),
  member(arr(Ident, Data0), Arrays0),
  replace0(I, Data0, Value, Data1),
  selectchk(arr(Ident, _), Arrays0, T),   % semi-deterministically remove arr from Vars0
  getArrays(S1, [arr(Ident, Data1) | T]).
execute(sekcja, S0, Pid, S1) :-
  getCrit(S0, []) -> getCrit(S1, [Pid]); 
  getCrit(S0, Crit), throw(unsafe([Pid|Crit])).

% execute(assign(array(Ident, i), _), (_, Arrays0), (_, Arrays1)).

replace0(I, L, E, R) :- nth0(I, L, _, L0), nth0(I, R, E, L0).
replace1(I, L, E, R) :- nth1(I, L, _, L0), nth1(I, R, E, L0).

empty([]).

getCrit(state(_, _, _, Crit), Crit).
getProcs(state(_, _, Procs, _), Procs).
getVars(state(Vars, _, _, _), Vars).
getArrays(state(_, Arrays, _, _), Arrays).

step(Program, S0, Pid, S1) :-
  getProcs(S0, Procs0),
  nth0(Pid, Procs0, InstrNum),    % find instruction number to execute by process
  (
    nth1(InstrNum, Program, goto(NextInstrNum));
    nth1(InstrNum, Program, condGoto(BExpr, JumpTo)), 
    (isTrue(BExpr, S0, Pid) -> NextInstrNum is JumpTo;
      NextInstrNum is InstrNum + 1
    );
    nth1(InstrNum, Program, Instr),
      execute(Instr, S0, Pid, S1),
      NextInstrNum is InstrNum + 1
  ),
  replace0(Pid, Procs0, NextInstrNum, Procs1),
  getProcs(S1, Procs1).

% runSeq(Program, S0, N, [S0 | T]) :-
%   step(Program, S0, N, SX),
%   runSeq(Program, SX, N, [S0 | Acc]).

% verifyT(N, Program) :-
%   initState(Program, N, State),


