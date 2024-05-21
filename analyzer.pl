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

initState(_, N, state(Vars, Arrays, Procs)) :-
  variables(VarNames), initVars(VarNames, Vars),
  arrays(ArrayNames), initArrays(ArrayNames, N, Arrays),
  initProcs(N, Procs).

lookupVar(Ident, [var(Ident, Value) | _], Value).
lookupVar(Ident, [_ | T], Value) :- lookupVar(Ident, T, Value).

evalBoth(E1, E2, State, N, Value1, Value2) :-
  eval(E1, State, N, Value1),
  eval(E2, State, N, Value2).

% assumes all used variables were previously defined
eval(Ident, state(Vars, _, _), _, Value) :- lookupVar(Ident, Vars, Value).

eval(E1 = E2, State, N, Value) :-
  evalBoth(E1, E2, State, N, V1, V2),
  (V1 = V2 -> Value is 1; Value is 0).
eval(E1 \= E2, State, N, Value) :-
  eval(E1 = E2, State, N, V),
  Value is 1 - V.
eval(E1 < E2, State, N, Value) :-
  evalBoth(E1, E2, State, N, V1, V2),
  (V1 < V2 -> Value is 1; Value is 0).
eval(E1 + E2, State, N, Value) :-
  evalBoth(E1, E2, State, N, V1, V2),
  Value is V1 + V2.
eval(E1 - E2, State, N, Value) :-
  evalBoth(E1, E2, State, N, V1, V2),
  Value is V1 - V2.
eval(E1 * E2, State, N, Value) :-
  evalBoth(E1, E2, State, N, V1, V2),
  Value is V1 * V2.
eval(E1 / E2, State, N, Value) :-
  evalBoth(E1, E2, State, N, V1, V2),
  Value is V1 / V2.
eval(Num, _, _, Num) :- number(Num).
eval(pid, _, N, N).

% step(Program, (Vars0, Arrays0, Procs0), Pid, StateOut) :-
