:- ensure_loaded(library(lists)).

% System state is represented by:
%
%   state(Vars, Arrays, Procs, Crit)
%
% where:
%   - `Vars` is list of terms `var(Ident, Value)`. Forms a mapping between
%   variable identifiers and their values.
%   - `Arrays` is a list of terms `arr(Ident, Data)`. Ident is array
%   identifier, Data is a list of length N that stores the array's contents.
%   - `Procs` is an array in which i-th cell denotes that proces with pid=i 
%   is ready to execute the number of instruction in the cell.
%   - `Crit` is a list of process PIDs that are currently in the critical
%   section. In practice, it is either empty or there is only one process in,
%   otherwise exception is thrown because program is unsafe. It is empty by
%   default.

%% State initialization

% init Procs to N-sized list of all ones
initProcs(0, []).
initProcs(N, [1 | T]) :- 
  N > 0, K is N - 1, initProcs(K, T).

% init all variables to zeros
initVars([], []).
initVars([Ident | T1], [var(Ident, 0)|T2]) :- initVars(T1, T2).

% init an array to N-sized zero array
initArray(0, []).
initArray(N, [0 | R]) :- 
  N > 0, K is N - 1, initArray(K, R).

% init all identifiers to to N-sized zero arrays
initArrays([], _, []).
initArrays([Ident | T1], N, [arr(Ident, A)|T2]) :-
  initArray(N, A), initArrays(T1, N, T2).

% init system state
initState(VarNames, ArrayNames, _, N, state(Vars, Arrays, Procs, [])) :-
  initVars(VarNames, Vars),
  initArrays(ArrayNames, N, Arrays),
  initProcs(N, Procs).

%% Setters and getters

getVars(state(Vars, _, _, _), Vars).
getArrays(state(_, Arrays, _, _), Arrays).
getProcs(state(_, _, Procs, _), Procs).
getCrit(state(_, _, _, Crit), Crit).

setVars(state(_, A, P, C), V1, state(V1, A, P, C)).
setArrays(state(V, _, P, C), A1, state(V, A1, P, C)).
setProcs(state(V, A, _, C), P1, state(V, A, P1, C)).
setCrit(state(V, A, P, _), C1, state(V, A, P, C1)).

%% Expression evaluation

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
eval(Ident, state(Vars, _, _, _), _, Value) :-
  member(var(Ident, Value), Vars). % lookup Value under var's Ident

eval(array(Ident, Expr), State, Pid, Value) :- 
  eval(Expr, State, Pid, I),
  getArrays(State, Arrays),
  member(arr(Ident, Data), Arrays), % lookup Data under array's Ident
  nth0(I, Data, Value). % get Value under I-th index in Data

isTrue(E1 = E2, State, Pid) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  V1 = V2.
isTrue(E1 \= E2, State, Pid) :-
  \+isTrue(E1 = E2, State, Pid).
isTrue(E1 < E2, State, Pid) :-
  evalBoth(E1, E2, State, Pid, V1, V2),
  V1 < V2.

%% Statement execution

% replace{0,1} set I-th value in the list to E (counting from {0,1},
% accordingly)
replace0(I, List, E, Res) :- nth0(I, List, _, L0), nth0(I, Res, E, L0).
replace1(I, List, E, Res) :- nth1(I, List, _, L0), nth1(I, Res, E, L0).

execute(assign(Ident, Expr), S0, Pid, S1) :-
  getVars(S0, Vars0),
  eval(Expr, S0, Pid, Value),
  selectchk(var(Ident, _), Vars0, T), % get T with Ident removed
  setVars(S0, [var(Ident, Value) | T], S1). % map var Ident mapped to new Value
execute(assign(array(Ident, IExpr), Expr), S0, Pid, S1) :-
  getArrays(S0, Arrays0),
  eval(Expr, S0, Pid, Value), % evaluate new value
  eval(IExpr, S0, Pid, I), % evaluate index expression
  member(arr(Ident, Data0), Arrays0), % lookup array ident for it's data
  replace0(I, Data0, Value, Data1), % update I-th value in data to new one
  selectchk(arr(Ident, _), Arrays0, T), % get T with Ident removed
  setArrays(S0, [arr(Ident, Data1) | T], S1). % map array Ident to new Data
execute(sekcja, S0, _, S1) :- setCrit(S0, [], S1).

%% Step function

stepInstr(S0, _, goto(NextInstrNum), _, S0, NextInstrNum).
stepInstr(S0, InstrNum, condGoto(BExpr, JumpTo), Pid, S0, NextInstrNum) :-
  (  isTrue(BExpr, S0, Pid) -> NextInstrNum is JumpTo
  ;  NextInstrNum is InstrNum + 1
  ).
stepInstr(S0, InstrNum, Instr, Pid, S1, NextInstrNum) :-
  execute(Instr, S0, Pid, S1),
  NextInstrNum is InstrNum + 1.

% check whether the instruction under InstrNum is a critical section access
% if so, and:
%   - section is empty, then add the Pid to Crit, updating the S1
%   - section is occupied, throw exception, because program is unsafe
% otherwise, do nothing (pass S0 as S1 unchanged).
checkSafety(Program, S0, Pid, InstrNum, S1) :-
  nth1(InstrNum, Program, sekcja) -> (
  getCrit(S0, Crit),
  (  Crit = [] -> setCrit(S0, [Pid], S1)
  ;  throw(unsafe(S0, [Pid|Crit]))
  ))
  ; S0 = S1.

step(Program, S0, Pid, S3) :-
  getProcs(S0, Procs0),
  nth0(Pid, Procs0, InstrNum),    % find instr number to execute by process
  nth1(InstrNum, Program, Instr), % get program instr from its number
  stepInstr(S0, InstrNum, Instr, Pid, S1, NextInstrNum), % step through instr
  replace0(Pid, Procs0, NextInstrNum, Procs1), % update Pid's instr num to next
  setProcs(S1, Procs1, S2), % update State with new Procs 
  checkSafety(Program, S2, Pid, NextInstrNum, S3). % check safety of new State

%% Queue operations

% init(Queue)
init(Q) :- empty(Q).

% get(Elem, OldQueue, ResQueue)
get(E, [E|X]-Y, X-Y).

% put(Elem, OldQueue, ResQueue)
put(E, X-[E|Y], X-Y).

% empty(Queue)
empty(X - X) :- var(X).

%% Unsafe error catching and pretty printing

% unwrap Procs from States
justProcs([State | T1], [Proc | T2]) :-
  getProcs(State, Proc), justProcs(T1, T2).
justProcs([], []).

% perform a Goal and watch for exception unsafe(BadState, Crit).
% If one occurs, print a corresponding interleaving and fail.
% PrevSs is a history of states in a given interleaving with
% newest state first
catchUnsafe(Goal, PrevSs) :-
  catch(Goal, unsafe(BS, Crit),
    (
    justProcs([BS | PrevSs], ProcHis), % add BS to history
    reverse(ProcHis, RevProcHis), % reverse so that states are old to new
    format(
    'Program jest niepoprawny.\nNiepoprawny przeplot: ~p\nProcesy w sekcji: ~k',
    [RevProcHis, Crit]),
    fail % fail immediately to print just one bad interleaving
    )
  ).

%% BFS search over states

% reminder: PIDs are from 0, ..., N-1

% if Pid = N, do nothing
stepForEachProc(_, _, N, Pid, Q0, Q0) :- Pid is N.

% generate next states by stepping through S0 by all N processes and add them
% to BFS queue
stepForEachProc(Program, (S0, PrevSs), N, Pid, Q0, Q2) :- Pid < N,
  catchUnsafe(step(Program, S0, Pid, S1), [S0 | PrevSs]),
  put((S1, [S0 | PrevSs]), Q0, Q1),
  NextPid is Pid + 1,
  stepForEachProc(Program, (S0, PrevSs), N, NextPid, Q1, Q2).

% if queue empty, search is completed
search(_, _, Q0, _) :- empty(Q0),
  !. % cut to prevent endless backtracking after visiting all states

% perform BFS search for all states in queue until it's empty
search(Program, N, Q0, Visited) :-
  get((S0, PrevSs), Q0, Q1), 
  (member(S0, Visited) ->
  search(Program, N, Q1, Visited); % skip S0, visited already
  stepForEachProc(Program, (S0, PrevSs), N, 0, Q1, Q2), % else: step through S0
  search(Program, N, Q2, [S0 | Visited])). % continue the loop

% term version of verify 
verifyT(N, Vars, Arrays, Program) :-
  initState(Vars, Arrays, Program, N, State),
  init(Q0),
  put((State, []), Q0, Q1), % add init state with no history to queue
  search(Program, N, Q1, []), % begin BFS
  format('Program jest poprawny (bezpieczny).', []).

%% End-user predicates

verify(N, File) :-
  N < 1 -> format('Error: parametr ~p powinien byc liczba > 0', [N]), fail;
  catch(see(File), _,
    (format('Error: brak pliku o nazwie - ~p', [File]), fail)
    ),
  read(variables(VarNames)),
  read(arrays(ArrNames)),
  read(program(Program)),
  seen,
  verifyT(N, VarNames, ArrNames, Program).
