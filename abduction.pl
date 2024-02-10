/**
 * @author	Jiefei Ma
 * @date		Feb. 2011 (initial version)
 * Department of Computing, Imperial College London
 * 
 * NOTE: this lite version of the system has been tested with SICStus 4.1.1 and YAP 6.2.1
 * NOTE: this lite version can generate query trace in graphml format, which can
 * then be used in yEd (http://www.yworks.com/en/products_yed_about.html)
 *
 * Change Log:
 *  2011/11/02 - added eval_all/2 and eval_all_with_ground_query/2 macros
 *             - added auto system built-in predicate recognition
 * 	2011/07/13 - added depth bound support
 * 	2011/07/12 - fixed floundering case for goal "X in Min..Max"
 *  2011/03/18 - fixed bug in preprocessing defined abducibles (thanks Antonis Kakas)
 *             - added predicates for specifying maximum state count for the 
 *               tracer.
 */

% # ===================== Documentation ======================
% 
% 1. Syntax for user input files:
% 
% * abducible, defined (a.k.a. non-abducible) and builtin are predicates
%   e.g. holds(has(jeff, apple), 3), member(X, [2,3])
%
% * a negative literal is "\+ A" where "A" is an abducible, defined or builtin
%
% * a finite domain constraint is one used in "library(clpfd)"
%   e.g. X in 1..3, Y #< Z - 3, X #\= Y
%
% * a real domain constraint is one used in "library(clpr)"
%   e.g. {X + 3 = Y -2}
%
% * an equality is "X = Y", an inequality is "X =/= Y".
%
% 2. Each input file should specify an abductive framework:
%
% * an abducible is declared as:
%
%   abducible(happens(_,_)).
%
% * a builtin is declared as:
%
%   builtin(member(_,_)).
%
% * a rule is specified as:
%
%   holds(F,T) :- 
%     happens(A, T1),
%     T1 #< T,
%     initiates(A, F, T1),
%     \+ clipped(F, T1, T).
%
% * an integrity is specified as:
%
%   ic :- happens(A1, T), happens(A2, T), A1=/=A2.
%
% 3. Loading and querying the System
%
% * Load a user defined abductive theory of <P, A, B, I>, where "P" is a 
%   set of rules called the background knowledge, "A" is the set of abducible 
%   predicates, "B" is the set of builtin predicates, and "I" is the set of 
%   integrity constraints,  e.g. 
%   
%     ?- load_theory('blocksworld.pl').
% 
%   or if the theory in different files:
%   
%     ?- load_theories(['system.pl', 'policies.pl', 'domain.pl']).
%
% * Query the system:
%   e.g. 

%     ?- query([T #> 0, T #< 10, holds(has(jiefei, apple), T)], Ans)
%
%  If succeeded, Ans has the form (As, Cs, Ns, Info) where "As" is the set of 
%  collected abducibles, "Cs" is the set of collected inequalities, finite 
%  domain constraints, and real domain constraints, "Ns" is the set of 
%  collected dynamic denials and "Info" is the user collected data along the 
%  computation.
%
% * To clean up the already loaded theory (so that a new one can be loaded):
%
%    ?- clear_theory.
%
% ==========================  End of Documentation ===========================

:- module(abduction, [
		% for the inequality store
		'=/='/2, inequalities/2,
		% #load_theory(+TheoryFile)
		load_theory/1,
		% #load_theories(+ListOfTheoryFiles)
		load_theories/1,
		% #clear_theory
		% for clearing the loaded theory
		clear_theory/0,
		% #query(+ListOfGoals, -SolvedState)
		% for querying the system
		query/2,
		% #eval(+ListOfGoals, -GloballyMinimalGroundHypotheses)
		eval/2,
		eval_with_one_labelling/2,  %TONY-MA 2ndNov2012
		label/1,
		% #eval(+ListOfGoals, +TimeOut, -GloballyMinimalGroundHypotheses)
		eval/3,
		% #query_all(+ListOfGoals) and #eval_all(+ListOfGoals)
		% for pretty output of all the solutions
		query_all/1,
		eval_all/1,
		% eval_all(+ListOfGoals, -AllGroundQueryMinimalHypothesesPairs)
		% eval_all_with_ground_query(+ListOfGroundGoals, -AllGloballyMinimalGroundHypotheses)
		eval_all/2,
		eval_all_with_ground_query/2,
		% #enforce_labeling(+TrueOrFalse)
		% when it is set to 'true', all the finite domain variables in the state
		% will be grounded.  This can sometimes affect the performance (improved
		% or downgraded).
		enforce_labeling/1,
		% trace
		query_all_with_trace/1,
		query_all_with_trace/2,
		eval_all_with_trace/1,
		eval_all_with_trace/2,
		set_max_states/1,
		% depth bound
		set_depth_limit/1,
		clear_depth_limit/0,
		% turn on or off auto-builtin predicate recognition
		use_system_builtin/1
	]).

% ===================== Implementation ==============================

% ### Preamable ###

% need to declare the following operator for the subsequent conditional compilations
:- if(current_prolog_flag(dialect, yap)).
:- op(760, yfx, #<=>).
:- elif(current_prolog_flag(dialect, sicstus)).
:- op(760, yfx, #<==>).
:- endif.

% *** Constraint Solvers ***
:- use_module(library(clpfd)).
:- use_module(library(clpr)).

% For inequality store
:- use_module(library(atts)).
:- op(700, xfx, =/=).
:- attribute aliens/1.

% For meta-interpreter
:- use_module(library(ordsets), [
		ord_union/3,
		ord_intersection/3,
		list_to_ord_set/2
	]).


% *** Utilities ***
:- if(current_prolog_flag(dialect, yap)).
%{ YAP
:- use_module(library(terms), [
		unifiable/3,
		variables_within_term/3
	]).
:- use_module(library(apply_macros), [
		maplist/3,
		selectlist/3
	]).
:- use_module(library(lists), [
		member/2,
		append/3,
		select/3
	]).
%} YAP
:- elif(current_prolog_flag(dialect, sicstus)).
%{ SICStus
:- use_module(library(terms), [
		term_variables/2
	]).
:- use_module(library(lists), [
		maplist/3,
		select/3
	]).

variables_within_term(Vs, Term, OldVs) :-
	term_variables(Term, TVs),
	collect_old_variables(TVs, Vs, OldVs).
collect_old_variables([], _, []).
collect_old_variables([H|T], Vs, OldVs) :-
	collect_old_variables(T, Vs, OldVs1),
	(strictmember(Vs, H) ->
		OldVs = [H|OldVs1]
	;
		OldVs = OldVs1
	).

unifiable(X, Y, Eq) :-
	(var(X) ; var(Y)), !,
	(X == Y -> Eq = [] ; Eq = [X = Y]). 
unifiable(X, Y, []) :-
	atomic(X), atomic(Y), !, X == Y.
unifiable(X, Y, Eqs) :-
	functor(X, F, A),
	functor(Y, F, A), 
	X =.. [F|ArgsX],
	Y =.. [F|ArgsY],
	all_unifiable(ArgsX, ArgsY, Eqs).
all_unifiable([], [], []).
all_unifiable([X|TX], [Y|TY], AllEqs) :-
	unifiable(X, Y, Eqs),
	all_unifiable(TX, TY, RestEqs),
	append(Eqs, RestEqs, AllEqs).

selectlist(Pred, L1, L2) :- 
	selectlist_aux(L1, Pred, L2).
selectlist_aux([], _, []).
selectlist_aux([H|T], P, L) :-
	selectlist_aux(T, P, L1),
	(\+ \+ call(P, H) ->
		L = [H|L1]
	;
		L = L1
	).

:- dynamic mysetvalue/2.
set_value(Key, Val) :- retractall(mysetvalue(Key, _Val)), assert(mysetvalue(Key, Val)).
get_value(Key, Val) :- mysetvalue(Key, Val).
inc_value(Key, NewVal, OldVal) :-
	get_value(Key, OldVal),
	NewVal is OldVal + 1,
	set_value(Key, NewVal).

forall(X, Y) :- \+ (X, \+ Y).
%} SICStus
:- endif.

unifiable(X, Y) :- \+ \+ (X = Y).

nonground(X) :- \+ ground(X).

strictdelete([], _, []).
strictdelete([H|T], X, R) :-
	(H == X ->
		strictdelete(T, X, R)
	;
		strictdelete(T, X, R1),
		R = [H|R1]
	).

% ----------------------------------------------------------------------------------------
% --- Preprocessing ---
use_system_builtin(true) :-
	set_value(sys_builtin, true).
use_system_builtin(false) :-
	set_value(sys_builtin, false).
:- use_system_builtin(true).

load_theory(DataFile) :-
	clear_theory,
	loadf(DataFile, Cls),
	assert_knowledge(Cls).

load_theories(DataFiles) :-
	clear_theory,
	loadfs(DataFiles, Cls),
	assert_knowledge(Cls).

clear_theory :-
	clean_up.

% Predicates used for specifying the in
:- dynamic abducible/1, builtin/1. % used by users and the system
:- dynamic enum/2, types/2. % EXP: used for specifying abducible argument types
:- dynamic abhead/2. % EXP: used for transforming rules with abducible in the head
:- dynamic rule/2, ic/1. % used by the meta-interpreter

clean_up :-
	retractall(abducible(_)),
	retractall(enum(_,_)), % EXP
	retractall(types(_, _)), % EXP
	retractall(abhead(_,_)),
	retractall(builtin(_)),
	retractall(rule(_,_)),
	retractall(ic(_)).

% [Literal Type]: 
%
% In order to speed up the search, each input rule or integrity constraint
% is preprocessed when it is loaded, such that each literal "L" is wrapped 
% as "(Type, L)", where "Type" is the literal type.
%
% There are four literal types: 
%  a: abducible
%  b: builtin
%  d: defined
%  e: equality
%  i: inequality
%  n: negation
%  f: finite domain constraint
%  r: real domain constraint
%  -: failure goal (see below)
%
% There is a special literal, of the form "fail(Vs, Literals)", called the 
% failure goal which can appear as a sub-goal during the abductive search.  
% Logically, the failure goal is "\forall Vs . <- Literals", where "Vs" is 
% the set of variables in "Literals" that are universally quantified with
% the scope the whole failure goal (denial).  All other varaibles in "Literals"
% are existentially quantified implicitly. "-" represents the type of a failure
% goal.

transform_and_wrap_literal(X, Xw) :-
	wrap_literal(X, (Type, G)),
	((Type == a, functor(G, Ftr, Ary), abhead(Ftr, Ary)) ->
		% need to transform it
		atom_concat(Ftr, '_', NewFtr),
		G =.. [Ftr|Params],
		NewG =.. [NewFtr|Params],
		Xw = (d, NewG)
	;
		Xw = (Type, G)
	).

wrap_literal(X, Xw) :-
	(X = (\+ A) ->
		% for negative literal, we need to wrap the atom too
		wrap_atom(A, Aw),
		Xw = (n, \+ Aw)
	;
		wrap_atom(X, Xw)
	).

wrap_atom(X = Y, (e, X = Y)) :- !.
wrap_atom(X=/=Y, (i, X=/=Y)) :- !.

wrap_atom({X}, (r, {X})) :- !.

wrap_atom(X in Y, (f, X in Y)) :- !.
wrap_atom(X #= Y, (f, X #= Y)) :- !.
wrap_atom(X #< Y, (f, X #< Y)) :- !.
wrap_atom(X #=< Y, (f, X #=< Y)) :- !.
wrap_atom(X #> Y, (f, X #> Y)) :- !.
wrap_atom(X #>= Y, (f, X #>= Y)) :- !.
wrap_atom(X #\= Y, (f, X #\= Y)) :- !.
wrap_atom(#\ X, (f, #\ X)) :- !.
wrap_atom(X #/\ Y, (f, X #/\ Y)) :- !.
wrap_atom(X #\/ Y, (f, X #\/ Y)) :- !.

wrap_atom(call(X), (b, X)) :- !.
wrap_atom(X, (b, X)) :-
	get_value(sys_builtin, true),
	predicate_property(X, Prop),
	(Prop == built_in ; Prop = imported_from(_)), !.
wrap_atom(X, (b, X)) :-
	builtin(X), !.

wrap_atom(X, (a, X)) :- 
	abducible(X), !.

wrap_atom(X, (d, X)). % for anything else, it is assumed to be a defined.

unwrap_literal((n, \+ (_, A)), (\+ A)) :- !.
unwrap_literal((-, fail(Vs, BodyW)), fail(Vs, Body)) :- 
	!, maplist(unwrap_literal, BodyW, Body).
unwrap_literal((_, A), A).

flatten_body(B, L) :-
	(B = (X, Y) ->
		flatten_body(Y, L1),
		L = [X|L1]
	;
		L = [B]
	).

transform_and_wrap_ic(Body, ic(NewBody)) :-
	flatten_body(Body, Lits),
	maplist(transform_and_wrap_literal, Lits, NewBody).
transform_and_wrap_fact(Head, rule(NewHead, [])) :-
	transform_and_wrap_literal(Head, NewHead).
transform_and_wrap_rule(Head, Body, rule(NewHead, NewBody)) :-
	flatten_body(Body, Lits),
	maplist(transform_and_wrap_literal, [Head|Lits], [NewHead|NewBody]).

unwrap_denial(fail(Vs, BodyW), fail(Vars, Body)) :-
	maplist(unwrap_literal, BodyW, Body),
	selectlist(nonground, Vs, Vars).
		
% /** API **/
% Read the user input file and perform preprocessing.
loadfs([], []).
loadfs([F|T], Cls):-
	loadfs(T, C2),
	loadf(F, C1),
	append(C1, C2, Cls).

loadf(DataFile, Cls) :-
	open(DataFile, read, IN),
	read_clauses(IN, Cls),
	close(IN).

assert_knowledge(Cls) :-
	assert_abducibles(Cls, Cls1),
	assert_enums(Cls1, Cls2), % EXP
	assert_types(Cls2, Cls3), % EXP
	assert_builtins(Cls3, Cls4),
	record_abducible_heads(Cls4),
	transform_and_assert_clauses(Cls4),
	assert_new_rules_for_transformed_abducibles.

read_clauses(IN, Cls) :-
	catch(read(IN, Term), Err, (write(Err), fail)),
	(Term == end_of_file ->
		Cls = []
	; Term = (:- D) ->
		call(D),
		read_clauses(IN, Cls)
	;
		read_clauses(IN, ClsRest),
		Cls = [Term|ClsRest]
	).

assert_abducibles([], []).
assert_abducibles([abducible(X)|T], L) :-
	!, 
	assertz(abducible(X)),
	assert_abducibles(T, L).
assert_abducibles([H|T], [H|L]) :-
	assert_abducibles(T, L).

assert_builtins([], []).
assert_builtins([builtin(X)|T], L) :-
	!, assertz(builtin(X)),
	assert_builtins(T, L).
assert_builtins([H|T], [H|L]) :-
	assert_builtins(T, L).

assert_enums([], []). % EXP
assert_enums([enum(X, D)|T], L) :-
	!, 
	ground(X), ground(D),
	D = [_|_], % L must be a non-empty list
	assertz(enum(X, D)),
	assert_enums(T, L).
assert_enums([H|T], [H|L]) :-
	assert_enums(T, L).

assert_types([], []). % EXP
assert_types([types(X, Conds)|T], L) :-
	!, 
	forall(member(C, Conds), (
		functor(C, Ftr, 2),
		(Ftr = '=' ; Ftr = type)
	)),
	assertz(types(X, Conds)),
	assert_types(T, L).
assert_types([H|T], [H|L]) :-
	assert_types(T, L).


transform_and_assert_clauses([]).
transform_and_assert_clauses([C|T]) :-
	(C = ( H :- B) ->
		(H == ic ->
			% preprocess and add integrity constraint
			transform_and_wrap_ic(B, IC),
			assert(IC)
		;
			% preprocess and add a rule
			transform_and_wrap_rule(H, B, Rule),
			assert(Rule)
		)
	;
		transform_and_wrap_fact(C, Fact),
		assert(Fact)
	),
	transform_and_assert_clauses(T).

record_abducible_heads(Cls) :-
	findall(abhead(AbPred,Arity), (
			member(C, Cls),
			(C = (H :- _) ->
				A = H
			;
				A = C
			),
			abducible(A),
			functor(A, AbPred, Arity)
		), AbHeads),
	list_to_ord_set(AbHeads, SortedAbHeads),
	forall(member(AbHead, SortedAbHeads), assertz(AbHead)).

assert_new_rules_for_transformed_abducibles :-
	forall(abhead(Ftr, Ary), (
		atom_concat(Ftr, '_', NewFtr),
		functor(H, NewFtr, Ary),
		H =.. [NewFtr|Args],
		B =.. [Ftr|Args],
		wrap_atom(H, Hw),
		wrap_atom(B, Bw),
		assert(rule(Hw, [Bw]))
	)).

% --- Abductive Meta-Interpreter (Depth-First) ---

% Ans: (As, Cs, Ns)
query(Query, Ans) :-
	initialise(Query, Gs, As, Cs, Ns, Info),
	solve_all(Gs, As, Cs, Ns, Info, Ans).

% solve_all(Gs, As, Cs, Ns, Info, Solution)
%   Gs: set of pending goals
%   As: set of collected abducibles
%   Cs: set of constraints, of the form (Es, Fs, Rs), where
%     Es: set of inequalities
%     Fs: set of finite domain constraints
%     Rs: set of real domain constraints
%   Info: any user-defined data structure for storing 
%     computational information, such as debug data
%   Solution: when the whole abductive computation succeeds,
%     this will contain the final answer

% base case: no more pending goals.  so it succeeds.
solve_all([], As, (Es, Fs, Rs), NsW, Info, (As, Cs, Ns)) :-
	extract_constraints((Es, Fs, Rs), Cs),
	maplist(unwrap_denial, NsW, Ns),
	inspect_successful_state(As, Cs, Ns, Info).
% recursive case: simple depth-first left-right search strategy
solve_all([(Type, G)|RestGs], As, Cs, Ns, Info, Sol) :-
	solve_one(Type, G, RestGs, As, Cs, Ns, Info, Sol).

solve_one(a, A, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((a, A), RestGs, As, Cs, Ns, Info, NewInfo),
	(
		% reuse hypotheses
		member(A, As),
		solve_all(RestGs, As, Cs, Ns, NewInfo, Sol)
	;	% a create new hypothesis
		force_types(A), % EXP
		resolve_abducible_with_delta(As, A, Inequalities), 
		propagate_inequalities(Inequalities, Cs, NewCs), 
		resolve_abducible_with_dynamic_ics(Ns, A, FailureGoals), 
		append(FailureGoals, RestGs, NewGs),
		solve_all(NewGs, [A|As], NewCs, Ns, NewInfo, Sol)
	).

solve_one(d, D, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((d, D), RestGs, As, Cs, Ns, Info, NewInfo),
	rule((d,D), B), % pick a rule
	append(B, RestGs, NewGs), % FIXME: solve constraints first?
	solve_all(NewGs, As, Cs, Ns, NewInfo, Sol).

solve_one(b, B, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((b, B), RestGs, As, Cs, Ns, Info, NewInfo),
	call(B), % backtrackable
	solve_all(RestGs, As, Cs, Ns, NewInfo, Sol).

solve_one(e, X = Y, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((e, X = Y), RestGs, As, Cs, Ns, Info, NewInfo),
	call(X = Y),
	solve_all(RestGs, As, Cs, Ns, NewInfo, Sol).

solve_one(i, X=/=Y, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((i, X=/=Y), RestGs, As, Cs, Ns, Info, NewInfo),
	propagate_inequalities([X=/=Y], Cs, NewCs), 
	solve_all(RestGs, As, NewCs, Ns, NewInfo, Sol).

solve_one(n, \+ G, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((n, \+ G), RestGs, As, Cs, Ns, Info, NewInfo),
	solve_one(-, fail([], [G]), RestGs, As, Cs, Ns, NewInfo, Sol).

solve_one(f, FC, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((f, FC), RestGs, As, Cs, Ns, Info, NewInfo),
	propagate_finite_domain_constraints([FC], Cs, NewCs),
	solve_all(RestGs, As, NewCs, Ns, NewInfo, Sol).

solve_one(r, RC, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_solve_one((r, RC), RestGs, As, Cs, Ns, Info, NewInfo),
	propagate_real_domain_constraints([RC], Cs, NewCs), 
	solve_all(RestGs, As, NewCs, Ns, NewInfo, Sol).

solve_one(-, fail(Vs, Lits), RestGs, As, Cs, Ns, Info, Sol) :-
	(safe_select_failure_literal(Lits, Vs, (Type, L), RestLits) ->
		fail_one(Type, L, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol)
	;
		inspect_solve_one((-, fail(Vs, Lits)), RestGs, As, Cs, Ns, Info, NewInfo),
		(Lits == [] ->
			fail % fail normally
		;
			(backup_safe_select_failure_literal(Lits, Vs, (Type, L), RestLits) ->
				fail_one(Type, L, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol)
			;
				% if "Lits" contains only finite domain constraints and/or 
				% real constraints, then we can try to test for satisfiability.
				% if it is satisfiable, then it fails normally (i.e. falsity 
				% can be derived); otherwise if it is not satisfiable, then
				% it succeeds.
				(partition_failure_literals(Lits, FCs, RCs) ->
					(\+ \+ (
								% can be satisfied?
								propagate_finite_domain_constraints(FCs, Cs, Cs1),
								propagate_real_domain_constraints(RCs, Cs1, _)
							) ->
						% yes, satisfiable.  so fail
						fail
					;
						% no, and hence no floundering, so continue the reasoning
						solve_all(RestGs, As, Cs, Ns, NewInfo, Sol)
					)
				; % indeed, it flounders.
					write('Floundered: '), write(fail(Vs, Lits)), nl, !, 
					fail
				)
			)
		)
	).

fail_one(a, A, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((a, A), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	resolve_failure_abducible_with_delta(As, A, Vs, RestLits, FailureGoals),
	append(FailureGoals, RestGs, NewGs),
	NewNs = [fail(Vs, [(a, A)|RestLits])|Ns],
	solve_all(NewGs, As, Cs, NewNs, NewInfo, Sol).

fail_one(d, D, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((d, D), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	findall(H-B, (rule((d, H), B), unifiable(H, D)), Rules),
	resolve_failure_non_abducible_with_rules(Rules, D, Vs, RestLits, FailureGoals),
	append(FailureGoals, RestGs, NewGs),
	solve_all(NewGs, As, Cs, Ns, NewInfo, Sol).

fail_one(b, B, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((b, B), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	findall(B-[], call(B), Rules),
	resolve_failure_non_abducible_with_rules(Rules, B, Vs, RestLits, FailureGoals),
	append(FailureGoals, RestGs, NewGs),
	solve_all(NewGs, As, Cs, Ns, NewInfo, Sol).

fail_one(e, X = Y, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((e, X = Y), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	((var(X), strictmember(Vs, X)) ->
		% X is uni. quant. and we don't care about Y
		strictdelete(Vs, X, NewVs),
		call(X = Y),
		solve_one(-, fail(NewVs, RestLits), RestGs, As, Cs, Ns, NewInfo, Sol)
	; (var(Y), strictmember(Vs, Y)) ->
		% Y is uni. quant. but X is not
		strictdelete(Vs, Y, NewVs),
		call(Y = X),
		solve_one(-, fail(NewVs, RestLits), RestGs, As, Cs, Ns, NewInfo, Sol)
	; var(X) ->
		% X is ex. quant. 
		% NB: by the safe selection strategy, "Y" doesn't contain any
		% universally quantified variable
		(
			% try to succeed in the inequality
			propagate_inequalities([X=/=Y], Cs, NewCs),
			solve_all(RestGs, As, NewCs, Ns, NewInfo, Sol)
		;
			% try to succeed in the equality and fail one of the rest literals
			call(X = Y),
			solve_one(-, fail(Vs, RestLits), RestGs, As, Cs, Ns, NewInfo, Sol)
		)
	; var(Y) ->
		% Y is ex. quant. but X is not
		% NB: by the safe selection strategy, "X" doesn't contain any
		% universally quantified variable
		(
			% try to succeed in the inequality
			propagate_inequalities([Y=/=X], Cs, NewCs),
			solve_all(RestGs, As, NewCs, Ns, NewInfo, Sol)
		;
			% try to succeed in the equality and fail one of the rest literals
			call(Y = X),
			solve_one(-, fail(Vs, RestLits), RestGs, As, Cs, Ns, NewInfo, Sol)
		)
	; % one of them is a variable
		(unifiable(X, Y, Es) ->
			maplist(wrap_atom, Es, EsW),
			append(EsW, RestLits, NewBody),
			solve_one(-, fail(Vs, NewBody), RestGs, As, Cs, Ns, NewInfo, Sol)
		;
			% this literal fails trivially
			solve_all(RestGs, As, Cs, Ns, NewInfo, Sol)
		)
	).

fail_one(i, X=/=Y, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((i, X=/=Y), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	(
		call(X = Y),
		solve_all(RestGs, As, Cs, Ns, NewInfo, Sol)
	;
		propagate_inequalities([X=/=Y], Cs, NewCs),
		solve_one(-, fail(Vs, RestLits), RestGs, As, NewCs, Ns, NewInfo, Sol)
	).

fail_one(n, \+ G, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((n, \+ G), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	(
		% Case 1:
		solve_all([G|RestGs], As, Cs, Ns, NewInfo, Sol)
	;
		% case 2:
		G = (Type, L),
		fail_one(Type, L, [], [], [(-, fail(Vs, RestLits))|RestGs], As, Cs, Ns, NewInfo, Sol)
	).

fail_one(f, C, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((f, C), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	(special_domain_condition(C, Vs) ->
		% need to treat this as a built-in for X in Dom
		C = (X in Dom),
		findall((X in Dom)-[], call((X in Dom, fd_label([X]))), Rules),
		resolve_failure_non_abducible_with_rules(Rules, C, Vs, RestLits, FailureGoals),
		append(FailureGoals, RestGs, NewGs),
		solve_all(NewGs, As, Cs, Ns, NewInfo, Sol)
	;
		fd_entailment(C, B), % reitification
		(B == 0 -> 
			% the constraint can never hold anyway
			solve_all(RestGs, As, Cs, Ns, NewInfo, Sol)
		; B == 1 ->
			% the constraint always hold
			solve_one(-, fail(Vs, RestLits), RestGs, As, Cs, Ns, NewInfo, Sol)
		; % the constraint can hold and can unhold
			% then we either (a) fail it or (b) succeed it and fail the rest
			(
				negate_finite_domain_constraint(C, NC), 
				propagate_finite_domain_constraints([NC], Cs, NewCs),
				solve_all(RestGs, As, NewCs, Ns, NewInfo, Sol)
			;
				propagate_finite_domain_constraints([C], Cs, NewCs),
				solve_one(-, fail(Vs, RestLits), RestGs, As, NewCs, Ns, NewInfo, Sol)
			)
		)
	).

fail_one(r, C, Vs, RestLits, RestGs, As, Cs, Ns, Info, Sol) :-
	inspect_fail_one((r, C), Vs, RestLits, RestGs, As, Cs, Ns, Info, NewInfo),
	negate_real_domain_constraint(C, NC),
	C = {Cons}, NC = {NCons},
	(entailed(NCons) -> 
		% the constraint can never hold anyway
		solve_all(RestGs, As, Cs, Ns, NewInfo, Sol)
	; entailed(Cons) ->
		% the constraint always hold
		solve_one(-, fail(Vs, RestLits), RestGs, As, Cs, Ns, NewInfo, Sol)
	; % we either (a) fail it, or (b) succeed it and fail the rest.
		(
			propagate_real_domain_constraints([NC], Cs, NewCs),
			solve_all(RestGs, As, NewCs, Ns, NewInfo, Sol)
		;
			propagate_real_domain_constraints([C], Cs, NewCs),
			solve_one(-, fail(Vs, RestLits), RestGs, As, NewCs, Ns, NewInfo, Sol)
		)
	).

% --- Auxiliary Predicates for the Meta-Interpreters ---

% initialise(Query, InitGs, Abducibles, Constraints, Denials, Info)
initialise(Query, InitGs, [], ([], [], []), InitNs, NewInfo) :-
	maplist(wrap_literal, Query, QueryW),
	collect_static_ics(FGs, InitNs),
	append(QueryW, FGs, InitGs),
	inspect_initial_state(Query, NewInfo).

collect_static_ics(FailureGoals, DynamicDenials) :-
	findall(IC, ic(IC), ICs),
	partition_ics(ICs, FailureGoals, DynamicDenials).

partition_ics([], [], []).
partition_ics([IC|Rest], AllFs, AllNs) :-
	partition_ics(Rest, Fs, Ns),
	term_variables(IC, Vs),
	(select((a, A), IC, RestBody) ->
		% contains an abducible, so move it to the front to form a dynamic denial
		AllNs = [fail(Vs, [(a,A)|RestBody])|Ns],
		AllFs = Fs
	;
		% otherwise, keep it as a failure goal
		AllFs = [(-, fail(Vs, IC))|Fs],
		AllNs = Ns
	).

resolve_abducible_with_delta([], _, []).
resolve_abducible_with_delta([H|T], A, [(A=/=H)|IEs]) :-
	unifiable(H, A), !,
	resolve_abducible_with_delta(T, A, IEs).
resolve_abducible_with_delta([_|T], A, IEs) :-
	resolve_abducible_with_delta(T, A, IEs).

resolve_abducible_with_dynamic_ics([], _, []).
resolve_abducible_with_dynamic_ics([fail(Vs, [(a, Left)|Rest])|RestNs], A, [F|Fs]) :-
	unifiable(Left, A), !,
	rename_universal_variables(Vs, Left-Rest, RnVs, RnLeft-RnRest),
	unifiable(RnLeft, A, Bindings),
	bind_universal_variables(Bindings, RnVs, RemainingBindings, RemainingRnVs),
	maplist(wrap_atom, RemainingBindings, Es),
	append(Es, RnRest, NewRest),
	F = (-, fail(RemainingRnVs, NewRest)),
	resolve_abducible_with_dynamic_ics(RestNs, A, Fs).
resolve_abducible_with_dynamic_ics([_|RestNs], A, Fs) :-
	resolve_abducible_with_dynamic_ics(RestNs, A, Fs).

bind_universal_variables([], Vs, [], Vs).
bind_universal_variables([(A=B)|T], Vs, NewEs, NewVs) :-
	(strictmember(Vs, A) ->
		% A is universally quantified, so bind it
		strictdelete(Vs, A, Vs1),
		call(A=B),
		bind_universal_variables(T, Vs1, NewEs, NewVs)
	;
		% A is not universally quantified, so keep the equality
		bind_universal_variables(T, Vs, Es1, NewVs),
		NewEs = [(A=B)|Es1]
	).

% rename all the universally quantified variables in a given term.
% HACK: the term_variables/2 in YAP and that in SICStus behave
% differently.  Therefore, the implementation of "rename_universal_variables" 
% can't rely on them any more.  Below is a new implementation that should work
% on both systems

:- dynamic mycopy/1.
rename_universal_variables(VsIn, FormIn, VsOut, FormOut) :-
	assert(mycopy(VsIn-FormIn)), retract(mycopy(VsOut-FormOut)),
	rebind_existential_variables(FormIn, VsIn, FormOut).
rebind_existential_variables(Pin, VsIn, Pout) :-
	(atomic(Pin) ->
		true % nothing to bind
	; var(Pin) ->
		(strictmember(VsIn, Pin) ->
			% this is a universally quantified variable. so do not bind it
			true
		;
			% this is an existentially quantified variable, so BIND it.
			Pout = Pin
		)
	; % this is a compound term
		Pin =.. [F|ArgsIn],
		Pout =.. [F|ArgsOut],
		rebind_existential_variables_recursively(ArgsIn, VsIn, ArgsOut)
	).
rebind_existential_variables_recursively([], _, []).
rebind_existential_variables_recursively([H1|T1], VsIn, [H2|T2]) :-
	rebind_existential_variables(H1, VsIn, H2),
	rebind_existential_variables_recursively(T1, VsIn, T2).

safe_select_failure_literal(Lits, Vs, (Type, L), RestLits) :-
	select((Type, L), Lits, RestLits), 
	safe_failure_literal(Type, L, Vs), !.

% 11/07/2011 Bug fixed: floundering case
backup_safe_select_failure_literal(Lits, Vs, (f, X in Dom), RestLits) :- 
	select((f, X in Dom), Lits, RestLits),
	strictmember(Vs, X),
	ground(Dom).

special_domain_condition(X in Dom, Vs) :-
	strictmember(Vs, X),
	ground(Dom).

% 17/09/2010 Bug fixed: thanks Domenico Corapi
partition_failure_literals([], [], []).
partition_failure_literals([(f,C)|T], [C|FCs], RCs) :-
	partition_failure_literals(T, FCs, RCs).
partition_failure_literals([(r,C)|T], FCs, [C|RCs]) :-
	partition_failure_literals(T, FCs, RCs).

safe_failure_literal(n, L, Vs) :-
	% negative literal must not contain universally quantified 
	% variables
	variables_within_term(Vs, L, []).
safe_failure_literal(i, L, Vs) :-
	% simliary inequality must not involve universally quantified
	% variables
	variables_within_term(Vs, L, []).
safe_failure_literal(f, L, Vs) :-
	% finite domain constraint with universally quantified variables
	% should not be selected at first
	variables_within_term(Vs, L, []).
safe_failure_literal(r, L, Vs) :-
	% similarly real domain constraint with universally quantified 
	% variables should not be selected at first
	variables_within_term(Vs, L, []).
safe_failure_literal(e, X = Y, Vs) :-
	% for equalitiy it is a bit trickier
	% FIXME (low priority): at the moment, the equality store does
	% not handle inequalities with universally quantified variables.
	% Thus, equalities between one existentially quantified variable
	% and a compound term with universally quantified variables should
	% not be selected.
	\+ (
		% the following means "X is an existentially quantified variable
		% but Y is a compound term with universally quantified variables"
		var(X), \+ strictmember(Vs, X),
		\+ var(Y), \+ variables_within_term(Vs, Y, [])
	), 
	\+ (
		% the following means "Y is an existentially quantified variable
		% but X is a compound term with universally quantified variables"
		var(Y), \+ strictmember(Vs, Y),
		\+ var(X), \+ variables_within_term(Vs, X, [])
	).
% finally, everything else is safe.
safe_failure_literal(a, _, _).
safe_failure_literal(b, _, _).
safe_failure_literal(d, _, _).

resolve_failure_abducible_with_delta([], _, _, _, []).
resolve_failure_abducible_with_delta([H|T], A, Vs, RestLits, [FailureGoal|FailureGoals]) :-
	unifiable(H, A), !,
	rename_universal_variables(Vs, A-RestLits, RnVs, RnA-RnRestLits),
	unifiable(RnA, H, Es),
	bind_universal_variables(Es, RnVs, RemainingEs, RemainingRnVs),
	maplist(wrap_atom, RemainingEs, EsW),
	append(EsW, RnRestLits, NewBody),
	FailureGoal = (-, fail(RemainingRnVs, NewBody)),
	resolve_failure_abducible_with_delta(T, A, Vs, RestLits, FailureGoals).
resolve_failure_abducible_with_delta([_|T], A, Vs, RestLits, FailureGoals) :-
	resolve_failure_abducible_with_delta(T, A, Vs, RestLits, FailureGoals).

resolve_failure_non_abducible_with_rules([], _, _, _, []).
resolve_failure_non_abducible_with_rules([H-B|T], P, Vs, RestLits, 
		[FailureGoal|FailureGoals]) :-
	rename_universal_variables(Vs, P-RestLits, RnVs, RnP-RnRestLits),
	term_variables(H-B, NewVs),
	append(NewVs, RnVs, AllVs), % no need to use union/3 here as "NewVs" must be fressh
	unifiable(H, RnP, Es),
	bind_universal_variables(Es, AllVs, RemainingEs, RemainingVs),
	maplist(wrap_atom, RemainingEs, EsW),
	append(EsW, B, NewB), append(NewB, RnRestLits, AllBody),
	FailureGoal = (-, fail(RemainingVs, AllBody)),
	resolve_failure_non_abducible_with_rules(T, P, Vs, RestLits, FailureGoals).

% --- Utilities for Inequality and Constraint stores ---

enforce_labeling(true) :-
	set_value(lbl, true).
enforce_labeling(false) :-
	set_value(lbl, false).

finite_domain_inequality(X=/=Y) :-
	fd_var(X) ; fd_var(Y) ; % already be fd var
	(var(X), integer(Y)) ; (var(Y), integer(X)). % about to become fd var

:- if(current_prolog_flag(dialect, yap)).
%{
fd_entailment(C, B) :-
	call(C #<==> B).

real_domain_inequality(X=/=Y) :-
	get_attr(X, itf, _) ; get_attr(Y, itf, _) ; % already be rd var
	(var(X), float(Y)) ; (var(Y), float(X)). % about to become rd var

fd_label(Vs) :-
	label(Vs).
%}
:- elif(current_prolog_flag(dialect, sicstus)).
%{
fd_entailment(C, B) :-
	call(C #<=> B).

real_domain_inequality(X=/=Y) :-
	% get_atts(X, itf) ; get_atts(Y, itf) ; % already be rd var % FIXME: can't get it working
	(var(X), float(Y)) ; (var(Y), float(X)). % about to become rd var

fd_label(Vs) :-
	labeling([], Vs).
%}
:- endif.

fd_label_once(Vs) :-
	fd_label(Vs), !.

propagate_inequalities(Es, (E, F, R), (NewE, NewF, NewR)) :-
	add_inequalities(Es, (E, F, R), (NewE, NewF, NewR)).

add_inequalities([], Cs, Cs).
add_inequalities([(X=/=Y)|T], (Ei, Fi, Ri), (Eo, Fo, Ro)) :-
	(finite_domain_inequality(X=/=Y) ->
		% push it to the finite domain constraint store
		fd_entailment((X #\= Y), B),
		(B == 1 ->
			% already reitified, so can discard it
			add_inequalities(T, (Ei, Fi, Ri), (Eo, Fo, Ro))
		; % otherwise, try to add it to the finite domain constraint store
			call(X #\= Y),
			add_inequalities(T, (Ei, [(X #\= Y)|Fi], Ri), (Eo, Fo, Ro))
		)
	; real_domain_inequality(X=/=Y) ->
		% push it to the real domain constraint store
		(entailed(X =\= Y) ->
			% already entailed, so can discard it
			add_inequalities(T, (Ei, Fi, Ri), (Eo, Fo, Ro))
		; % otherwise, try to add it to the real domain constraint store
			call({X =\= Y}),
			add_inequalities(T, (Ei, Fi, [{X =\= Y}|Ri]), (Eo, Fo, Ro))
		)
	; % a real inequality?
		(unifiable(X, Y) ->
			% still need to keep it as the inequality could be falsified
			call(X=/=Y),
			add_inequalities(T, ([(X=/=Y)|Ei], Fi, Ri), (Eo, Fo, Ro))
		;
			add_inequalities(T, (Ei, Fi, Ri), (Eo, Fo, Ro))
		)
	).

propagate_finite_domain_constraints(Fs, (E,F,R), (E,NewF,R)) :-
	add_finite_domain_constraints(Fs, F, NewF),
	finite_domain_soundness_check(NewF).

add_finite_domain_constraints([], F, F).
add_finite_domain_constraints([H|T], Fin, Fout) :-
	fd_entailment(H, B),
	(B == 1 ->
		% can discard it
		add_finite_domain_constraints(T, Fin, Fout)
	;
		call(H),
		add_finite_domain_constraints(T, [H|Fin], Fout)
	).

propagate_real_domain_constraints(Rs, (E,F,R), (E,F,NewR)) :-
	add_real_domain_constraints(Rs, R, NewR).

add_real_domain_constraints([], R, R).
add_real_domain_constraints([H|T], Rin, Rout) :-
	H = {C},
	(entailed(C) ->
		% can discard it
		add_real_domain_constraints(T, Rin, Rout)
	;
		call(H),
		add_real_domain_constraints(T, [H|Rin], Rout)
	).

negate_finite_domain_constraint(C1 #\/ C2, NC1 #/\ NC2) :-
	negate_finite_domain_constraint(C1, NC1),
	negate_finite_domain_constraint(C2, NC2).
negate_finite_domain_constraint(C1 #/\ C2, NC1 #\/ NC2) :-
	negate_finite_domain_constraint(C1, NC1),
	negate_finite_domain_constraint(C2, NC2).
negate_finite_domain_constraint(#\ C, C).
negate_finite_domain_constraint(X #< Y, X #>= Y).
negate_finite_domain_constraint(X #> Y, X #=< Y).
negate_finite_domain_constraint(X #=< Y, X #> Y).
negate_finite_domain_constraint(X #>= Y, X #< Y).
negate_finite_domain_constraint(X #\= Y, X #= Y).

negate_real_domain_constraint({C1 , C2}, {NC1 ; NC2}) :-
	negate_real_domain_constraint({C1}, {NC1}),
	negate_real_domain_constraint({C2}, {NC2}).
negate_real_domain_constraint({C1 ; C2}, {NC1 , NC2}) :-
	negate_real_domain_constraint({C1}, {NC1}),
	negate_real_domain_constraint({C2}, {NC2}).
negate_real_domain_constraint({X < Y}, {X >= Y}).
negate_real_domain_constraint({X > Y}, {X =< Y}).
negate_real_domain_constraint({X =< Y}, {X > Y}).
negate_real_domain_constraint({X >= Y}, {X < Y}).
negate_real_domain_constraint({X =\= Y}, {X = Y}).
negate_real_domain_constraint({X = Y}, {X =\= Y}).
negate_real_domain_constraint({X =:= Y}, {X =\= Y}).

domain_bounded(X) :- fd_size(X, S), S \== sup. 

finite_domain_soundness_check(F) :-
	term_variables(F, Vs),
	selectlist(domain_bounded, Vs, BVs),
	(get_value(lbl, true) ->
		fd_label(BVs)
	;
		\+ \+ fd_label(BVs)
	).

extract_constraints((Es, Fs, Rs), Cs) :-
	% finite domain constraints soundness check
	finite_domain_soundness_check(Fs),
	% collect inequalities
	term_variables(Es, EsVs),
	maplist(inequalities, EsVs, Ess),
	flatten_lists(Ess, Es1),
	list_to_ord_set(Es1, Es2),
	% collect ground finite domain constraints
	selectlist(nonground, Fs, Fs1),
	% collect real domain constraints
	term_variables(Rs, RsVs),
	dump(RsVs, RsVs, Rs1),
	append(Fs1, Rs1, Cs1),
	append(Es2, Cs1, Cs).

flatten_lists([], []).
flatten_lists([H|T], L) :-
        flatten_lists(T, L1),
        append(H, L1, L).

% --- Inequality Store ---

% public
X =/= Y :-
	(var(X) ; var(Y)), !,
	X \== Y, 
	reinforce_neq(X, Y),
	reinforce_neq(Y, X).
X =/= Y :-
	(unifiable(X, Y, Eqs) ->
		(Eqs = [A = B] ->
			A =/= B % no choice point
		;
			member(A = B, Eqs), % backtrackable
			A =/= B
		)
	;
		true
	).

reinforce_neq(A, B) :-
	var(A), !,
	(get_atts(A, aliens(S)) ->
		(\+ strictmember(S, B) -> NewS = [B|S] ; NewS = S),
		put_atts(A, aliens(NewS))
	;
		put_atts(A, aliens([B]))
	).
reinforce_neq(_, _).

strictmember([H|T], X) :-
	(X == H ->
		true
	;
		strictmember(T, X)
	).

% hook
verify_attributes(Var, Val, Goals) :-
	get_atts(Var, aliens(S1)), !, % are we involved?
	\+ strictmember(S1, Val), % is it an alien?
	((var(Val), get_atts(Val, aliens(S2))) -> 
	% thanks Domenico Corapi for helping with fixing the bug, 2010/03/31
	%(var(Val) ->
		%get_atts(Val, aliens(S2)), 
		% \+ strictmember(S2, Var) % this should be implied by the previous test
		list_to_ord_set(S2, NewS2),
		list_to_ord_set(S1, NewS1),
		ord_union(NewS2, NewS1, S3), % copy forward aliens
		put_atts(Val, aliens(S3)),
		Goals = []
	;
		generate_goals(S1, Val, Goals)
	).
verify_attributes(_, _, []).

generate_goals([], _, []).
generate_goals([H|T], Val, Gs) :-
	generate_goals(T, Val, Gs1),
	(var(H) ->
		Gs = Gs1
	;
		Gs = [(Val =/= H)|Gs1]
	).

% hook
attribute_goal(Var, Goal) :-
	get_atts(Var, aliens(S)),
	list_to_ord_set(S, S1),
	construct_body(S1, Var, Goal).

construct_body([H|T], Var, Goal) :-
	(T = [] ->
		Goal = (Var =/= H)
	;
		construct_body(T, Var, G),
		Goal = ((Var =/= H),G)
	).

% public
inequalities(Var, Ineqs) :-
	get_atts(Var, aliens(S)), !,
	list_to_ord_set(S, S1),
	collect_inequalities(S1, Var, Ineqs).
inequalities(_, []).

collect_inequalities([], _, []).
collect_inequalities([H|T], Var, [N|Rest]) :-
	(Var @=< H ->
		N = (Var =/= H)
	;
		N = (H =/= Var)
	),
	collect_inequalities(T, Var, Rest).

% ------------------------------------------------------------------------
% ---------- Extensions (Experimental) ---------------
% EXP

:- use_module(library(timeout)).
:- use_module(library(system)).

% similar to eval/2 (see below) but with timeout
eval(Query, TimeOut, Delta) :-
	time_out(query_with_minimal_solutions(Query, MinSols), TimeOut, Result),
	(Result == success ->
		member((_Length, Query-Delta), MinSols)
	;
		write('TIMEOUT! Cannot compute all ground solutions and global minimality '),
		write('of explanations cannot be guaranteed.  Please use "query('),
		write(Query), write('), (Delta, Constraints, Denials))." instead.'), nl, fail
	).

% eval(Query, Delta) holds if and only if Delta is the minimal ground explanation 
% for Query.  Currently it only works if we can compute all the ground solutions 
% for the given query.
eval(Query, Delta) :-
	query_with_minimal_solutions(Query, MinSols),
	member((_Length, Query-Delta), MinSols).

query_with_minimal_solutions(Query, SortedSolutions) :-
	% 1. compute all the ground answers
	findall(Query-SortedAs, (
			query(Query, (As, Cs, _Ns)),
			term_variables(Cs, Vs),
			selectlist(domain_bounded, Vs, BVs),
			fd_label(BVs),
			list_to_ord_set(As, SortedAs)
		), Solutions),
	% 2. make sure everything is ground
	ground(Solutions),
	% 3. select the minimal ones
	select_minimal_solutions(Solutions, [], MinSolutions),
	% 4. sort it according to its length
	sort_solutions_according_to_length(MinSolutions, SortedSolutions).

eval_with_one_labelling(Query, Delta) :-
	query_with_minimal_solutions_with_one_labelling(Query, MinSols),
	member((_Length, Query-Delta), MinSols).

query_with_minimal_solutions_with_one_labelling(Query, SortedSolutions) :-
	% 1. compute all the ground answers
	findall(Query-SortedAs, (
			query(Query, (As, Cs, _Ns)),
			term_variables(Cs, Vs),
			selectlist(domain_bounded, Vs, BVs),
			fd_label_once(BVs),
			list_to_ord_set(As, SortedAs)
		), Solutions),
	% 2. make sure everything is ground
	ground(Solutions),
	% 3. select the minimal ones
	select_minimal_solutions(Solutions, [], MinSolutions),
	% 4. sort it according to its length
	sort_solutions_according_to_length(MinSolutions, SortedSolutions).

select_minimal_solutions([], MinSols, MinSols).
select_minimal_solutions([H|T], Sols, MinSols) :-
	((is_minimal(T, H), is_minimal(Sols, H)) ->
		NewSols = [H|Sols]
	;
		NewSols = Sols
	),
	select_minimal_solutions(T, NewSols, MinSols).

is_minimal([], _).
is_minimal([H|T], X) :- 
	\+ ground_subsumes(H, X),
	is_minimal(T, X).

ground_subsumes(Q-D1, Q-D2) :-
	ord_intersection(D1, D2, Inter),
	D1 = Inter.

sort_solutions_according_to_length(MinSols, SortedSols) :-
	maplist(attach_length, MinSols, Sols),
	sort(Sols, SortedSols).

attach_length(Q-D, (L, Q-D)) :-
	length(D, L).

% forcing the argument of P to be typed.
force_types(P) :-
	(\+ types(P, _) ->
		true
	;
		types(P, Conds),
		force_all_type_conditions(Conds)
	).

force_all_type_conditions([]).
force_all_type_conditions([C|T]) :-
	(C = (X = Y) ->
		call(C)
	; C = type(X, Y) ->
		enum(Y, D),
		member(X, D)
	),
	force_all_type_conditions(T).

% -- enhanced querying interface

eval_all(Query) :-
	nl,
	write('+++++++++++++++ Start +++++++++++++++++'), nl, nl,
	now(Time1),
	findall(Query-Delta, eval(Query, Delta), Ans),
	now(Time2),
	Diff is Time2 - Time1,
	length(Ans, Len),
	(ground(Query) ->
		write('Query: '), portray_clause(Query),
		forall(member(_-D, Ans), (
			write(' <= '), portray_clause(D)
		))
	;
		forall(member(Q-D, Ans), (
			write('Query: '), portray_clause(Q),
			write(' <= '), portray_clause(D)
		))
	),
	nl,
	write('Total execution time (seconds): '), write(Diff), nl,
	write('Total minimal explanations found: '), write(Len), nl, nl,
	write('---------------  End  -----------------'), nl,
	nl.

eval_all(Query, GroundQueryHypothesesPairs) :-
	findall((Query, Delta), eval(Query, Delta), GroundQueryHypothesesPairs).

eval_all_with_ground_query(Query, AllGroundHypotheses) :-
	ground(Query),
	findall(Delta, eval(Query, Delta), AllGroundHypotheses).

query_all(Query) :-
	nl,
	write('+++++++++++++++ Start +++++++++++++++++'), nl,
	write('Original Query: '), write(Query), nl, nl,
	now(Time1),
	findall(Query-Delta, query(Query, (Delta,_,_)), Ans),
	now(Time2),
	Diff is Time2 - Time1,
	length(Ans, Len),
	(ground(Query) ->
		write('Query: '), portray_clause(Query),
		forall(member(_-D, Ans), (
			write(' <= '), portray_clause(D)
		))
	;
		forall(member(Q-D, Ans), (
			write('Query: '), portray_clause(Q),
			write(' <= '), portray_clause(D)
		))
	),
	nl,
	write('Total execution time (seconds): '), write(Diff), nl,
	write('Total explanations found: '), write(Len), nl, nl,
	write('---------------  End  -----------------'), nl,
	nl.

% -- state inspection --

:- set_value(depth_limit, 0).

set_depth_limit(N) :-
	N > 0,
	set_value(depth_limit, N).
clear_depth_limit :-
	set_value(depth_limit, 0).

:- set_value(max_states, 0). % by default, no limit
set_max_states(M) :-
	M >= 0,
	set_value(max_states, M).

query_all_with_trace(Query) :-
	query_all_with_trace(Query, 'trace.graphml').

query_all_with_trace(Query, TraceFile) :-
	set_value(dbg, true),
	initialise_trace(TraceFile),
	query_all(Query),
	finalise_trace,
	set_value(dbg, false).
	
eval_all_with_trace(Query) :-
	eval_all_with_trace(Query, 'trace.graphml').

eval_all_with_trace(Query, TraceFile) :-
	set_value(dbg, true),
	initialise_trace(TraceFile),
	eval_all(Query),
	finalise_trace,
	set_value(dbg, false).

reset_state_count :-
	set_value(state_count, 0).

increment_state_count :-
	get_value(max_states, MaxVal),
	(MaxVal == 0 ->
		true
	;
		inc_value(state_count, NewVal, _),
		NewVal < MaxVal
	).

inspect_solve_one(SelectedGoal, RestGoals, Abducibles, Constraints, Denials, Info, NewInfo) :-
	((get_value(depth_limit, DMax), DMax \== 0) ->
		Info = [Log, depth(D)],
		D =< DMax,
		NewD is D + 1,
		Info1 = [Log, depth(NewD)]
	;
		Info1 = Info
	),
	(get_value(dbg, true) ->
		increment_state_count,
		Info1 = [log([PID, OldComment]), Depth],
		inc_value(state_id, CID, _),
		trace_file(OutStream),
		open_node(OutStream, CID),
		dump_goals(OutStream, [SelectedGoal|RestGoals]),
		dump_abducibles(OutStream, Abducibles),
		dump_constraints(OutStream, Constraints),
		dump_denials(OutStream, Denials),
		close_node(OutStream),
		output_edge(OutStream, PID, CID, OldComment),
		SelectedGoal = (Type, _),
		goal_type(Type, TypeName),
		unwrap_literal(SelectedGoal, UwGoal),
		(UwGoal = fail(Vs, Body) ->
			NewComment = ['Select ', TypeName, ' goal: forall ', Vs, ' . fail ', Body]
		;
			NewComment = ['Select ', TypeName, ' goal: ', UwGoal]
		),		
		NewInfo = [log([CID, NewComment]), Depth]
	;
		NewInfo = Info1
	).

inspect_fail_one(SelectedLiteral, UniversalVariables, RestDenial, RestGoals, Abducibles, Constraints, Denials, Info, NewInfo) :-
	((get_value(depth_limit, DMax), DMax \== 0) ->
		Info = [Log, depth(D)],
		D =< DMax,
		NewD is D + 1,
		Info1 = [Log, depth(NewD)]
	;
		Info1 = Info
	),
	(get_value(dbg, true) ->
		increment_state_count,
		Info1 = [log([PID, OldComment]), Depth],
		inc_value(state_id, CID, _),
		trace_file(OutStream),
		open_node(OutStream, CID),
		dump_goals(OutStream, [(-, fail(UniversalVariables, [SelectedLiteral|RestDenial]))|RestGoals]),
		dump_abducibles(OutStream, Abducibles),
		dump_constraints(OutStream, Constraints),
		dump_denials(OutStream, Denials),
		close_node(OutStream),
		output_edge(OutStream, PID, CID, OldComment),
		SelectedLiteral = (Type, _),
		goal_type(Type, TypeName),
		unwrap_literal(SelectedLiteral, UwLit),
		maplist(unwrap_literal, RestDenial, UwRestDenial),
		NewComment = ['Select ', TypeName, ' literal ', UwLit, ' in denial goal: forall ', UniversalVariables, ' . fail ', [UwLit|UwRestDenial]],
		NewInfo = [log([CID, NewComment]), Depth]
	;
		NewInfo = Info1
	).

inspect_initial_state(Query, NewInfo) :-
	(get_value(dbg, true) ->
		reset_state_count,
		% 1. reset counter for generation of state ids
		set_value(state_id, 0),
		% 2. output new info
		NewLog = log([0, ['Start!']]),
		% 3 output state node
		trace_file(OutStream),
		open_node(OutStream, 0),
		writeln(OutStream, 'Query:'),
		writeln(OutStream, Query),
		close_node(OutStream)
	;
		NewLog = log([])
	),
	NewInfo = [NewLog, depth(0)].

inspect_successful_state(Abducibles, Constraints, Denials, Info) :-
	% ignore depth bound
	(get_value(dbg, true) ->
		Info = [log([PID, Comment]), _Depth],
		inc_value(state_id, CID, _),
		trace_file(OutStream),
		open_node(OutStream, CID),
		dump_abducibles(OutStream, Abducibles),
		dump_extracted_constraints(OutStream, Constraints),
		dump_unwrapped_denials(OutStream, Denials),
		close_node(OutStream),
		output_edge(OutStream, PID, CID, ['Succeeded :::: '|Comment])
	;
		true
	).

dump_goals(OutStream, Goals) :-
	maplist(unwrap_literal, Goals, Gs),
	maplist(replace_special_chars, Gs, Gs1),
	(Gs1 \= [] ->
		writeln(OutStream, 'Goals:'),
		forall(member(X, Gs1), (
			X = fail(Vs, Body) ->
				write(OutStream, '  forall '), write(OutStream, Vs), write(OutStream, ' . fail '),
				write(OutStream, Body), nl(OutStream)
			;
				write(OutStream, '  '), write(OutStream, X), nl(OutStream)
		))
	;
		true
	).

dump_abducibles(OutStream, Abducibles) :-
	maplist(replace_special_chars, Abducibles, As),
	(As \= [] ->
		writeln(OutStream, 'Abducibles:'),
		forall(member(X, As), (
			write(OutStream, '  '), write(OutStream, X), nl(OutStream)
		))
	;
		true
	).

dump_extracted_constraints(OutStream, Constraints) :-
	maplist(replace_special_chars, Constraints, Cs),
	(Cs \= [] ->
		writeln(OutStream, 'Constraints:'),
		forall(member(X, Cs), (
			write(OutStream, '  '), write(OutStream, X), nl(OutStream)
		))
	;
		true
	).

dump_constraints(OutStream, (Es, Fs, Rs)) :-
	append(Fs, Rs, Cons1),
	selectlist(nonground, Cons1, Cons2),
	term_variables(Es, EsVs),
	maplist(inequalities, EsVs, Ess),
	flatten_lists(Ess, Es1),
	list_to_ord_set(Es1, Es2),
	append(Es2, Cons2, Constraints),
	maplist(replace_special_chars, Constraints, Cs),
	(Cs \= [] ->
		writeln(OutStream, 'Constraints:'),
		forall(member(X, Cs), (
			write(OutStream, '  '), write(OutStream, X), nl(OutStream)
		))
	;
		true
	).

dump_denials(OutStream, Denials) :-
	maplist(unwrap_denial, Denials, Ns),
	dump_unwrapped_denials(OutStream, Ns).

dump_unwrapped_denials(OutStream, Denials) :-
	maplist(replace_special_chars, Denials, Ns1),
	(Ns1 \= [] ->
		writeln(OutStream, 'Denials:'),
		forall(member(fail(Vs, Body), Ns1), (
			write(OutStream, '  forall '), write(OutStream, Vs), write(OutStream, ' . fail '), 
			write(OutStream, Body), nl(OutStream)
		))
	;
		true
	).

open_node(OutStream, StateID) :-
	ttwrite(OutStream, '<node id="n'), write(OutStream, StateID), write(OutStream, '">'), nl(OutStream),
  tttwriteln(OutStream, '<data key="d6">'),
	ttttwriteln(OutStream, '<y:GenericNode configuration="ShinyPlateNode3">'),
	tttttwriteln(OutStream, '<y:Fill color="#FF9900" transparent="false"/>'),
	tttttwriteln(OutStream, '<y:BorderStyle hasColor="false" type="line" width="1.0"/>'),
	tttttwriteln(OutStream, '<y:NodeLabel alignment="left" autoSizePolicy="content" fontFamily="Dialog" fontSize="2" fontStyle="plain" hasBackgroundColor="false" hasLineColor="false" modelName="internal" modelPosition="c" textColor="#000000" visible="true">').
	
close_node(OutStream) :-
	tttttwriteln(OutStream, '</y:NodeLabel>'),
	ttttwriteln(OutStream, '</y:GenericNode>'),
	tttwriteln(OutStream, '</data>'),
	ttwriteln(OutStream, '</node>').

output_edge(OutStream, ParentID, ChildID, Comment) :-
	ttwrite(OutStream, '<edge id="e'), write(OutStream, ChildID), write(OutStream, '" source="n'), write(OutStream, ParentID), write(OutStream, '" target="n'), write(OutStream, ChildID), write(OutStream, '">'), nl(OutStream),
	tttwriteln(OutStream, '<data key="d9">'),
	ttttwriteln(OutStream, '<y:PolyLineEdge>'),
	tttttwriteln(OutStream, '<y:Path sx="0.0" sy="0.0" tx="0.0" ty="0.0"/>'),
	tttttwriteln(OutStream, '<y:LineStyle color="#000000" type="line" width="1.0"/>'),
	tttttwriteln(OutStream, '<y:Arrows source="none" target="standard"/>'),
	tttttwriteln(OutStream, '<y:EdgeLabel alignment="center" distance="2.0" fontFamily="Dialog" fontSize="2" fontStyle="plain" hasBackgroundColor="false" hasLineColor="false" modelName="six_pos" modelPosition="tail" preferredPlacement="anywhere" ratio="0.5" textColor="#000000" visible="true">'),
	forall(member(C, Comment), (
		write(OutStream, C)
	)), nl(OutStream),
	tttttwriteln(OutStream, '</y:EdgeLabel>'),
	tttttwriteln(OutStream, '<y:BendStyle smoothed="false"/>'),
	ttttwriteln(OutStream, '</y:PolyLineEdge>'),
	tttwriteln(OutStream, '</data>'),
	ttwriteln(OutStream, '</edge>').

initialise_trace(TraceFile) :-
	% open stream to write to TraceFile
	open(TraceFile, write, OutStream),
	retractall(trace_file(_)),
	assertz(trace_file(OutStream)),
	% generate header
	writeln(OutStream, '<?xml version="1.0" encoding="UTF-8" standalone="no"?>'),
	writeln(OutStream, '<graphml xmlns="http://graphml.graphdrawing.org/xmlns"'),
	twriteln(OutStream, 'xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:y="http://www.yworks.com/xml/graphml"'),
	twriteln(OutStream, 'xmlns:yed="http://www.yworks.com/xml/yed/3"'),
	twriteln(OutStream, 'xsi:schemaLocation="http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd">'),
	twriteln(OutStream, '<key for="graphml" id="d0" yfiles.type="resources" />'),
	twriteln(OutStream, '<key for="port" id="d1" yfiles.type="portgraphics" />'),
	twriteln(OutStream, '<key for="port" id="d2" yfiles.type="portgeometry" />'),
	twriteln(OutStream, '<key for="port" id="d3" yfiles.type="portuserdata" />'),
	twriteln(OutStream, '<key attr.name="url" attr.type="string" for="node" id="d4" />'),
	twriteln(OutStream, '<key attr.name="description" attr.type="string" for="node" id="d5" />'),
	twriteln(OutStream, '<key for="node" id="d6" yfiles.type="nodegraphics" />'),
	twriteln(OutStream, '<key attr.name="url" attr.type="string" for="edge" id="d7" />'),
	twriteln(OutStream, '<key attr.name="description" attr.type="string" for="edge" id="d8" />'),
	twriteln(OutStream, '<key for="edge" id="d9" yfiles.type="edgegraphics" />'),
	twriteln(OutStream, '<graph edgedefault="directed" id="G">').

finalise_trace :-
	retract(trace_file(OutStream)),
	% generate footer
	twriteln(OutStream, '</graph>'),
	twriteln(OutStream, '<data key="d0">'),
	ttwriteln(OutStream, '<y:Resources />'),
	twriteln(OutStream, '</data>'),
	writeln(OutStream, '</graphml>'),
	% close stream
	flush_output(OutStream),
	close(OutStream).

twrite(S, X) :- write(S, '\t'), write(S, X).
ttwrite(S, X) :- write(S, '\t\t'), write(S, X).
tttwrite(S, X) :- write(S, '\t\t\t'), write(S, X).

writeln(S, X) :- write(S, X), nl(S).
twriteln(S,X) :- write(S, '\t'), write(S,X), nl(S).
ttwriteln(S,X) :- write(S, '\t\t'), write(S,X), nl(S).
tttwriteln(S,X) :- write(S, '\t\t\t'), write(S,X), nl(S).
ttttwriteln(S,X) :- write(S, '\t\t\t\t'), write(S,X), nl(S).
tttttwriteln(S,X) :- write(S, '\t\t\t\t\t'), write(S,X), nl(S).
ttttttwriteln(S,X) :- write(S, '\t\t\t\t\t\t'), write(S,X), nl(S).

writelist(_, []) :- !.
writelist(S, [H|T]) :-
	write(S, H), writelist(S, T).

% --- for yEd ---
replace_special_chars(X, X) :-
	var(X), !.
replace_special_chars(X, Y) :-
	atomic(X), !,
	replace_special_atom(X, Y).
replace_special_chars(X, Y) :-
	% compound(X),
	X =.. [F|Args],
	replace_special_chars(F, F1),
	replace_special_chars_for_all(Args, Args1),
	Y =.. [F1|Args1].

replace_special_chars_for_all([], []).
replace_special_chars_for_all([H|T], [H1|T1]) :-
	replace_special_chars(H, H1),
	replace_special_chars_for_all(T, T1).

replace_special_atom(<, '&lt;') :- !.
replace_special_atom(=<, '=&lt;') :- !.
replace_special_atom(>, '&gt;') :- !.
replace_special_atom(>=, '&gt;=') :- !.
replace_special_atom(#<, '#&lt;') :- !.
replace_special_atom(#>, '#&gt;') :- !.
replace_special_atom(#=<, '#=&lt;') :- !.
replace_special_atom(#>=, '#&gt;=') :- !.
replace_special_atom(#<=>, '#&lt;=&gt;') :- !.
replace_special_atom(#<==>, '#&lt;==&gt;') :- !.
% replace_special_atom(\+, '\+') :- !.
% replace_special_atom(#\, '#\') :- !.
% replace_special_atom(#\=, '#\=') :- !.
% replace_special_atom(=\=, '=\=') :- !.
% replace_special_atom(#/\, '#/\') :- !.
% replace_special_atom(#\/, '#\/') :- !.
replace_special_atom(X, X).

goal_type(a, abducible).
goal_type(b, builtin).
goal_type(d, 'non-abducible').
goal_type(e, equality).
goal_type(i, inequality).
goal_type(n, negative).
goal_type(f, 'finite domain constraint').
goal_type(r, 'real domain constraint').
goal_type(-, 'denial').
