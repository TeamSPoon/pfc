/* Part of LogicMOO Base Logicmoo Debug Tools
% ===================================================================
% File '$FILENAME.pl'
% Purpose: An Implementation in SWI-Prolog of certain debugging tools
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: '$FILENAME.pl' 1.0.0
% Revision: $Revision: 1.1 $
% Revised At:  $Date: 2002/07/11 21:57:28 $
% Licience: LGPL
% ===================================================================
*/

:- module(pfc_test,[why_was_true/1]).

pfc_must(\+ G):-!, ( \+ call(G) -> true ; (log_failure(failed_pfc_test(\+ G)),!,ignore(why_was_true(G)),!,break_ex)).
pfc_must(G):- (call(G) -> true ; (ignore(sanity(why_was_true(\+ G))),(log_failure(failed_pfc_test(G))),!,break_ex)).

break_ex:- quietly((log_failure_red,dumpST,log_failure_red)),
  (t_l:no_breaks -> ansifmt(red,"NO__________________DUMP_BREAK/0") ;dbreak).

maybe_pfc_break(Info):- (t_l:no_breaks->true;(debugging(logicmoo(pfc))->dtrace(dmsg_pretty(Info));(dmsg_pretty(Info)))),break_ex.
%maybe_pfc_break(Info):- (t_l:no_breaks->true;(debugging(logicmoo(pfc))->dtrace(dmsg_pretty(Info));(dmsg_pretty(Info)))),break_ex.


%% show_if_debug( :GoalA) is semidet.
%
% Show If Debug.
%
:- meta_predicate(show_if_debug(0)).
% show_if_debug(A):- !,show_call(why,A).
show_if_debug(A):- show_call(pfc_is_tracing,call_u(A)).


:- thread_local(t_l:hide_pfc_trace_exec/0).

%% with_pfc_trace_exec( +P) is semidet.
%
% Using Trace exec.
%

% with_pfc_trace_exec(P):- locally_each(-t_l:hide_pfc_trace_exec,locally_each(t_l:pfc_debug_local, must_ex(show_if_debug(P)))).

%with_pfc_trace_exec(P):- call(pfc_is_tracing_exec),!,show_if_debug(P).
with_pfc_trace_exec(P):-
   locally_each(-t_l:hide_pfc_trace_exec,
       locally_each(t_l:pfc_debug_local,
           must_ex(show_if_debug(P)))).


%% with_pfc_trace_exec( +P) is semidet.
%
% Without Trace exec.
%
with_no_pfc_trace_exec(P):-
 with_no_dmsg((
   locally_each(-t_l:pfc_debug_local,locally_each(t_l:hide_pfc_trace_exec, must_ex(/*show_if_debug*/(P)))))).

call_u(G):-call(G).
must_ex(X):-must(X).
quietly_ex(G):- !,G,!.
quietly_ex(G):- quietly(G).
trace_or_throw_ex(G):- trace_or_throw(G).

log_failure(ALL):- quietly_ex((log_failure_red,maybe_pfc_break(ALL),log_failure_red)).

log_failure_red:- quietly(doall((
  show_current_source_location,
  between(1,3,_),
  ansifmt(red,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find log_failure_red in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
  ansifmt(yellow,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find log_failure_red in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n")))).


%:- use_module(library(must_trace)).

test_red_lined(Failed):- quietly((
  format('~N',[]),
  quietly((doall((between(1,3,_),
  ansifmt(red,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find ~q in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n",[Failed]),
  ansifmt(yellow,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find test_red_lined in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"))))))).

% pfc_test/1,pfc_test_fok/1, pfc_test(+),pfc_test_fok(+),

mpred_test(G):- pfc_test(G).
mpred_test_fok(G):- pfc_test_fok(G).
%% pfc_test(+P) is semidet.
%
% PFC Test.
%
pfc_test(G):-var(G),!,dmsg_pretty(var_pfc_test(G)),trace_or_throw(var_pfc_test(G)).
%pfc_test((G1;G2)):- !,call(G1);pfc_test(G2).
pfc_test(_):- quietly((compiling; current_prolog_flag(xref,true))),!.
%pfc_test(G):- quietly(pfc_is_silent),!, with_no_pfc_trace_exec(must(pfc_test_fok(G))),!.
pfc_test(G):- dmsg_pretty(:-pfc_test(G)),fail.
pfc_test(G):- current_prolog_flag(runtime_debug,D),D<1,!,with_no_pfc_trace_exec(must((G))),!.
pfc_test(G):- with_no_breaks(with_pfc_trace_exec(must(pfc_test_fok(G)))),!.
%pfc_test(G):- with_pfc_trace_exec(must(pfc_test_fok(G))),!.
:- if(false).
pfc_test(MPRED):- must(pfc_to_pfc(MPRED,PFC)),!,(show_call(umt(PFC))*->true;(pfc_call(PFC)*->pfc_why2(MPRED);test_red_lined(pfc_test(MPRED)),!,fail)).
pfc_why2(MPRED):- must(pfc_to_pfc(MPRED,PFC)),!,(show_call(pfc_why(PFC))*->true;(test_red_lined(pfc_why(MPRED)),!,fail)).
:- endif.

:- thread_local(t_l:no_breaks/0).
with_no_breaks(G):- locally_tl(no_breaks,G). 

pfc_why(G):- pfcWhy(G).
mpred_why(G):- pfcWhy(G).

why_was_true((A,B)):- !,pfc_why(A),pfc_why(B).
why_was_true(P):- predicate_property(P,dynamic),pfc_why(P),!.
why_was_true(P):- dmsg_pretty(justfied_true(P)),!.

pfc_test_fok(G):- source_file(_,_),!,pfc_test_fok0(G),!.
pfc_test_fok(G):- pfc_test_fok0(G),!.

pfc_test_fok0(\+ G):-!, ( \+ call(G) -> wdmsg_pretty(passed_pfc_test(\+ G)) ; (log_failure(failed_pfc_test(\+ G)),!,
  ignore(why_was_true(G)),!,fail)).
% pfc_test_fok(G):- (call(G) -> ignore(sanity(why_was_true(G))) ; (log_failure(failed_pfc_test(G))),!,fail).
pfc_test_fok0(G):- (call(G) *-> ignore(must(why_was_true(G))) ; (log_failure(failed_pfc_test(G))),!,fail).


                    
:- module_transparent(pfc_feature/1).
:- dynamic(pfc_feature/1).
:- export(pfc_feature/1).
pfc_feature(test_a_feature).

:- module_transparent(pfc_test_feature/2).
:- export(pfc_test_feature/2).

pfc_test_feature(Feature,Test):- pfc_feature(Feature)*-> pfc_test(Test) ; true.

:- system:import(pfc_feature/1).
:- system:export(pfc_feature/1).
:- system:import(pfc_test_feature/2).
:- system:export(pfc_test_feature/2).

:- system:import(pfc_feature/1).
:- system:export(pfc_feature/1).
:- baseKB:import(pfc_test_feature/2).
:- baseKB:export(pfc_test_feature/2).


warn_fail_TODO(G):- dmsg_pretty(:-warn_fail_TODO(G)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DUMPST ON WARNINGS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% none = dont act as installed
% ignore = ignore warnings but dumpst+break on errors
% dumpst = dumpst on warnings +break on errors
% break = break on warnings and errors
:- create_prolog_flag(logicmoo_message_hook,none,[keep(true),type(term)]).


skip_warning(informational).
skip_warning(information).
skip_warning(debug).

skip_warning(discontiguous).
skip_warning(query).
skip_warning(banner).
skip_warning(silent).
skip_warning(debug_no_topic).
skip_warning(break).
skip_warning(io_warning).
skip_warning(interrupt).
skip_warning(statistics).
% skip_warning(check).
skip_warning(compiler_warnings).
skip_warning(T):- \+ compound(T),!,fail.
skip_warning(_:T):- !, compound(T),functor(T,F,_),skip_warning(F).
skip_warning(T):-compound(T),functor(T,F,_),skip_warning(F).



inform_message_hook(T1,T2,_):- (skip_warning(T1);skip_warning(T2);(\+ thread_self_main)),!.
inform_message_hook(_,_,_):- \+ current_predicate(dumpST/0),!.
inform_message_hook(compiler_warnings(_,[always(true,var,_),always(false,integer,_),
   always(false,integer,_),always(true,var,_),always(false,integer,_),always(false,integer,_)]),warning,[]):- !.
inform_message_hook(import_private(_,_),_,_).
inform_message_hook(check(undefined(_, _)),_,_).
inform_message_hook(ignored_weak_import(header_sane,_),_,_).
inform_message_hook(error(existence_error(procedure,'$toplevel':_),_),error,_).
% inform_message_hook(_,warning,_).

inform_message_hook(T,Type,Warn):- atom(Type),
  memberchk(Type,[error,warning]),!,
  once((dmsg_pretty(message_hook_type(Type)),dmsg_pretty(message_hook(T,Type,Warn)),
  ignore((source_location(File,Line),dmsg_pretty(source_location(File,Line)))),
  assertz(system:test_results(File:Line/T,Type,Warn)),nop(dumpST),
  nop(dmsg_pretty(message_hook(File:Line:T,Type,Warn))))),   
  fail.
inform_message_hook(T,Type,Warn):-
  ignore(source_location(File,Line)),
  once((nl,dmsg_pretty(message_hook(T,Type,Warn)),nl,
  assertz(system:test_results(File:Line/T,Type,Warn)),
  dumpST,nl,dmsg_pretty(message_hook(File:Line:T,Type,Warn)),nl)),
  fail.

inform_message_hook(T,Type,Warn):- dmsg_pretty(message_hook(T,Type,Warn)),dumpST,dmsg_pretty(message_hook(T,Type,Warn)),!,fail.
inform_message_hook(_,error,_):- current_prolog_flag(runtime_debug, N),N>2,break.
inform_message_hook(_,warning,_):- current_prolog_flag(runtime_debug, N),N>2,break.


:- multifile prolog:message//1, user:message_hook/3.

:- dynamic(system:test_results/3).

system:test_repl:-  assertz(system:test_results(need_retake,warn,need_retake)).
system:test_completed:- listing(system:test_results/3),test_completed_exit_maybe(7).
system:test_retake:- listing(system:test_results/3),test_completed_exit_maybe(3).

test_completed_exit(N):- dmsg_pretty(test_completed_exit(N)),fail.
test_completed_exit(7):- halt(7).
test_completed_exit(4):- halt(4).
test_completed_exit(5):- halt(5).
test_completed_exit(N):- (debugging-> break ; true), halt(N).
test_completed_exit(N):- (debugging-> true ; halt(N)).

test_completed_exit_maybe(_):- system:test_results(_,error,_),test_completed_exit(9).
test_completed_exit_maybe(_):- system:test_results(_,warning,_),test_completed_exit(3).
test_completed_exit_maybe(_):- system:test_results(_,warn,_),test_completed_exit(3).
test_completed_exit_maybe(N):- test_completed_exit(N).


:- multifile prolog:message//1, user:message_hook/3.
% message_hook_handle(import_private(pfc_lib,_:_/_),warning,_):- source_location(_,_),!.
message_hook_handle(io_warning(_,'Illegal UTF-8 start'),warning,_):- source_location(_,_),!.
message_hook_handle(undefined_export(jpl, _), error, _):- source_location(_,_),!.
message_hook_handle(_, error, _):- source_location(File,4235),atom_concat(_,'/jpl.pl',File),!.
message_hook_handle(message_lines(_),error,['~w'-[_]]). 
message_hook_handle(error(resource_error(portray_nesting),_),
   error, ['Not enough resources: ~w'-[portray_nesting], nl,
      'In:', nl, '~|~t[~D]~6+ '-[9], '~q'-[_], nl, '~|~t[~D]~6+ '-[7], 
        _-[], nl, nl, 'Note: some frames are missing due to last-call optimization.'-[], nl, 
        'Re-run your program in debug mode (:- debug.) to get more detail.'-[]]).
message_hook_handle(T,Type,Warn):- 
  ((current_prolog_flag(runtime_debug, N),N>2) -> true ; source_location(_,_)),
  memberchk(Type,[error,warning]),once(inform_message_hook(T,Type,Warn)),fail.


:- fixup_exports.

user:message_hook(T,Type,Warn):- 
   Type \== silent,Type \== debug, Type \== informational,
   current_prolog_flag(logicmoo_message_hook,Was),Was\==none,
   once(message_hook_handle(T,Type,Warn)),!.


