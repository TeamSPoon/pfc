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

test_red_lined(Failed):- quietly((
  format('~N',[]),
  quietly_ex((doall((between(1,3,_),
  ansifmt(red,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find ~q in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n",[Failed]),
  ansifmt(yellow,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find test_red_lined in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"))))))).

% mpred_test/1,mpred_test_fok/1, mpred_test(+),mpred_test_fok(+),

%% mpred_test(+P) is semidet.
%
% PFC Test.
%
mpred_test(G):-var(G),!,dmsg(var_mpred_test(G)),trace_or_throw(var_mpred_test(G)).
%mpred_test((G1;G2)):- !,call_u(G1);mpred_test(G2).
mpred_test(_):- quietly_ex((compiling; current_prolog_flag(xref,true))),!.
mpred_test(G):- quietly_ex(mpred_is_silient),!, with_no_mpred_trace_exec(must(mpred_test_fok(G))),!.
mpred_test(G):- current_prolog_flag(runtime_debug,D),D<1,!,with_no_mpred_trace_exec(must((G))),!.
mpred_test(G):- with_no_breaks(with_mpred_trace_exec(must(mpred_test_fok(G)))),!.
:- if(false).
mpred_test(MPRED):- must(mpred_to_pfc(MPRED,PFC)),!,(show_call(umt(PFC))*->true;(pfc_call(PFC)*->mpred_why2(MPRED);test_red_lined(mpred_test(MPRED)),!,fail)).
mpred_why2(MPRED):- must(mpred_to_pfc(MPRED,PFC)),!,(show_call(pfcWhy(PFC))*->true;(test_red_lined(mpred_why(MPRED)),!,fail)).
:- endif.


why_was_true((A,B)):- !,mpred_why(A),mpred_why(B).
why_was_true(P):- mpred_why(P),!.
why_was_true(P):- dmsg(justfied_true(P)),!.

mpred_test_fok(G):- source_file(_,_),!,mpred_test_fok0(G),!.
mpred_test_fok(G):- mpred_test_fok0(G),!.

mpred_test_fok0(\+ G):-!, ( \+ call_u(G) -> wdmsg(passed_mpred_test(\+ G)) ; (log_failure(failed_mpred_test(\+ G)),!,ignore(why_was_true(G)),!,fail)).
% mpred_test_fok(G):- (call_u(G) -> ignore(sanity(why_was_true(G))) ; (log_failure(failed_mpred_test(G))),!,fail).
mpred_test_fok0(G):- (call_u(G) *-> ignore(must(why_was_true(G))) ; (log_failure(failed_mpred_test(G))),!,fail).


                    
:- module_transparent(pfc_feature/1).
:- dynamic(pfc_feature/1).
:- export(pfc_feature/1).
pfc_feature(test_a_feature).

:- module_transparent(pfc_test_feature/2).
:- export(pfc_test_feature/2).

pfc_test_feature(Feature,Test):- pfc_feature(Feature)*-> mpred_test(Test) ; true.

:- system:import(pfc_feature/1).
:- system:export(pfc_feature/1).
:- system:import(pfc_test_feature/2).
:- system:export(pfc_test_feature/2).

:- system:import(pfc_feature/1).
:- system:export(pfc_feature/1).
:- baseKB:import(pfc_test_feature/2).
:- baseKB:export(pfc_test_feature/2).


warn_fail_TODO(G):- dmsg(:-warn_fail_TODO(G)).



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
inform_message_hook(T,Type,Warn):-
  ignore(source_location(File,Line)),
  once((nl,dmsg(message_hook(T,Type,Warn)),nl,
  assertz(system:test_results(File:Line/T,Type,Warn)),dumpST,nl,dmsg(message_hook(File:Line:T,Type,Warn)),nl)),
  fail.

inform_message_hook(T,Type,Warn):- dmsg(message_hook(T,Type,Warn)),dumpST,dmsg(message_hook(T,Type,Warn)),!,fail.
inform_message_hook(_,error,_):- current_prolog_flag(runtime_debug, N),N>2,break.
inform_message_hook(_,warning,_):- current_prolog_flag(runtime_debug, N),N>2,break.


:- multifile prolog:message//1, user:message_hook/3.

:- dynamic(system:test_results/3).

system:test_repl:-  assertz(system:test_results(need_retake,warn,need_retake)).
system:test_completed:- listing(system:test_results/3),test_completed_exit_maybe(7).
system:test_retake:- listing(system:test_results/3),test_completed_exit_maybe(3).

test_completed_exit(N):- dmsg(test_completed_exit(N)),fail.
test_completed_exit(7):- halt(7).
test_completed_exit(4):- halt(4).
test_completed_exit(5):- halt(5).
test_completed_exit(N):- (debugging-> break ; true), halt(N).
test_completed_exit(N):- (debugging-> true ; halt(N)).

test_completed_exit_maybe(_):- system:test_results(_,error,_),test_completed_exit(9).
test_completed_exit_maybe(_):- system:test_results(_,warning,_),test_completed_exit(3).
test_completed_exit_maybe(_):- system:test_results(_,warn,_),test_completed_exit(3).
test_completed_exit_maybe(N):- test_completed_exit(N).

set_file_abox_module(User):- '$set_typein_module'(User), '$set_source_module'(User),
  set_fileAssertMt(User).

set_file_abox_module_wa(User):- set_file_abox_module(User),set_defaultAssertMt(User).

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

user:message_hook(T,Type,Warn):- current_prolog_flag(logicmoo_message_hook,Was),Was\==none,
   once(message_hook_handle(T,Type,Warn)).

user:message_hook(T,Type,Warn):-  Type \== silent,Type \== debug, Type \== informational,
  memberchk(Type,[error,warning]),
  once((dmsg(message_hook_type(Type)),dmsg(message_hook(T,Type,Warn)),
  ignore((source_location(File,Line),dmsg(source_location(File,Line)))),
  assertz(system:test_results(File:Line/T,Type,Warn)),nop(dumpST),
  nop(dmsg(message_hook(File:Line:T,Type,Warn))))),
   
  fail.

