

% runtype: default = pfc
:- if(current_prolog_flag(runtime_testing_module,_)->true;
  set_prolog_flag(runtime_testing_module,test_header)).
:- endif.

:- if(( \+ current_prolog_flag(test_header,_),set_prolog_flag(test_header,loaded))).

:- if(prolog_load_context(module,user)).
:- module(header_sane,[]).
:- endif.

pfc_test_feature(_,_).
:- if((pfc_test_feature(mt,X=1),X==1)).
:- endif.
:- dynamic(system:test_results/3).

:- multifile prolog:message//1, user:message_hook/3.
user:message_hook(T,Type,Warn):- memberchk(Type,[error,warnings]),
  assertz(system:test_results(T,Type,Warn)),dumpST,fail.

system:test_completed:- listing(system:test_results/3),test_completed_exit.

test_completed_exit(N):- halt(N).

test_completed_exit:- system:test_results(_,error,_),test_completed_exit(9).
test_completed_exit:- system:test_results(_,warning,_),test_completed_exit(3).
test_completed_exit:- system:test_results(_,warn,_),test_completed_exit(3).
test_completed_exit:- test_completed_exit(4).


:- use_module(library(pfc)).

:- endif.

:- prolog_load_context(module,W), '$set_typein_module'(W).
:- '$current_typein_module'(W), '$current_source_module'(W).
:- ensure_loaded(library(pfc)).

%:- set_prolog_flag(runtime_speed,0). % 0 = dont care
:- set_prolog_flag(runtime_speed, 0). % 1 = default
:- set_prolog_flag(runtime_debug, 3). % 2 = important but dont sacrifice other features for it
:- set_prolog_flag(runtime_safety, 3).  % 3 = very important
:- set_prolog_flag(unsafe_speedups, false).
% :- mpred_trace_exec.

% :- set_prolog_flag(gc, false).


:- if((pfc_test_feature(localMt,X=1),X==1)).
:- prolog_load_context(source,File),
   (atom_contains(File,'.pfc')-> sanity(is_pfc_file) ; must_not_be_pfc_file).

:- '$current_source_module'(W), (W\==user->'$set_typein_module'(W);true).

:- if(is_pfc_file).
:- '$current_source_module'(W),set_fileAssertMt(W).
%:- '$current_typein_module'(W),set_defaultAssertMt(W).
:- endif.

% :- set_prolog_flag(debug, true).

%:- set_prolog_flag(retry_undefined,true).
:- endif.
:- kb_shared(baseKB:rtArgsVerbatum/1).
%:- pfc_mod:import(rtArgsVerbatum/1).

