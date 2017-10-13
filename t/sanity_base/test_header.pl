
:- if(current_prolog_flag(test_header,_)).

:- wdmsg(reload_of_test_header).

:- mpred_reset.

:- else.


% runtype: default = pfc
:- if(current_prolog_flag(runtime_testing_module,_)->true;
  set_prolog_flag(runtime_testing_module,test_header)).
:- endif.

:- if(( \+ current_prolog_flag(test_header,_),set_prolog_flag(test_header,loaded))).


:- if((prolog_load_context(module,user), \+ current_module(pfc_lib))).
:- module(header_sane,[test_header_include/0]).
test_header_include.
:- endif.


%:- set_prolog_flag(runtime_speed,0). % 0 = dont care
:- set_prolog_flag(runtime_speed, 0). % 1 = default
:- set_prolog_flag(runtime_debug, 3). % 2 = important but dont sacrifice other features for it
:- set_prolog_flag(runtime_safety, 3).  % 3 = very important
:- set_prolog_flag(unsafe_speedups, false).
:- set_prolog_flag(logicmoo_message_hook,dumpst).

:- endif.

setup_hist0:-  '$toplevel':setup_history.
:- setup_hist0.



:- if(( \+ current_module(pfc_lib) )).
:- use_module(library(pfc)).
:- prolog_load_context(source,File),(atom_contains(File,'.pfc')-> sanity(is_pfc_file) ; must_not_be_pfc_file).
:- endif.

:- ensure_loaded(library(pfc_test)).


:- endif. % current_prolog_flag(test_header,_).



:- if(is_pfc_file).

% :- mpred_trace_exec.

:- else.

:- mpred_trace_exec.

:- endif.


%:- set_prolog_flag(debug, true).
%:- set_prolog_flag(gc, false).

:- '$current_source_module'(W), '$set_typein_module'(W).
:- sanity((defaultAssertMt(Mt1),fileAssertMt(Mt2),source_module(Mt3))),sanity((Mt1==Mt2,Mt1==Mt3)).





