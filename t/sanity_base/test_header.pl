
:- if(( \+ current_prolog_flag(test_header,_),set_prolog_flag(test_header,loaded))).

:- if(prolog_load_context(module,user)).
:- module(header_sane,[]).
:- endif.

:- '$current_typein_module'(W), (W\==user->'$set_typein_module'(W);true).

:- prolog_load_context(module,W), (W\==user->'$set_source_module'(W);true).

:- use_module(library(pfc)).

:- endif.

:- ensure_loaded(library(pfc)).

%:- set_prolog_flag(runtime_speed,0). % 0 = dont care
:- set_prolog_flag(runtime_speed, 0). % 1 = default
:- set_prolog_flag(runtime_debug, 3). % 2 = important but dont sacrifice other features for it
:- set_prolog_flag(runtime_safety, 3).  % 3 = very important
:- set_prolog_flag(unsafe_speedups, false).


