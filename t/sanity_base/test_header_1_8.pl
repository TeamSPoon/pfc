

:- if((prolog_load_context(module,user))).
:- module(header_sane,[test_header_include/0]).
test_header_include.
:- endif.

:- ensure_loaded(library(pfc_test)).
:- expects_dialect(pfc).

