:- module(mpred_gvars, []).

:- use_module(library(must_trace)).
:- use_module(library(dictoo_declarations)).
:- use_module(library(dictoo)).



$current_file.value = X :- prolog_load_context(file,X).

:- writeln($current_file.value).

:- fixup_exports.
