:- module(mpred_gvars, []).

:- use_module(library(must_trace)).
:- use_module(library(dictoo_declarations)).
:- use_module(library(dictoo)).



$current_file.value = X :- prolog_load_context(file,X).

/*
:- listing(dot_cfg:dictoo_decl).
:- (debug(gvar(_)),debug(dictoo(_)),debug(mpred(_))).
:- rtrace((dot_eval($current_file, value, Out),writeln(Out))).
:- (nodebug(gvar(_)),nodebug(dictoo(_)),nodebug(mpred(_))).
*/

%:- rtrace.
:- writeln($current_file.value).
%:- nortrace.

%:- break.
:- fixup_exports.
