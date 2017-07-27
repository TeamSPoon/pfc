#!/usr/bin/env swipl

% Tests Emulation of assertable attributed variables
:- include(test_header).

:- ensure_loaded(library(attvar_reader)).

:- pfc_test_feature(mt,must_not_be_pfc_file).

sk:attr_unify_hook(_,_).

:- debug_logicmoo(_).
:- nodebug_logicmoo(http(_)).
:- debug_logicmoo(logicmoo(_)).

% :- dynamic(sk_in/1).

:- read_attvars(true).
% :- set_prolog_flag(assert_attvars,true).

sk_in(avar([vn='Ex'],[sk='SKF-666'])).

:- listing(sk_in/1).

:- must((sk_in(Ex),get_attr(Ex,sk,What),What=='SKF-666')).

