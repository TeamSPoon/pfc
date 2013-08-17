#!/usr/bin/env swipl

%  was_module(sanity_ks_two,[]).

:- include(test_header).

:- debug_logicmoo(_).
:- nodebug_logicmoo(http(_)).
:- debug_logicmoo(logicmoo(_)).
 % :- mpred_trace_exec.

:- dynamic(sk_out/1).
:- dynamic(sk_in/1).

rtArgsVerbatum(my_sk).

:- read_attvars(true).

% :- file_begin(pl).
my_sk(avar([vn='Ex',sk='SKF-666'])).

:- must((my_sk(Ex),get_attr(Ex,sk,What),What=='SKF-666')).


