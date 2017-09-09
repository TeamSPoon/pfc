#!/usr/bin/env swipl
% 
% Dec 13, 2034
% Douglas Miles
%  cls ; kill -9 %1 ; swipl -g "ensure_loaded(pack(logicmoo_base/t/sanity_base/clause_fwd_01c.pfc'))."

:- include(test_header).
% :- set_prolog_flag(lm_pfc_lean,true).
% :- use_module(library(pfc)).

:- kb_local(aa/2).

( aa(N):- _B ) ==> early_aa_H(N). 
( aa(N):- B ) ==> early_aa_HB(N,B). 
( aa(N) ) ==> early_aa(N). 

aa(1):- writeln(1+1).
aa(2). 
aa(3):- true.
aa(N):- member(N,[4,5]).

( aa(N):- _B ) ==> late_aa_H(N). 
( aa(N):- B ) ==> late_aa_HB(N,B). 
( aa(N) ) ==> late_aa(N). 


:- mpred_test(early_aa(1)).
:- mpred_test(early_aa(2)).
:- mpred_test(early_aa(3)).
:- mpred_test(early_aa(4)).
:- mpred_test(early_aa(5)).

:- mpred_test(late_aa(1)).
:- mpred_test(late_aa(2)).
:- mpred_test(late_aa(3)).
:- mpred_test(late_aa(4)).
:- mpred_test(late_aa(5)).

:- mpred_test(late_aa_HB(A, member(A, [4, 5]))).
:- mpred_test(late_aa_HB(3, true)).
:- mpred_test(late_aa_HB(2, true)).
:- mpred_test(late_aa_HB(1, writeln(1+1))).


:- mpred_test(early_aa_HB(A, member(A, [4, 5]))).
:- warn_fail_TODO(early_aa_HB(3, true)).
:- warn_fail_TODO(early_aa_HB(2, true)).
:- mpred_test(early_aa_HB(1, writeln(1+1))).



:- warn_fail_TODO(late_aa_H(1)).
:- warn_fail_TODO(late_aa_H(2)).
:- warn_fail_TODO(late_aa_H(3)).
:- warn_fail_TODO(late_aa_H(_)).
:- mpred_test(clause_asserted(late_aa_H(_))).
:- warn_fail_TODO(\+ clause_asserted(late_aa_H(4))).
:- warn_fail_TODO(\+ clause_asserted(late_aa_H(5))).


:- warn_fail_TODO(early_aa_H(1)).
:- warn_fail_TODO(early_aa_H(2)).
:- warn_fail_TODO(early_aa_H(3)).
:- warn_fail_TODO(early_aa_H(_)).
:- mpred_test(clause_asserted(early_aa_H(_))).
:- warn_fail_TODO(\+ clause_asserted(early_aa_H(4))).
:- warn_fail_TODO(\+ clause_asserted(early_aa_H(5))).



:- listing([early_aa/1,late_aa/1]).

:- listing([early_aa_HB/2,late_aa_HB/2]).

:- listing([early_aa_H/1,late_aa_H/1]).


                     