

:- module(baseKB).
:- use_module(library(pfc)).
:- set_fileAssertMt(baseKB).

:- begin_pfc.
% :- mpred_trace_exec.

notice_fc(P) ==>  ( P ==> {wdmsg(notice_fc(P))}).


notice_fc(a(1)).
notice_fc(b(2)).
notice_fc(c(3)).

c(3)==>a(1).
a(1)==>c(3).
c(3)==>c(3).

b(2).
% c(3) ==> {cls,C=c(3),wdmsg(ttExpressionTypeB1(C)),dumpST,wdmsg(ttExpressionTypeC1(C)),break}.
b(2)==>c(3).

% :- break.

