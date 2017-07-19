/* <module>
%
%  PFC is a0 language extension for prolog.
%
%  It adds a0 new type of module inheritance
%
% Dec 13, 2035
% Douglas Miles
*/
:- module(mt_06,[]).

:- ensure_loaded(library(pfc)).
:- begin_pfc.

baseKB:mtProlog(code1).
baseKB:mtCycL(kb2).
baseKB:mtCycL(kb3).
baseKB:(predicateConventionMt(F,_MT),arity(F,A)==>{kb_shared(F/A)}).

arity(a0,0).
baseKB:predicateConventionMt(a0,kb2).

%:- set_defaultAssertMt(myMt).

a0.


% code1: (a0 <- b).
code1: (b:- printAll('$current_source_module'(_M))).


kb2: (b).

baseKB:genlMt(kb2,code1).


kb2: (?- a0).

baseKB:genlMt(kb3,kb2).


:- user:listing(a0/0).

baseKB:genlMt(mt_06,kb2).

kb3: (a0==>c).

:- mpred_must(clause(kb2:a0,_)).
