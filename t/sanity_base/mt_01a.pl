/* <module>
%
%  PFC is a language extension for prolog.
%
%  It adds a new type of module inheritance
%
% Dec 13, 2035
% Douglas Miles
*/

:- include(test_header).

:- header_sane:listing(mtCycL/1).

:- wdmsg(feature_test_may_fail).

%:- set_defaultAssertMt(header_sane).

mtCycL(socialMt).

:- must(baseKB:mtCycL(socialMt)).

:- header_sane:listing(mtCycL/1).


:- set_defaultAssertMt(myMt).

:- on_f_rtrace((on_x_rtrace(begin_pfc),is_pfc_file)).


:- ((ain(baseKB:predicateConventionMt(loves,socialMt)))).


% :- header_sane:listing(predicateConventionMt/2).

:- must((fix_mp(clause(_,_),loves(x,y),M,P),
   M:P==socialMt:loves(x,y))).

loves(sally,joe).

:- mpred_test(clause_u(socialMt:loves(_,_))).
:- mpred_test(\+clause_u(myMt:loves(_,_))).



