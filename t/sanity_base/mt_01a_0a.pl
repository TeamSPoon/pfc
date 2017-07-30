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

:- pfc_test_feature(mt,must_not_be_pfc_file).

:- pfc_test_feature(mt,\+ is_pfc_file).

:- pfc_test_feature(mt,\+ mtHybrid(header_sane)).

:- listing(mtHybrid/1).

:- wdmsg(feature_test_may_fail).

%:- set_defaultAssertMt(header_sane).

baseKB:mtHybrid(socialMt).

:- must(baseKB:mtHybrid(socialMt)).

:- header_sane:listing(mtHybrid/1).


:- set_defaultAssertMt(myMt).
:- set_fileAssertMt(myMt).

:- on_f_rtrace((on_x_rtrace(begin_pfc),is_pfc_file)).

baseKB:arity(loves,2).

:- ((ain(baseKB:predicateConventionMt(loves,socialMt)))).

% :- socialMt:listing(loves/2).

% :- header_sane:listing(predicateConventionMt/2).

:- must((fix_mp(clause(_,_),loves(x,y),M,P),
   M:P==socialMt:loves(x,y))).

loves(sally,joe).

baseKB:genlMt(myMt,socialMt).

:- mpred_test(clause_u(socialMt:loves(_,_))).

:- set_prolog_flag(retry_undefined,true).

:- listing(pfc_test_feature/2).

:- trace,pfc_test_feature(localMt,myMt:loves(_,_)).

:- mpred_test(clause(myMt:loves(_,_),_B,_R)).

:- pfc_test_feature(mt,\+clause_u(myMt:loves(_,_))).

:- mpred_test(myMt:loves(_,_)).

:- mpred_test((ain(genlMt(tooLazyMt,socialMt)),clause(tooLazyMt:loves(_,_),_B,_R))).

:- mpred_test(clause(tooLazyMt:loves(_,_),_B,_R)).

:- pfc_test_feature(mt,\+clause_u(tooLazyMt:loves(_,_))).

:- mpred_test(tooLazyMt:loves(_,_)).


:- must((ain(baseKB:genlMt(tooLazyBaseMt,socialMt)),clause(tooLazyBaseMt:loves(_,_),_B,_R))).

:- mpred_test(clause(tooLazyBaseMt:loves(_,_),_B,_R)).

:- pfc_test_feature(mt,\+clause_u(tooLazyBaseMt:loves(_,_))).

:- mpred_test(tooLazyBaseMt:loves(_,_)).



