/* <module>
%
%  PFC is a language extension for prolog.
%
%  It adds a new type of module inheritance
%
% Dec 13, 2035
% Douglas Miles
*/
%  was_module(header_sane,[]).

:- include(test_header).

:- begin_pfc.

:- set_fileAssertMt(cycKB1).

cycKB1:loves(sally,joe).

:- mpred_test(clause_u(cycKB1:loves(_,_))).

:- mpred_test(\+ clause_u(baseKB:loves(_,_))).

:- pfc_test_feature(\+ clause_u(header_sane:loves(_,_))).

:- mpred_test(clause_u(loves(_,_))).


:- mpred_test(call_u(cycKB1:loves(_,_))).

:- pfc_test_feature(\+ call_u(baseKB:loves(_,_))).

:- pfc_test_feature(listing(loves)).

:- pfc_test_feature(mpred_test(\+ call_u(header_sane:loves(_,_)))).

:- pfc_test_feature(mpred_test(call_u(loves(_,_)))).








