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


%:- add_import_module(header_sane,baseKB,end).

:- set_defaultAssertMt(myMt).

:- begin_pfc.

mtProlog(code1).
mtHybrid(kb2).




code1: (a:- printAll('$current_source_module'(_M)),b).

kb2: (b).

genlMt(kb2,code1).

% before test, to make sure a was not accdently defined in kb2
:- sanity( clause(kb2:a,_)).

% before test, genlMt makes the rule available and should not corrupt the code1 module
:- sanity(\+ clause(code1:b,_)).

% make sure genlMt didnt unassert 
:- sanity(clause(kb2:b,_)).



% run the test
kb2: (:- a).


% to make sure a does not get accdently defined in kb2
:- mpred_must( clause(kb2:a,_)).

% genlMt makes the rule available and should not corrupt the code1 module
:- mpred_must(\+ clause(code1:b,_)).

% genlMt 

:- mpred_must(\+ clause(code1:b,_)).
