%   File   : pfc
%   Author : Tim Finin, finin@umbc.edu
%   Updated: 10/11/87, ...
%   Purpose: consult system file for ensure

mpred_Version(2.2).

pfcFile('pfcsyntax').	% operator declarations.
pfcFile('pfccore').	% core of Pfc.
pfcFile('pfcsupport').	% support maintenance
pfcFile('pfcdb').	% predicates to manipulate database.
pfcFile('pfcdebug').	% debugging aids (e.g. tracing).
pfcFile('pfcjust').	% predicates to manipulate justifications.
pfcFile('pfcwhy').	% interactive exploration of justifications.

pfcLoad :- pfcFile(F), ensure_loaded(F), fail.
pfcLoad.

pfcFcompile :- pfcFile(F), qcompile(F), fail.
pfcFcompile.

:- pfcLoad.

%   File   : pfccompile.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Updated: 10/11/87, ...
%   Purpose: compile system file for Pfc


:- compile(pfcsyntax).
:- compile(pfccore).
:- compile(pfcdb).
:- compile(pfcjust).
:- compile(pfcwhy).
:- compile(pfcdebug).
%   File   : pfcsyntax.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Purpose: syntactic sugar for Pfc - operator definitions and term expansions.

:- module(pfcsyntax, [
    op(500,fx,'~'),
    op(1050,xfx,('==>')),
    op(1050,xfx,'<==>'),
    op(1050,xfx,('==>')),
    op(1050,xfx,'==>'),
    op(1050,xfx,('<-')),
    op(1050,xfx,('<-')),
    op(1100,fx,('==>')),
    op(1150,xfx,('::::'))]).
:- use_module(library(pfc_pack_xform)).

:- op(500,fx,'~').
:- op(1050,xfx,('==>')).
:- op(1050,xfx,'<==>').
:- op(1050,xfx,('<-')).
:- op(1100,fx,('==>')).
:- op(1150,xfx,('::::')).

/*
:- multifile('term_expansion'/2).

term_expansion((P==>Q),(:- add((P==>Q)))).
%term_expansion((P==>Q),(:- add(('<-'(Q,P))))).  % speed-up attempt
term_expansion(('<-'(P,Q)),(:- add(('<-'(P,Q))))).
term_expansion((P<==>Q),(:- add((P<==>Q)))).
term_expansion((RuleName :::: Rule),(:- add((RuleName :::: Rule)))).
term_expansion((==>P),(:- add(P))).
*/


%   File   : pfccore.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Updated: 10/11/87, ...
%            4/2/91 by R. McEntire: added calls to valid_dbref as a
%                                   workaround for the Quintus 3.1
%                                   bug in the recorded database.
%   Purpose: core Pfc predicates.


:- module(pfccore, []).

:- use_module(library(pfc_pack_xform)).

:- use_module(library(lists)).


:- dynamic ('<-')/2.
:- dynamic ('==>')/2.
:- dynamic ('::::')/2.
%:- dynamic '<==>'/2.
:- dynamic 'pt'/2.
:- dynamic 'nt'/3.
:- dynamic 'bt'/2.
:- dynamic fcUndoMethod/2.
:- dynamic fcAction/2.
:- dynamic fcTmsMode/1.
:- dynamic pfcQueue/1.
:- dynamic pfcCurrentDb/1.
:- dynamic pfcHaltSignal/1.
:- dynamic pfcDebugging/0.
:- dynamic pfcSelect/1.
:- dynamic pfcSearch/1.


%%% initialization of global assertons 

pfcSetVal(Stuff):- 
   duplicate_term(Stuff,DStuff),
   functor(DStuff,_,N),
   setarg(N,DStuff,_),
   retractall(DStuff),
   assert(Stuff).

%% pfcDefault/1 initialized a global assertion.
%%  pfcDefault(P,Q) - if there is any fact unifying with P, then do 
%%  nothing, else assert Q.

:- export(pfcDefault/2).
:- module_transparent(pfcDefault/2).
pfcDefault(GeneralTerm,Default) :-
  umt((clause(GeneralTerm,true) -> true ; assert(Default))).

%% fcTmsMode is one of {none,local,cycles} and controles the tms alg.
:- initialization(pfcDefault(fcTmsMode(_), fcTmsMode(cycles))).

% Pfc Search strategy. pfcSearch(X) where X is one of {direct,depth,breadth}
:- initialization(pfcDefault(pfcSearch(_), pfcSearch(direct))).


% 

%% add/2 and post/2 are the main ways to assert new clauses into the
%% database and have forward reasoning done.

%% add(P,S) asserts P into the dataBase with support from S.

add(M:P) :- b_setval(defaultQueryMt,M),b_setval(defaultAssertMt,M),!,
  current_why_UU(UU),
  M:add(P,UU).
add(P) :-  current_why_UU(UU),add(P,UU).

add((==>(P)),S) :- add(P,S).

add(P,S) :- 
  post(P,S),
  pfcRun.

%add(_,_).
%add(P,S) :- pfcWarn("add(~p,~p) failed",[P,S]).


% post(+Ps,+S) tries to add a fact or set of fact to the database.  For
% each fact (or the singelton) post1 is called. It always succeeds.

post([H|T],S) :-
  !,
  post1(H,S),
  post(T,S).
post([],_) :- !.
post(P,S) :- post1(P,S).


% post1(+P,+S) tries to add a fact to the database, and, if it succeeded,
% adds an entry to the pfc queue for subsequent forward chaining.
% It always succeeds.

post1(M:'==>'(P),S) :-!, post1_(M:P,S).
post1('==>'(P),S) :-!, post1_(P,S).
post1(P,S) :- post1_(P,S),!.

post1_(PIn,S) :- 
  defaultAssertMt(M),
  %% db 
  (pfcAddDbToHead(PIn,P) -> true ; P = PIn),
  % old vesrion 
  nop(pfcRemoveOldVersion(P)),
  pfcAddSupport(P,S),
  pfcUnique(P),
  assert(P),
  pfcTraceAdd(P,S),
  !,
  pfcEnqueue(M,P,S),
  !.

post1_(_,_).
%%post1_(P,S) :-  pfcWarn("add(~p,~p) failed",[P,S]).

%%  pfcAddDbToHead(+P,-NewP) is semidet.
% talkes a fact P or a conditioned fact
% (P:-C) and adds the Db context.
%

pfcAddDbToHead(P,NewP) :-
  umt(pfcCurrentDb(Db)),
  (Db=true        -> NewP = P;
   P=(Head:-Body) -> NewP = (Head :- (Db,Body));
   otherwise      -> NewP = (P :- Db)).


%% pfcUnique(X) is det.
% 
% is true if there is no assertion X in the prolog db.
%

pfcUnique((Head:-Tail)) :- 
  !, 
  \+ clause(Head,Tail).
pfcUnique(P) :-
  \+ clause(P,true).


%% pfcEnqueue(P,Q) is det.
% 
% Enqueu according to settings
%
/*
pfcEnqueue(P,S):- strip_module(P,M,PP),
 % defaultAssertMt(M),
  pfcEnqueue(M,PP,S).
*/
pfcGetSearch(Mode):- umt(pfcSearch(Mode0)),!,Mode0=Mode.
pfcGetSearch(direct).
pfcEnqueue(M,P,S) :-
  must(pfcGetSearch(Mode)) 
    -> (Mode=direct  -> fc(P) ;
	Mode=depth   -> pfcAsserta(pfcQueue(M,P),S) ;
	Mode=breadth -> pfcAssert(pfcQueue(M,P),S) ;
	nop(otherwise)         -> pfcWarn("Unrecognized pfcSearch mode: ~p", Mode))
     ; pfcWarn("No pfcSearch mode").


%% pfcRemoveOldVersion(+Rule) is det.
%
% if there is a rule of the form Identifier ::: Rule then delete it.

pfcRemoveOldVersion((Identifier::::Body)) :-
  % this should never happen.
  (var(Identifier)
  ->
  pfcWarn("variable used as an  rule name in ~p :::: ~p",
          [Identifier,Body]);
  umt((pfcRemoveOldVersion0(Identifier::::Body)))).

  
pfcRemoveOldVersion0((Identifier::::Body)) :-
  nonvar(Identifier),
  clause((Identifier::::OldBody),_),
  \+(Body=OldBody),
  pfcWithdraw((Identifier::::OldBody)),
  !.
pfcRemoveOldVersion0(_).



% 

% pfcRun compute the deductive closure of the current database. 
% How this is done depends on the searching mode:
%    direct -  fc has already done the job.
%    depth or breadth - use the pfcQueue mechanism.

pfcRun :-
  (\+ pfcGetSearch(direct)),
  pfcStep,
  pfcRun.
pfcRun.


% pfcStep removes one entry from the pfcQueue and reasons from it.


pfcStep :-  
  % if pfcHaltSignal is true, reset it and fail, thereby stopping inferencing.
  pfcRetract(pfcHaltSignal(Msg)),
  pfcTraceMsg(removing(pfcHaltSignal(Msg))),
  !, 
  fail.

pfcStep :-
  % draw immediate conclusions from the next fact to be considered.
  % fails iff the queue is empty.
  get_next_fact(P),
  ignore(fc(P)),
  !.

get_next_fact(P) :-
  %identifies the nect fact to fc from and removes it from the queue.
  select_next_fact(P),
  remove_selection(P).

remove_selection(P) :- 
  umt((
    pfcRetract(pfcQueue(MM,P)),sanity((strip_module(P,M,PP),MM=M),
  must(pfcRemoveSupportsQuietly(pfcQueue(MM,PP)))))),
  !.
remove_selection(P) :-
  brake(format("~Npfc:get_next_fact - selected fact not on Queue: ~p",
               [P])).


% select_next_fact(P) identifies the next fact to reason from.  
% It tries the user defined predicate first and, failing that, 
%  the default mechanism.

select_next_fact(M:P) :- 
  umt((pfcSelect(M,P))),
  !.  
select_next_fact(P) :- 
  defaultpfcSelect(P),
  !.  

% the default selection predicate takes the item at the froint of the queue.
defaultpfcSelect(M:PP) :- umt((pfcQueue(MM,P),sanity((strip_module(P,M,PP),MM=M)))),!.

% pfcHalt stops the forward chaining.
pfcHalt :-  pfcHalt("unknown_reason",[]).

pfcHalt(Format) :- pfcHalt(Format,[]).

pfcHalt(Format,Args) :- 
  format(Format,Args),
  umt((pfcHaltSignal -> 
       pfcWarn("pfcHalt finds pfcHaltSignal already set")
     ; assert(pfcHaltSignal))).


%%
%%
%% predicates for manipulating triggers
%%

pfcAddTrigger(pt(Trigger,Body),Support) :-
  !,
  pfcTraceMsg('      Adding positive trigger: ','~p~n',
		[pt(Trigger,Body)]),
  deterministically_must(pfcAssert(pt(Trigger,Body),Support)),
  copy_term(pt(Trigger,Body),Tcopy),
  deterministically_must(pfc(Trigger)),
  deterministically_must(fcEvalLHS(Body,(Trigger,Tcopy))),
  fail.


pfcAddTrigger(nt(Trigger,Test,Body),Support) :-
  !,
  pfcTraceMsg('      Adding negative trigger: ','~p~n       test: ~p~n       body: ~p~n',
		[Trigger,Test,Body]),
  copy_term(Trigger,TriggerCopy),
  pfcAssert(nt(TriggerCopy,Test,Body),Support),
  \+ call(Test),
  fcEvalLHS(Body,((\+Trigger),nt(TriggerCopy,Test,Body))).

pfcAddTrigger(bt(Trigger,Body),Support) :-
  !,
  pfcAssert(bt(Trigger,Body),Support),
  pfcBtPtCombine(Trigger,Body,Support).

pfcAddTrigger(X,_Support) :-
  pfcWarn("Unrecognized trigger to pfcAddtrigger: ~p",[X]).


pfcBtPtCombine(Head,Body,Support) :- 
  %% a backward trigger (bt) was just added with head and Body and support Support
  %% find any pt's with unifying heads and add the instantied bt body.
  pfcGetTriggerQuick(pt(Head,_PtBody)),
  fcEvalLHS(Body,Support),
  fail.
pfcBtPtCombine(_,_,_) :- !.

pfcGetTriggerQuick(Trigger) :-  umt(clause(Trigger,true)).
% pfcGetTriggerQuick(Trigger) :-  umt(Trigger).

%%
%%
%% predicates for manipulating action traces.
%%

pfcAddActionTrace(Action,Support) :- 
  % adds an action trace and it's support.
  umt((pfcAddSupport(pfcAction(Action),Support))).

pfcRemActionTrace(pfcAction(A)) :-
  umt((fcUndoMethod(A,M),
  M)),
  !.


%%
%% predicates to remove pfc facts, triggers, action traces, and queue items
%% from the database.
%%

pfcRetract(X) :- 
  %% retract an arbitrary thing.
  pfcType(X,Type),
  pfcRetractType(Type,X),
  !.

pfcRetractType(fact,X) :-   
  %% db 
  pfcAddDbToHead(X,X2)-> retract(X2) ; retract(X).

pfcRetractType(rule,X) :- 
  %% db  
  pfcAddDbToHead(X,X2) ->  retract(X2) ; retract(X).

pfcRetractType(trigger,X) :- 
  retract(X)
    -> unFc(X)
     ; pfcWarn("Trigger not found to retract: ~p",[X]).

pfcRetractType(action,X) :- pfcRemActionTrace(X).
  

%% pfcAdd(X) adds item X to some database

pfcAdd(X) :-
  % what type of X do we have?
  pfcType(X,Type),
  % call the appropriate predicate.
  pfcAddType(Type,X).

pfcAddType(fact,X) :- 
  pfcUnique(X), 
  assert(X),!.
pfcAddType(rule,X) :- 
  pfcUnique(X), 
  assert(X),!.
pfcAddType(trigger,X) :- 
  assert(X).
pfcAddType(action,_Action) :- !.


  

%% pfcWithdraw(P,S) removes support S from P and checks to see if P is still supported.
%% If it is not, then the fact is retreactred from the database and any support
%% relationships it participated in removed.

pfcWithdraw(P) :- 
  current_why_UU(UU),
  % iterate down the list of facts to be pfcWithdraw'ed.
  (is_list(P)->
  pfc_withdraw_list(P,UU);
    % pfcWithdraw/1 is the user's interface - it withdraws user support for P.
  pfcWithdraw(P,UU)).
  
  
pfc_withdraw_list(P) :- 
  current_why_UU(UU),
  pfc_withdraw_list(P,UU).

pfc_withdraw_list([H|T],UU) :-
  % pfcWithdraw each element in the list.
  pfcWithdraw(H,UU),
  pfc_withdraw_list(T,UU).

pfcWithdraw(P,S) :-
  % pfcDebug(format("~Nremoving support ~p from ~p",[S,P])),
  (pfcTraceMsg('    Removing support: ','~p~n',[S]),
     pfcTraceMsg('     Which was: ','~p~n',[P])),
  
  ((pfcRemSupport(P,S)
     -> removeIfUnsupported(P)
      ; pfcWarn("pfcWithdraw/2 Could not find support ~p to remove from fact ~p",
                [S,P]))).

%%
%% pfc_remove2 is like pfcWithdraw, but if P is still in the DB after removing the
%% user's support, it is retracted by more forceful means (e.g. remove).
%%

pfc_remove2(P) :-  freeze(UU,current_why_UU(UU)),
  % pfc_remove2/1 is the user's interface - it withdraws user support for P.
  pfc_remove2(P,UU).

pfc_remove2(P,S) :-
  pfcWithdraw(P,S),
  pfc(P)
     -> remove(P) 
      ; true.

%%
%% remove(+F) retracts fact F from the DB and removes any dependent facts */
%%

remove(F) :- 
  pfcRemoveSupports(F),
  fcUndo(F).


% removes any remaining supports for fact F, complaining as it goes.

pfcRemoveSupports(F) :- 
  pfcRemSupport(F,S),
  pfcWarn("~p was still supported by ~p",[F,S]),
  fail.
pfcRemoveSupports(_).

pfcRemoveSupportsQuietly(F) :- 
  pfcRemSupport(F,_),
  fail.
pfcRemoveSupportsQuietly(_).

% fcUndo(X) undoes X.


fcUndo(pfcAction(A)) :-  
  % undo an action by finding a method and successfully executing it.
  !,
  pfcRemActionTrace(pfcAction(A)).

fcUndo(pt(Head,Body)) :-  
  % undo a positive trigger.
  %
  !,
  (retract(pt(Head,Body))
    -> unFc(pt(Head,Body))
     ; pfcWarn("Trigger not found to retract: ~p",[pt(Head,Body)])).

fcUndo(nt(Head,Condition,Body)) :-  
  % undo a negative trigger.
  !,
  (retract(nt(Head,Condition,Body))
    -> unFc(nt(Head,Condition,Body))
     ; pfcWarn("Trigger not found to retract: ~p",[nt(Head,Condition,Body)])).

fcUndo(Fact) :-
  % undo a random fact, printing out the trace, if relevant.
  retract(Fact),
  pfcTraceRem(Fact),
  unFc1(Fact).
  

%% unFc(P) is det.
%
% unFc(P) "un-forward-chains" from fact f.  That is, fact F has just
% been removed from the database, so remove all support relations it
% participates in and check the things that they support to see if they
% should stayu in the database or should also be removed.


unFc(F) :- 
  pfcRetractSupportRelations(F),
  unFc1(F).

unFc1(F) :-
  pfcUnFcCheckTriggers(F),
  % is this really the right place for pfcRun<?
  pfcRun.


pfcUnFcCheckTriggers(F) :-
  pfcType(F,fact),
  copy_term(F,Fcopy),
  umt(nt(Fcopy,Condition,Action)),
  (\+ umt(Condition)),
  fcEvalLHS(Action,((\+F),nt(F,Condition,Action))),
  fail.
pfcUnFcCheckTriggers(_).

pfcRetractSupportRelations(Fact) :-
  pfcType(Fact,Type),
  (Type=trigger -> pfcRemSupport(P,(_,Fact))),
  removeIfUnsupported(P),
  fail.
pfcRetractSupportRelations(Fact) :-
  % pfcType(Fact,Type),
  pfcRemSupport(P,(Fact,_)),
  removeIfUnsupported(P),
  fail.
pfcRetractSupportRelations(_).



%% removeIfUnsupported(+P) checks to see if P is supported and removes
%% it from the DB if it is not.

removeIfUnsupported(P) :- 
   fcSupported(P) -> true ;  fcUndo(P).


%% fcSupported(+P) succeeds if P is "supported". What this means
%% depends on the TMS mode selected.

fcSupported(P) :- 
  must(umt(fcTmsMode(Mode));Mode=cycles),
  pfcSupported(Mode,P).

pfcSupported(local,P) :- !, pfcGetSupport(P,_).
pfcSupported(cycles,P) :-  !, wellFounded(P).
pfcSupported(_,_P) :- true.


%%
%% a fact is well founded if it is supported by the user
%% or by a set of facts and a rules, all of which are well founded.
%%

wellFounded(Fact) :- wf(Fact,[]).

wf(F,_) :-
  % supported by user (axiom) or an "absent" fact (assumption).
  (axiom(F) ; assumption(F)),
  !.

wf(F,Descendants) :-
  % first make sure we aren't in a loop.
  (\+ memberchk(F,Descendants)),
  % find a justification.
  supports(F,Supporters),
  % all of whose members are well founded.
  wflist(Supporters,[F|Descendants]),
  !.

%% wflist(L) simply maps wf over the list.

wflist([],_).
wflist([X|Rest],L) :-
  wf(X,L),
  wflist(Rest,L).



% supports(+F,-ListofSupporters) where ListOfSupports is a list of the
% supports for one justification for fact F -- i.e. a list of facts which,
% together allow one to deduce F.  One of the facts will typically be a rule.
% The supports for a user-defined fact are: [user].

supports(F,[Fact|MoreFacts]) :-
  pfcGetSupport(F,(Fact,Trigger)),
  triggerSupports(Trigger,MoreFacts).

triggerSupports(U,[]) :- current_why_UU((_,U)), !.
triggerSupports(Trigger,[Fact|MoreFacts]) :-
  pfcGetSupport(Trigger,(Fact,AnotherTrigger)),
  triggerSupports(AnotherTrigger,MoreFacts).


%%
%%
%% fc(X) forward chains from a fact or a list of facts X.
%%


fc([H|T]) :- !, fc1(H), fc(T).
fc([]) :- !.
fc(P) :- fc1(P).

% fc1(+P) forward chains for a single fact.

fc1(Fact) :-
  fc_rule_check(Fact),
  copy_term(Fact,F),
  % check positive triggers
  fcpt(Fact,F),
  % check negative triggers
  fcnt(Fact,F).


%%
%% fc_rule_check(P) does some special, built in forward chaining if P is 
%% a rule.
%% 

fc_rule_check((P==>Q)) :-  
  !,  
  processRule(P,Q,(P==>Q)).
fc_rule_check((Name::::P==>Q)) :- 
  !,  
  processRule(P,Q,(Name::::P==>Q)).
fc_rule_check((P<==>Q)) :- 
  !, 
  processRule(P,Q,(P<==>Q)), 
  processRule(Q,P,(P<==>Q)).
fc_rule_check((Name::::P<==>Q)) :- 
  !, 
  processRule(P,Q,((Name::::P<==>Q))), 
  processRule(Q,P,((Name::::P<==>Q))).

fc_rule_check(('<-'(P,Q))) :-
  !,
  pfcDefineBcRule(P,Q,('<-'(P,Q))).

fc_rule_check(_).


fcpt(Fact,F) :- 
  pfcGetTriggerQuick(pt(F,Body)),
  pfcTraceMsg('      Found positive trigger: ~p~n       body: ~p~n',
		[F,Body]),
  fcEvalLHS(Body,(Fact,pt(F,Body))),
  fail.

%fcpt(Fact,F) :- 
%  pfcGetTriggerQuick(pt(presently(F),Body)),
%  fcEvalLHS(Body,(presently(Fact),pt(presently(F),Body))),
%  fail.

fcpt(_,_).

fcnt(_Fact,F) :-
  support3(nt(F,Condition,Body),X,_),
  call(Condition),
  pfcWithdraw(X,(_,nt(F,Condition,Body))),
  fail.
fcnt(_,_).


%%
%% pfcDefineBcRule(+Head,+Body,+ParentRule) - defines a backeard
%% chaining rule and adds the corresponding bt triggers to the database.
%%

pfcDefineBcRule(Head,_Body,ParentRule) :-
  (\+ pfcLiteral(Head)),
  pfcWarn("Malformed backward chaining rule.  ~p not atomic.",[Head]),
  pfcWarn("rule: ~p",[ParentRule]),
  !,
  fail.

pfcDefineBcRule(Head,Body,ParentRule) :-
  copy_term(ParentRule,ParentRuleCopy),
  current_why_UU((_,U)),
  buildRhs(Head,Rhs),
  forall(pfc_nf(Body,Lhs),
          ignore((buildTrigger(Lhs,rhs(Rhs),Trigger),
           add(bt(Head,Trigger),(ParentRuleCopy,U))))).
 


%%
%%
%% eval something on the LHS of a rule.
%%

 
fcEvalLHS((Test->Body),Support) :-  
  !, 
  (call(Test) -> fcEvalLHS(Body,Support)),
  !.

fcEvalLHS(rhs(X),Support) :-
  !,
  pfc_eval_rhs(X,Support),
  !.

fcEvalLHS(X,Support) :-
  pfcType(X,trigger),
  !,
  pfcAddTrigger(X,Support),
  !.

%fcEvalLHS(snip(X),Support) :- 
%  snip(Support),
%  fcEvalLHS(X,Support).

fcEvalLHS(X,_) :-
  pfcWarn("Unrecognized item found in trigger body, namely ~p.",[X]).


%%
%% eval something on the RHS of a rule.
%%

pfc_eval_rhs([],_) :- !.
pfc_eval_rhs([Head|Tail],Support) :- 
  pfc_eval_rhs1(Head,Support),
  pfc_eval_rhs(Tail,Support).


pfc_eval_rhs1({Action},Support) :-
 % evaluable Prolog code.
 !,
 fcEvalAction(Action,Support).

pfc_eval_rhs1(P,_Support) :-
 % predicate to remove.
 pfcNegatedLiteral(P),
 !,
 pfcWithdraw(P).

pfc_eval_rhs1([X|Xrest],Support) :-
 % embedded sublist.
 !,
 pfc_eval_rhs([X|Xrest],Support).

pfc_eval_rhs1(Assertion,Support) :-
 % an assertion to be added.
 post1(Assertion,Support).


pfc_eval_rhs1(X,_) :-
  pfcWarn("Malformed rhs of a rule: ~p",[X]).


%%
%% evaluate an action found on the rhs of a rule.
%%

fcEvalAction(Action,Support) :-
  umt(Action), 
  (undoable(Action) 
     -> pfcAddActionTrace(Action,Support) 
      ; true).


%%
%% 
%%

trigger_trigger(Trigger,Body,_Support) :-
 trigger_trigger1(Trigger,Body).
trigger_trigger(_,_,_).


%trigger_trigger1(presently(Trigger),Body) :-
%  !,
%  copy_term(Trigger,TriggerCopy),
%  pfc_call(Trigger),
%  fcEvalLHS(Body,(presently(Trigger),pt(presently(TriggerCopy),Body))),
%  fail.

trigger_trigger1(Trigger,Body) :-
  copy_term(Trigger,TriggerCopy),
  pfc_call(Trigger),
  fcEvalLHS(Body,(Trigger,pt(TriggerCopy,Body))),
  fail.



%% pfc_call(F) is nondet.
%
% pfc_call(F) is true iff F is a fact available for forward chaining.
% Note that this has the side effect of catching unsupported facts and
% assigning them support from God.
%

pfc(P) :-
  % trigger any bc rules.
  pfcGetTriggerQuick(bt(P,Trigger)),
  pfcGetSupport(bt(P,Trigger),S),
  fcEvalLHS(Trigger,S),
  fail.

pfc(F) :- ground(F),!,pfc0(F),!.
pfc(F) :- pfc0(F).
pfc(F) :-
  %- this is probably not advisable due to extreme inefficiency.
  var(F)    ->  pfcFact(F) ;
  otherwise ->  clause(F,Condition),call(Condition).

%- pfc(F) :- 
%-  %% we really need to check for system predicates as well.
%-  % current_predicate(_,F) -> call(F).
%-  clause(F,Condition),call(Condition).


pfc0(F) :- !,
  %- this is probably not advisable due to extreme inefficiency.
  (var(F)    ->  pfcFact(F) ;
  otherwise -> findall(F-C,clause(F,C),List),member(F-C,List),umt(C)).



% an action is undoable if there exists a method for undoing it.
undoable(A) :- umt(fcUndoMethod(A,_)).



%%
%%
%% defining fc rules 
%%

%% pfc_nf(+In,-Out) maps the LHR of a pfc rule In to one normal form 
%% Out.  It also does certain optimizations.  Backtracking into this
%% predicate will produce additional clauses.


pfc_nf(LHS,List) :-
  pfc_nf1(LHS,List2),
  pfc_nf_negations(List2,List).


%% pfc_nf1(+In,-Out) maps the LHR of a pfc rule In to one normal form
%% Out.  Backtracking into this predicate will produce additional clauses.

% handle a variable.

pfc_nf1(P,[P]) :- is_ftVar(P), !.


pfc_nf1(P/Cond,[(\+P)/Cond]):- mpred_negated_literal(P), !, dmsg(warn(pfc_nf1(P/Cond,[(\+P)/Cond]))).

pfc_nf1(P/Cond,[P/Cond]):- var(P),!.
pfc_nf1(P/Cond,[P/Cond]):- ((mpred_db_type(P,trigger);mpred_literal_nonvar(P))), !.


% these next two rules are here for upward compatibility and will go 
% away eventually when the P/Condition form is no longer used anywhere.

pfc_nf1(P/Cond,[(\+P)/Cond]) :- pfcNegatedLiteral(P), !.

pfc_nf1(P/Cond,[P/Cond]) :-  pfcLiteral(P), !.

%% handle a negated form

pfc_nf1(NegTerm,NF) :-
  pfc_unnegate(NegTerm,Term),
  !,
  pfc_nf1_negation(Term,NF).

%% disjunction.

pfc_nf1((P;Q),NF) :- 
  !,
  (pfc_nf1(P,NF) ;   pfc_nf1(Q,NF)).


%% conjunction.

pfc_nf1((P,Q),NF) :-
  !,
  pfc_nf1(P,NF1),
  pfc_nf1(Q,NF2),
  append(NF1,NF2,NF).


% prolog_clause pfc_nf1
pfc_nf1((H :- B)  , [(H :- B)]):-  
  mpred_positive_literal(H),!.


%% handle a random atom.

pfc_nf1(P,[P]) :-
  pfcLiteral(P), 
  !.

%%% shouln't we have something to catch the rest as errors?
pfc_nf1(Term,[Term]) :-
  pfcWarn("pfc_nf doesn't know how to normalize ~p",[Term]).


%% pfc_nf1_negation(P,NF) is true if NF is the normal form of \+P.
pfc_nf1_negation((P/Cond),[(\+(P))/Cond]) :- !.

pfc_nf1_negation((P;Q),NF) :-
  !,
  pfc_nf1_negation(P,NFp),
  pfc_nf1_negation(Q,NFq),
  append(NFp,NFq,NF).

pfc_nf1_negation((P,Q),NF) :- 
  % this code is not correct! twf.
  !,
  pfc_nf1_negation(P,NF) 
  ;
  (pfc_nf1(P,Pnf),
   pfc_nf1_negation(Q,Qnf),
   append(Pnf,Qnf,NF)).

pfc_nf1_negation(P,[\+P]).


%% pfc_nf_negations(List2,List) sweeps through List2 to produce List,
%% changing ~{...} to {\+...}
%%% ? is this still needed? twf 3/16/90

pfc_nf_negations(X,X) :- !.  % I think not! twf 3/27/90

pfc_nf_negations([],[]).

pfc_nf_negations([H1|T1],[H2|T2]) :-
  pfc_nf_negation(H1,H2),
  pfc_nf_negations(T1,T2).

% Maybe \+ tilded_negation ?

pfc_nf_negation(Form,{\+ X}) :-
  nonvar(Form),
  Form=(~({X})),
  !.
pfc_nf_negation(X,X).



     %% constrain_meta(+Lhs, ?Guard) is semidet.
     %
     % Creates a somewhat sane Guard.
     %
     % To turn this feature off...
     % ?- set_prolog_flag(constrain_meta,false).  
     %
     %
     constrain_meta(_,_):- current_prolog_flag(constrain_meta,false),!,fail.
     % FACT
     constrain_meta(P,mpred_positive_fact(P)):- is_ftVar(P),!.
     % NEG chaining
     constrain_meta(~ P, CP):- !,  constrain_meta(P,CP).
     constrain_meta(\+ P, CP):- !,  constrain_meta(P,CP).
     % FWD chaining
     constrain_meta((_==>Q),nonvar(Q)):- !, is_ftVar(Q).
     % EQV chaining
     constrain_meta((P<==>Q),(nonvar(Q);nonvar(P))):- (is_ftVar(Q);is_ftVar(P)),!.
     % BWD chaining
     constrain_meta((Q <- _),mpred_literal(Q)):- is_ftVar(Q),!.
     constrain_meta((Q <- _),CQ):- !, constrain_meta(Q,CQ).
     % CWC chaining
     constrain_meta((Q :- _),mpred_literal(Q)):- is_ftVar(Q),!.
     constrain_meta((Q :- _),CQ):- !, constrain_meta(Q,CQ).





     is_simple_lhs(ActN):- is_ftVar(ActN),!,fail.
     is_simple_lhs( \+ _ ):-!,fail.
     is_simple_lhs( ~ _ ):-!,fail.
     is_simple_lhs( _  / _ ):-!,fail.
     is_simple_lhs((Lhs1,Lhs2)):- !,is_simple_lhs(Lhs1),is_simple_lhs(Lhs2).
     is_simple_lhs((Lhs1;Lhs2)):- !,is_simple_lhs(Lhs1),is_simple_lhs(Lhs2).
     is_simple_lhs(ActN):- is_active_lhs(ActN),!,fail.
     is_simple_lhs((Lhs1/Lhs2)):- !,fail, is_simple_lhs(Lhs1),is_simple_lhs(Lhs2).
     is_simple_lhs(_).


     is_active_lhs(ActN):- var(ActN),!,fail.
     is_active_lhs(!).
     is_active_lhs(cut_c).
     is_active_lhs(actn(_Act)).
     is_active_lhs('{}'(_Act)).
     is_active_lhs((Lhs1/Lhs2)):- !,is_active_lhs(Lhs1);is_active_lhs(Lhs2).
     is_active_lhs((Lhs1,Lhs2)):- !,is_active_lhs(Lhs1);is_active_lhs(Lhs2).
     is_active_lhs((Lhs1;Lhs2)):- !,is_active_lhs(Lhs1);is_active_lhs(Lhs2).


     add_lhs_cond(Lhs1/Cond,Lhs2,Lhs1/(Cond,Lhs2)):-!.
     add_lhs_cond(Lhs1,Lhs2,Lhs1/Lhs2).



%%
%% buildRhs(+Conjunction,-Rhs)
%%

buildRhs(X,[X]) :- 
  var(X),
  !.

buildRhs((A,B),[A2|Rest]) :- 
  !, 
  pfcCompileRhsTerm(A,A2),
  buildRhs(B,Rest).

buildRhs(X,[X2]) :-
   pfcCompileRhsTerm(X,X2).

pfcCompileRhsTerm((P/C),((P:-C))) :- !.

pfcCompileRhsTerm(P,P).


%% pfc_unnegate(N,P) is true if N is a negated term and P is the term
%% with the negation operator stripped.

pfc_unnegate(P,_):- is_ftVar(P),!,fail.
pfc_unnegate((~P),P).
pfc_unnegate((-P),P).
pfc_unnegate((\+(P)),P).

pfcNegatedLiteral(P) :- 
  callable(P),
  pfc_unnegate(P,Q),
  pfcPositiveLiteral(Q).

pfcLiteral(X) :- pfcNegatedLiteral(X).
pfcLiteral(X) :- pfcPositiveLiteral(X).

pfcPositiveLiteral(X) :-  
  callable(X),
  functor(X,F,_), 
  \+ pfcConnective(F).

pfcConnective(';').
pfcConnective(',').
pfcConnective('/').
pfcConnective('|').
pfcConnective(('==>')).
pfcConnective(('<-')).
pfcConnective('<==>').

pfcConnective(('==>')).
pfcConnective(('<-=')).
pfcConnective('==>').

pfcConnective('-').
%pfcConnective('~').
pfcConnective(( \+ )).

processRule(Lhs,Rhs,ParentRule) :-
 current_why_UU((_,U)),
  copy_term(ParentRule,ParentRuleCopy),
  buildRhs(Rhs,Rhs2),
  forall(pfc_nf(Lhs,Lhs2), 
          ignore(buildRule(Lhs2,rhs(Rhs2),(ParentRuleCopy,U)))).

buildRule(Lhs,Rhs,Support) :-
  buildTrigger(Lhs,Rhs,Trigger),
  fcEvalLHS(Trigger,Support).

buildTrigger([],Consequent,Consequent).

buildTrigger([V|Triggers],Consequent,pt(V,X)) :-
  var(V),
  !, 
  buildTrigger(Triggers,Consequent,X).

buildTrigger([(T1/Test)|Triggers],Consequent,nt(T2,Test2,X)) :-
  pfc_unnegate(T1,T2),
  !, 
  buildNtTest(T2,Test,Test2),
  buildTrigger(Triggers,Consequent,X).

buildTrigger([(T1)|Triggers],Consequent,nt(T2,Test,X)) :-
  pfc_unnegate(T1,T2),
  !,
  buildNtTest(T2,true,Test),
  buildTrigger(Triggers,Consequent,X).

buildTrigger([{Test}|Triggers],Consequent,(Test->X)) :-
  !,
  buildTrigger(Triggers,Consequent,X).

buildTrigger([T/Test|Triggers],Consequent,pt(T,X)) :-
  !, 
  buildTest(Test,Test2),
  buildTrigger([{Test2}|Triggers],Consequent,X).


%buildTrigger([snip|Triggers],Consequent,snip(X)) :-
%  !,
%  buildTrigger(Triggers,Consequent,X).

buildTrigger([T|Triggers],Consequent,pt(T,X)) :-
  !, 
  buildTrigger(Triggers,Consequent,X).

%%
%% buildNtTest(+,+,-).
%%
%% builds the test used in a negative trigger (nt/3).  This test is a
%% conjunction of the check than no matching facts are in the db and any
%% additional test specified in the rule attached to this ~ term.
%%

buildNtTest(T,Testin,Testout) :-
  buildTest(Testin,Testmid),
  pfcConjoin((pfc(T)),Testmid,Testout).

  
% this just strips away any currly brackets.

buildTest({Test},Test) :- !.
buildTest(Test,Test).

%%


%% pfcType(+VALUE1, ?Type) is semidet.
%
% PFC Database Type.
%
%  simple typeing for Pfc objects
%


pfcType(('==>'(_,_)),Type) :- !, Type=rule.
pfcType(('<==>'(_,_)),Type) :- !, Type=rule.
pfcType(('<-'(_,_)),Type) :- !, Type=rule.
pfcType(pt(_,_,_),Type) :- !, Type=trigger.
pfcType(pt(_,_),Type) :- !, Type=trigger.
pfcType(nt(_,_,_),Type) :- !,  Type=trigger.
pfcType(bt(_,_),Type) :- !,  Type=trigger.
pfcType(pfcAction(_),Type) :- !, Type=action.
pfcType((('::::'(_,X))),Type) :- !, pfcType(X,Type).
pfcType(_,fact) :-
  %% if it's not one of the above, it must be a fact!
  !.

pfcAssert(P,Support) :- 
  (pfc_clause(P) ; assert(P)),
  !,
  pfcAddSupport(P,Support).

pfcAsserta(P,Support) :-
  (pfc_clause(P) ; asserta(P)),
  !,
  pfcAddSupport(P,Support).

pfcAssertz(P,Support) :-
  (pfc_clause(P) ; assertz(P)),
  !,
  pfcAddSupport(P,Support).

pfc_clause((Head :- Body)) :-
  !,
  copy_term(Head,Head_copy),
  copy_term(Body,Body_copy),
  clause(Head,Body),
  variant(Head,Head_copy),
  variant(Body,Body_copy).

pfc_clause(Head) :-
  % find a unit clause identical to Head by finding one which unifies,
  % and then checking to see if it is identical
  copy_term(Head,Head_copy),
  clause(Head_copy,true),
  variant(Head,Head_copy).

pfcForEach(Binder,Body) :- umt(( Binder,pfcdo(Body))),fail.
pfcForEach(_,_).

% pfcdo(X) executes X once and always succeeds.
pfcdo(X) :- umt((X)),!.
pfcdo(_).


%% pfcUnion(L1,L2,L3) - true if set L3 is the result of appending sets
%% L1 and L2 where sets are represented as simple lists.

pfcUnion([],L,L).
pfcUnion([Head|Tail],L,Tail2) :-  
  memberchk(Head,L),
  !,
  pfcUnion(Tail,L,Tail2).
pfcUnion([Head|Tail],L,[Head|Tail2]) :-  
  pfcUnion(Tail,L,Tail2).


%% pfcConjoin(+Conjunct1,+Conjunct2,?Conjunction).
%% arg3 is a simplified expression representing the conjunction of
%% args 1 and 2.

pfcConjoin(C1,C2,C12):- 
  C1 == true -> C12 = C2;
  C2 == true -> C12 = C1;
  otherwise -> C12 = (C1,C2).

/*
pfcConjoin(true,X,X) :- !.
pfcConjoin(X,true,X) :- !.
pfcConjoin(C1,C2,(C1,C2)).
*/

:- fixup_exports.


%   File   : pfcdb.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Author :  Dave Matuszek, dave@prc.unisys.com
%   Author :  Dan Corpron
%   Updated: 10/11/87, ...
%   Purpose: predicates to manipulate a pfc database (e.g. save,
%%	restore, reset, etc.0

:- module(pfcdb, []).
:- use_module(library(pfc_pack_xform)).

% pfcDatabaseTerm(P/A) is true iff P/A is something that pfc adds to
% the database and should not be present in an empty pfc database

pfcDatabaseTerm(support1/3):- ifNotDMiles(true,fail).
pfcDatabaseTerm(support2/3):- ifNotDMiles(true,fail).
pfcDatabaseTerm(support3/3):- ifNotDMiles(true,fail).
pfcDatabaseTerm(spft/3):- ifNotDMiles(fail,true).

pfcDatabaseTerm(pt/2).
pfcDatabaseTerm(bt/2).
pfcDatabaseTerm(nt/3).
pfcDatabaseTerm('==>'/2).
pfcDatabaseTerm('<==>'/2).
pfcDatabaseTerm('<-'/2).
pfcDatabaseTerm(pfcQueue/2).

% removes all forward chaining rules and justifications from db.

pfcReset :-
  pfcGetSupport(P,(F,Trigger)),
  pfcAddDbToHead(P,PDb),
  pfcRetractOrWarn(PDb),
  pfcRetractOrWarn(support1(P,F,Trigger)),
  pfcRetractOrWarn(support2(F,Trigger,P)),
  pfcRetractOrWarn(support3(Trigger,P,F)),
  fail.
pfcReset :-
  pfcDatabaseItem(T),
  pfcError("Pfc database not empty after pfcReset, e.g., ~p.~n",[T]).
pfcReset.

% true if there is some pfc crud still in the database.
pfcDatabaseItem(Term) :-
  pfcDatabaseTerm(P/A),
  functor(Term,P,A),
  clause(Term,_).

pfcRetractOrWarn(X) :-  retract(X), !.
pfcRetractOrWarn(X) :- 
  pfcWarn("Couldn't retract ~p.",[X]).


:- fixup_exports.

%   File   : pfcdebug.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Author :  Dave Matuszek, dave@prc.unisys.com
%   Updated:
%   Purpose: provides predicates for examining the database and debugginh 
%   for Pfc.

:- module(pfcdebug, []).
:- use_module(library(pfc_pack_xform)).

:- dynamic pfcTraced/1.
:- dynamic pfcSpied/2.
:- dynamic pfcTraceExecution/0.
:- dynamic   pfcWarnings/1.


:- initialization(pfcDefault(pfcWarnings(_), pfcWarnings(true))).

%% predicates to examine the state of pfc

pfcQueue :- umt(( listing(pfcQueue/2))).

pfcPrintDB :-
  pfcPrintFacts,
  pfcPrintRules,
  pfcPrintTriggers,
  pfcPrintSupports.

%% pfcPrintFacts ...

pfcPrintFacts :- pfcPrintFacts(_,true).

pfcPrintFacts(Pattern) :- pfcPrintFacts(Pattern,true).

pfcPrintFacts(P,C) :-
  pfcFacts(P,C,L),
  pfcClassifyFacts(L,User,Pfc,_Rule),
  ansi_format([underline],"~N~nUser added facts: ",[]),
  pfcPrintitems(User),
  ansi_format([underline],"~N~nPfc added facts: ",[]),
  pfcPrintitems(Pfc).



pfcPrintitems(List):- \+ \+ umt((pfcPrintitems0(List))).
%- printitems0 clobbers it's arguments - beware!
pfcPrintitems0([]).
pfcPrintitems0([H|T]) :-
  numbervars(H,0,_),
  ansi_format([bold],"~N  ~p",[H]),
  pfcPrintitems0(T).

pfcClassifyFacts([],[],[],[]).

pfcClassifyFacts([H|T],User,Pfc,[H|Rule]) :-
  pfcType(H,rule),
  !,
  pfcClassifyFacts(T,User,Pfc,Rule).

pfcClassifyFacts([H|T],[H|User],Pfc,Rule) :-
  pfcGetSupport(H,UU),
  get_first_real_user_reason(H,UU),
  is_axiom_support(UU),
  !,
  pfcClassifyFacts(T,User,Pfc,Rule).

pfcClassifyFacts([H|T],User,[H|Pfc],Rule) :-
  pfcClassifyFacts(T,User,Pfc,Rule).

pfcPrintRules :-
  bagof((P==>Q),clause((P==>Q),true),R1),
  pfcPrintitems(R1),
  bagof((P<==>Q),clause((P<==>Q),true),R2),
  pfcPrintitems(R2),
  bagof((P<-Q),clause((P<-Q),true),R3),
  pfcPrintitems(R3).

pfcPrintTriggers :-
  ansi_format([underline],"~NPositive triggers...~n",[]),
  bagof(pt(T,B),pfcGetTrigger(pt(T,B)),Pts),
  pfcPrintitems(Pts),
  ansi_format([underline],"~NNegative triggers...~n",[]),
  bagof(nt(A,B,C),pfcGetTrigger(nt(A,B,C)),Nts),
  pfcPrintitems(Nts),
  ansi_format([underline],"~NGoal triggers...~n",[]),
  bagof(bt(A,B),pfcGetTrigger(bt(A,B)),Bts),
  pfcPrintitems(Bts).

pfcPrintSupports :- 
  % temporary hack.
  setof((S > P), pfcGetSupport(P,S),L),
  pfcPrintitems(L).

%% pfcFact(P) is true if fact P was asserted into the database via add.

pfcFact(P) :- pfcFact(P,true).

%% pfcFact(P,C) is true if fact P was asserted into the database via
%% add and contdition C is satisfied.  For example, we might do:
%% 
%%  pfcFact(X,pfcUserFact(X))
%%

pfcFact(P,C) :- 
  pfcGetSupport(P,_),
  pfcType(P,fact),
  call(C).

%% pfcFacts(-ListofPfcFacts) returns a list of facts added.

pfcFacts(L) :- pfcFacts(_,true,L).

pfcFacts(P,L) :- pfcFacts(P,true,L).

%% pfcFacts(Pattern,Condition,-ListofPfcFacts) returns a list of facts added.

pfcFacts(P,C,L) :- setof(P,pfcFact(P,C),L).

brake(X) :-  pfc(X), break.

%%
%%
%% predicates providing a simple tracing facility
%%

pfcTraceAdd(P) :- 
  % this is here for upward compat. - should go away eventually.
  pfcTraceAdd(P,(o,o)).

pfcTraceAdd(pt(_,_),_) :-
  % hack for now - never trace triggers.
  !.
pfcTraceAdd(nt(_,_,_),_) :-
  % hack for now - never trace triggers.
  !.

pfcTraceAdd(P,S) :-
   pfcTraceAddPrint(P,S),
   pfcTraceBreak(P,S).
   

pfcTraceAddPrint(P,S) :-
  umt(pfcTraced(P)),
  !,
  copy_term(P,Pcopy),
  numbervars(Pcopy,0,_),
  (current_why_UU(S)
       -> ansi_format([fg(green)],"~NAdding (u) ~p~n",[Pcopy])
        ; ansi_format([fg(green)],"~NAdding ~p~n",[Pcopy])).

pfcTraceAddPrint(_,_).


pfcTraceBreak(P,_S) :-
  umt(pfcSpied(P,add)) -> 
   (copy_term(P,Pcopy),
    numbervars(Pcopy,0,_),
    ansi_format([fg(yellow)],"~N~nBreaking on add(~p)~n",[Pcopy]),
    break)
   ; true.

pfcTraceRem(pt(_,_)) :-
  % hack for now - never trace triggers.
  !.
pfcTraceRem(nt(_,_,_)) :-
  % hack for now - never trace triggers.
  !.

pfcTraceRem(P) :-
  (umt(pfcTraced(P))
     -> ansi_format([fg(cyan)],'~NRemoving ~p.',[P])
      ; true),
  (umt(pfcSpied(P,rem))
   -> (ansi_format([fg(yellow)],"~NBreaking on rem(~p)",[P]),
       break)
   ; true).


pfcTrace :- pfcTrace(_).

pfcTrace(Form) :-
  assert(pfcTraced(Form)).

pfcTrace(Form,Condition) :- 
  assert((pfcTraced(Form) :- umt(Condition))).

pfcSpy(Form) :- pfcSpy(Form,[add,rem],true).

pfcSpy(Form,Modes) :- pfcSpy(Form,Modes,true).

pfcSpy(Form,[add,rem],Condition) :-
  !,
  pfcSpy1(Form,add,Condition),
  pfcSpy1(Form,rem,Condition).

pfcSpy(Form,Mode,Condition) :-
  pfcSpy1(Form,Mode,Condition).

pfcSpy1(Form,Mode,Condition) :-
  assert((pfcSpied(Form,Mode) :- umt(Condition))).

pfcNospy :- pfcNospy(_,_,_).

pfcNospy(Form) :- pfcNospy(Form,_,_).

pfcNospy(Form,Mode,Condition) :- 
  clause(pfcSpied(Form,Mode), umt(Condition), Ref),
  erase(Ref),
  fail.
pfcNospy(_,_,_).

pfcNoTrace :- pfcUntrace.
pfcUntrace :- pfcUntrace(_).
pfcUntrace(Form) :- retractall(pfcTraced(Form)).

% needed:  pfcTraceRule(Name)  ...


pfcTraceMsg(Msg) :- pfcTraceMsg('TRACE:','~N~p~N', Msg),!.
% if the correct flag is set, trace exection of Pfc
pfcTraceMsg(Msg,Args) :- pfcTraceMsg('       TRACE:',Msg,Args).
pfcTraceMsg(PreMsg,Msg,Args) :-
    umt(pfcTraceExecution),
    !,
    ansi_format([fg(green)], '~N~n', []),!,
    ansi_format([fg(green)], PreMsg, []),!,
    ansi_format([fg(yellow)], Msg, Args),!.
pfcTraceMsg(_PreMsg,_Msg,_Args).


mpred_notrace_exec:- pfcNoWatch.

mpred_trace_exec:- pfcWatch.

pfcWatch :- assert(pfcTraceExecution).

pfcNoWatch :-  retractall(pfcTraceExecution).

pfcError(Msg) :-  pfcError(Msg,[]).

pfcError(Msg,Args) :- 
  ansi_format([fg(red)],"~N~nERROR/Pfc: ",[]),
  ansi_format([fg(red),bold],Msg,Args),
  ansi_format([underline],"~N",[]).


%%
%% These control whether or not warnings are printed at all.
%%   pfcWarn.
%%   nopfcWarn.
%%
%% These print a warning message if the flag pfcWarnings is set.
%%   pfcWarn(+Message)
%%   pfcWarn(+Message,+ListOfArguments)
%%

pfcWarn :- 
  retractall(pfcWarnings(_)),
  assert(pfcWarnings(true)).

nopfcWarn :-
  retractall(pfcWarnings(_)),
  assert(pfcWarnings(false)).
 
pfcWarn(Msg) :-  pfcWarn('~p',[Msg]).

pfcWarn(Msg,Args) :- 
  umt(pfcWarnings(true)),
  !,
  ansi_format([fg(red)],"~N~nWARNING/Pfc: ",[]),
  ansi_format([fg(yellow)],Msg,Args),
  ansi_format([underline],"~N",[]).
pfcWarn(_,_).

%%
%% pfcWarnings/0 sets flag to cause pfc warning messages to print.
%% pfcNoWarnings/0 sets flag to cause pfc warning messages not to print.
%%

pfcWarnings :- 
  retractall(pfcWarnings(_)),
  assert(pfcWarnings(true)).

pfcNoWarnings :- 
  retractall(pfcWarnings(_)).

:- fixup_exports.
%   File   : pfcjust.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Author :  Dave Matuszek, dave@prc.unisys.com
%   Updated:
%   Purpose: predicates for accessing Pfc justifications.
%   Status: more or less working.
%   Bugs:

%= *** predicates for exploring supports of a fact *****

:- module(pfcjust, []).
:- use_module(library(pfc_pack_xform)).

:- use_module(library(lists)).

justification(F,J) :- supports(F,J).

justifications(F,Js) :- bagof(J,justification(F,J),Js).



%% base(P,L) - is true iff L is a list of "base" facts which, taken
%% together, allows us to deduce P.  A base fact is an axiom (a fact 
%% added by the user or a raw Prolog fact (i.e. one w/o any support))
%% or an assumption.

base(F,[F]) :- (axiom(F) ; assumption(F)),!.

base(F,L) :-
  % i.e. (reduce 'append (map 'base (justification f)))
  justification(F,Js),
  bases(Js,L).


%% bases(L1,L2) is true if list L2 represents the union of all of the 
%% facts on which some conclusion in list L1 is based.

bases([],[]).
bases([X|Rest],L) :-
  base(X,Bx),
  bases(Rest,Br),
  pfcUnion(Bx,Br,L).
	
%- axiom(F) :- 
%-  pfcGetSupport(F,(user,user)); 
%-  pfcGetSupport(F,(god,god)).

axiom(F) :- 
 umt(((pfcGetSupport(F,UU),
   \+ \+ is_axiom_support(UU)))).

current_why_UU(UU):- get_source_ref(UU).
%current_why_UU((user,user)).

%is_axiom_support(UU):- current_why_UU(UU).
is_axiom_support((_,AX)):- atomic(AX).


%% an assumption is a failed goal, i.e. were assuming that our failure to 
%% prove P is a proof of not(P)

assumption(P) :- pfc_unnegate(P,_).
   
%% assumptions(X,As) if As is a set of assumptions which underly X.

assumptions(X,[X]) :- assumption(X).
assumptions(X,[]) :- axiom(X).
assumptions(X,L) :-
  justification(X,Js),
  assumptions1(Js,L).

assumptions1([],[]).
assumptions1([X|Rest],L) :-
  assumptions(X,Bx),
  assumptions1(Rest,Br),
  pfcUnion(Bx,Br,L).  


%% pfcProofTree(P,T) the proof tree for P is T where a proof tree is
%% of the form
%%
%%     [P , J1, J2, ;;; Jn]         each Ji is an independent P justifier.
%%          ^                         and has the form of
%%          [J11, J12,... J1n]      a list of proof trees.


%% mpred_child(+P,?Q) is nondet.
%
% mpred_child(P,Q) is true iff P is an immediate justifier for Q.
%

mpred_child(P,Q) :-
  pfcGetSupport(Q,(P,_)).

mpred_child(P,Q) :-
  pfcGetSupport(Q,(_,Trig)),
  pfcType(Trig,trigger),
  mpred_child(P,Trig).

mpred_children(P,L) :- bagof(C,mpred_child(P,C),L).

% pfcDescendant(P,Q) is true iff P is a justifier for Q.

pfcDescendant(P,Q) :- 
   pfcDescendant1(P,Q,[]).

pfcDescendant1(P,Q,Seen) :-
  mpred_child(X,Q),
  (\+ member(X,Seen)),
  (P=X ; pfcDescendant1(P,X,[X|Seen])).
  
pfcDescendants(P,L) :- 
  bagof(Q,pfcDescendant1(P,Q,[]),L).

%%
%%
%% predicates for manipulating support relationships
%%
:- module(pfcsupport,[ifNotDMiles/1,ifNotDMiles/2]).


:- use_module(library(pfc_pack_xform)).

:- if(false).
% NON-DMILES
:- dynamic support1/3.
:- dynamic support2/3.
:- dynamic support3/3.
ifNotDMiles(G):- G.
ifNotDMiles(G,_):- G.

:- else.

% DMILES
:- dynamic spft/3.
support1(P,Fact,Trigger):-umt(spft(P,Fact,Trigger)).
support2(Fact,Trigger,P):-umt(spft(P,Fact,Trigger)).
support3(Trigger,P,Fact):-umt(spft(P,Fact,Trigger)).

ifNotDMiles(_).
ifNotDMiles(_,G):- G.

:- endif.


%% pfcAddSupport(+Fact,+Support)

pfcAddSupport(P,(Fact,Trigger)) :- umt(clause_asserted(spft(P,Fact,Trigger))),!,dmsg(tWICE_pfcAddSupport(P,(Fact,Trigger))),!.
pfcAddSupport(P,(Fact,Trigger)) :-
  show_call(assert_u(spft(P,Fact,Trigger))),!,
  nop(ifNotDMiles(assert(support2(Fact,Trigger,P)))),
  nop(ifNotDMiles(assert(support3(Trigger,P,Fact)))),!.

pfcGetSupport(P,(F,T)):- !, umt((spft(P,F,T))).

pfcGetSupport(P,FT):- umt((pfcGetSupport0(P,FT))).

pfcGetSupport(P,(Fact,Trigger)) :-
   nonvar(P)         -> support1(P,Fact,Trigger) 
   ; nonvar(Fact)    -> support2(Fact,Trigger,P) 
   ; nonvar(Trigger) -> support3(Trigger,P,Fact) 
   ; otherwise       -> support1(P,Fact,Trigger).


% There are three of these to try to efficiently handle the cases
% where some of the arguments are not bound but at least one is.

pfcRemSupport(P,(Fact,Trigger)) :-
  nonvar(P),
  !,
  pfcRetractOrWarn(spft(P,Fact,Trigger)),
  ifNotDMiles(pfcRetractOrWarn(support2(Fact,Trigger,P))),
  ifNotDMiles(pfcRetractOrWarn(support3(Trigger,P,Fact))).


pfcRemSupport(P,(Fact,Trigger)) :-
  nonvar(Fact),
  !,
  ifNotDMiles(pfcRetractOrWarn(support2(Fact,Trigger,P)),support2(Fact,Trigger,P)),
  pfcRetractOrWarn(spft(P,Fact,Trigger)),
  ifNotDMiles(pfcRetractOrWarn(support3(Trigger,P,Fact))).

pfcRemSupport(P,(Fact,Trigger)) :-
  ifNotDMiles(pfcRetractOrWarn(support3(Trigger,P,Fact)),support3(Trigger,P,Fact)),
  pfcRetractOrWarn(spft(P,Fact,Trigger)),
  ifNotDMiles(pfcRetractOrWarn(support2(Fact,Trigger,P))).


pfc_collect_supports(Tripples) :-
  bagof(Tripple, pfc_support_relation(Tripple), Tripples),
  !.
pfc_collect_supports([]).

pfc_support_relation((P,F,T)) :-
  umt((support1(P,F,T))).

pfc_make_supports((P,S1,S2)) :- 
  pfcAddSupport(P,(S1,S2)),
  (pfcAdd(P); true),
  !.

%% pfcTriggerKey(+Trigger,-Key) 
%%
%% Arg1 is a trigger.  Key is the best term to index it on.

pfcTriggerKey(pt(Key,_),Key).
% unused? pfcTriggerKey(pt(Key,_,_),Key).
pfcTriggerKey(nt(Key,_,_),Key).
pfcTriggerKey(Key,Key).


%%^L
%% Get a key from the trigger that will be used as the first argument of
%% the trigger base clause that stores the trigger.
%%

pfc_trigger_key(X,X) :- var(X), !.
pfc_trigger_key(chart(word(W),_L),W) :- !.
pfc_trigger_key(chart(stem([Char1|_Rest]),_L),Char1) :- !.
pfc_trigger_key(chart(Concept,_L),Concept) :- !.
pfc_trigger_key(X,X).

:- fixup_exports.
%   File   : pfcwhy.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Updated:
%   Purpose: predicates for interactively exploring Pfc justifications.

end_of_file.

:- module(pfcwhy, []).
:- use_module(library(pfc_pack_xform)).

% ***** predicates for brousing justifications *****

:- use_module(library(lists)).

:- thread_local(t_l:whybuffer/2).

pfcWhy :- 
 umt((
  t_l:whybuffer(P,_),
  mpred_why0(P))).
% see pfc_why
mpred_why(X):- source_file(_,_), % non-interactive
  color_line(green,2),
  forall(no_repeats(P-Js,justifications(P,Js)),
    (color_line(yellow,1),mpred_showJustifications(X,Js))),
  color_line(green,2),!.
  

mpred_why(X):-
  umt((mpred_why0(X))).

mpred_why0(N) :-
  number(N),
  !,
  t_l:whybuffer(P,Js),
  mpred_whyCommand0(N,P,Js).

mpred_why0(P) :-
  justifications(P,Js),
  retractall(t_l:whybuffer(_,_)),
  assert(t_l:whybuffer(P,Js)),
  mpred_whyBrouse(P,Js).

mpred_why1(P) :-
  justifications(P,Js),
  mpred_whyBrouse(P,Js).

mpred_whyBrouse(P,Js) :-
  mpred_showJustifications(P,Js),
  ttyflush,
  read_pending_chars(current_input,_,[]),!,
  ttyflush,
  % pfcAsk(' >> ',Answer),
  % read_pending_chars(current_input,[Answer|_],[]),!,  
  format('~N',[]),write('proof [q/h/u/?.?]: '),get_char(Answer),
  mpred_whyCommand0(Answer,P,Js).

mpred_whyCommand0(q,_,_) :- !.
mpred_whyCommand0(h,_,_) :- 
  !,
  format("~n
Justification Brouser Commands:
 q   quit.
 N   focus on Nth justification.
 N.M brouse step M of the Nth justification
 u   up a level
",[]).

mpred_whyCommand0(N,_P,Js) :-
  float(N),
  !,
  mpred_selectJustificationNode(Js,N,Node),
  mpred_why1(Node).

mpred_whyCommand0(u,_,_) :-
  % u=up
  !.

mpred_whyCommand0(N,_,_) :-
  integer(N),
  !,
  format("~n~w is a yet unimplemented command.",[N]),
  fail.

mpred_whyCommand0(X,_,_) :-
 format("~n~w is an unrecognized command, enter h. for help.",[X]),
 fail.
  
mpred_showJustifications(P,Js) :-
  format("~nJustifications for ~w:",[P]),
  mpred_showJustification1(Js,1).

mpred_showJustification1([],_).

mpred_showJustification1([J|Js],N) :-
  % show one justification and recurse.
  nl,
  mpred_showJustifications2(J,N,1),
  N2 is N+1,
  mpred_showJustification1(Js,N2).

mpred_showJustifications2([],_,_).

mpred_showJustifications2([C|Rest],JustNo,StepNo) :- 
  copy_term(C,CCopy),
  numbervars(CCopy,0,_),
  format("~n    ~w.~w ~w",[JustNo,StepNo,CCopy]),
  StepNext is 1+StepNo,
  mpred_showJustifications2(Rest,JustNo,StepNext).

pfcAsk(Msg,Ans) :-
  format("~n~w",[Msg]),
  read(Ans).

mpred_selectJustificationNode(Js,Index,Step) :-
  JustNo is integer(Index),
  nth1(JustNo,Js,Justification),
  StepNo is 1+ integer(Index*10 - JustNo*10),
  nth1(StepNo,Justification,Step).
 



