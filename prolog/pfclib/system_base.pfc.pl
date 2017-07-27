:- module(system_base_lite,[]).
:- set_module(class(development)).
%:- mpred_unload_file.
:- '$set_source_module'(baseKB).
:- ensure_abox(baseKB).
:- use_module(library(rtrace)).
:- use_module(library(pfc_lib)).
/** <module> system_base_lite
% =============================================
% File 'system_base_lite.pfc'
% Purpose: Agent Reactivity for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface' 1.0.0
% Revision: $Revision: 1.9 $
% Revised At: $Date: 2002/06/27 14:13:20 $
% =============================================
%
%  PFC is a language extension for prolog.. there is so much that can be done in this language extension to Prolog
%
%
% props(Obj,[height(ObjHt)]) == t(height,Obj,ObjHt) == rdf(Obj,height,ObjHt) == t(height(Obj,ObjHt)).
% pain(Obj,[height(ObjHt)]) == prop_set(height,Obj,ObjHt,...) == ain(height(Obj,ObjHt))
% [pdel/pclr](Obj,[height(ObjHt)]) == [del/clr](height,Obj,ObjHt) == [del/clr]svo(Obj,height,ObjHt) == [del/clr](height(Obj,ObjHt))
% keraseall(AnyTerm).
%
%                      ANTECEEDANT                                   CONSEQUENT
%
%         P =         test nesc true                         assert(P),retract(~P) , enable(P).
%       ~ P =         test nesc false                        assert(~P),retract(P), disable(P)
%
%   ~ ~(P) =         test possible (via not impossible)      retract( ~(P)), enable(P).
%  \+ ~(P) =         test impossiblity is unknown            retract( ~(P))
%   ~ \+(P) =        same as P                               same as P
%     \+(P) =        test naf(P)                             retract(P)
%
% Dec 13, 2035
% Douglas Miles
*/

:- set_prolog_flag(runtime_debug, 1). % 2 = important but dont sacrifice other features for it

:- if((current_prolog_flag(runtime_debug,D),D>1)).
:- '$def_modules'([clause_expansion/2],O),dmsg(O),nl.
:- make:list_undefined([]).
:- endif.

:- sanity(is_pfc_file).


% :- kb_local( ('~') /1).
:- kb_shared(arity/2).
:- kb_shared(col_as_unary/1).  % never used for arg2 of isa/2
:- kb_shared(comment/2).
:- kb_shared(feature_setting/2).
:- kb_shared(functorIsMacro/1).
:- kb_shared(hybrid_support/2).
:- kb_shared(mpred_prop/3).
:- kb_shared(mtExact/1).
:- kb_shared(never_assert_u/1).
:- kb_shared(never_assert_u/2).
:- kb_shared(never_retract_u/1).
:- kb_shared(never_retract_u/2).
:- kb_shared(pfcControlled/1).
:- kb_shared(predicateConventionMt/2).
:- kb_shared(prologHybrid/1).
:- kb_shared(prologOnly/1).
:- kb_shared(rtAvoidForwardChain/1).
:- kb_shared(tooSlow/0).
:- kb_shared(ttRelationType/1).

% :- forall(between(1,11,A),kb_shared(t/A)).

:- meta_predicate t(*,?).
:- meta_predicate t(*,?,?).
:- meta_predicate t(*,?,?,?).
:- meta_predicate t(*,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?,?,?).



% ===================================================================
%  Microtheory System
% ===================================================================

%((ttTypeType(TT),abox:isa(T,TT))==>tSet(T)).
%tSet(T)==>functorDeclares(T).
:- kb_shared(functorDeclares/1).
:- kb_shared(mtHybrid/1).
:- kb_shared(mtProlog/1).
:- kb_shared(mtNonAssertable/1).
:- kb_shared(predicateConventionMt/2).
:- kb_shared(genlMt/2).


(genlMt(C,P) ==> {decl_assertable_module(C),decl_assertable_module(P)}).
%(genlMt(C,P),mtProlog(C) ==> {decl_assertable_module(C),add_import_module(C,P,end)}).
%(genlMt(C,P),mtProlog(P) ==> {decl_assertable_module(C),add_import_module(C,P,end)}).
(genlMt(C,P) ==> {decl_assertable_module(C),add_import_module(C,P,end)}).
(mtHybrid(C) ==> {decl_assertable_module(C),ensure_abox(C)}).
% (mtProlog(C) ==> {decl_assertable_module(C)}).
predicateConventionMt(genlMt,baseKB).
predicateConventionMt(predicateConventionMt,baseKB).
predicateConventionMt(mtHybrid,baseKB).
predicateConventionMt(mtProlog,baseKB).
predicateConventionMt(mtNonAssertable,baseKB).
(predicateConventionMt(F,MT),arity(F,A))==>{kb_shared(MT:F/A)}.

ttRelationType(RT)==>predicateConventionMt(RT,baseKB).

%:- install_constant_renamer_until_eof.

 % :- mpred_trace_exec.
ttTypeType(ttModuleType,mudToCyc('MicrotheoryType')).

==>ttModuleType(tSourceCode,mudToCyc('tComputerCode'),comment("Source code files containing callable features")).
==>ttModuleType(tSourceData,mudToCyc('iboPropositionalInformationThing'),comment("Source data files containing world state information")).
:- mpred_notrace_exec.


typeGenls(ttModuleType,tMicrotheory).



%:- kb_shared( ('~') /1).

ttTypeType(ttTypeType).
ttTypeType(ttRelationType).
ttTypeType(TT)==>functorDeclares(TT).
ttRelationType(RT)==> { decl_rt(RT) },functorDeclares(RT).
%functorDeclares(RT)==>{kb_shared(RT/1)},arity(RT,1),prologHybrid(RT),functorIsMacro(RT).
functorDeclares(RT)==>{kb_local(RT/1)},arity(RT,1),prologHybrid(RT),functorIsMacro(RT).
% ttRelationType(RT) ==> ( ~genlPreds(RT,tFunction) <==> genlPreds(RT,tPred)).


ttRelationType(compilerDirective).
% compilerDirective(F)==>{kb_local(F/0)}.
compilerDirective(F)==>{kb_shared(F/0)}.

compilerDirective(hardCodedExpansion,comment("Is Already Implemented From Code")).
compilerDirective(codeTooSlow,comment("A faster more incomplete version is filling in for it")).
compilerDirective(pfc_checking,comment("Checks for common Pfc Errors")).
compilerDirective(pass2,comment("Probably not needed at first")).
compilerDirective(tooSlow,comment("Slow and Probably not needed at first")).
compilerDirective(redundantMaybe,comment("Probably redundant")).
compilerDirective(isRedundant,comment("Redundant")).
compilerDirective(isRuntime,comment("Only use rule/fact at runtime")).

==> ttRelationType(isEach(
                  prologBuiltin,
                  prologDynamic,
                  prologHybrid,

                  prologKIF,
                  prologPTTP,
                  pfcMustFC, 

                  prologListValued,
                  prologMultiValued,
                  prologSingleValued,
                  prologOrdered,

                  prologEquality,


                  rtArgsVerbatum,
                  prologSideEffects,
                  rtNotForUnboundPredicates,
                  rtAvoidForwardChain,
                  rtSymmetricBinaryPredicate,
                  predCanHaveSingletons,
                  pfcControlled,  % pfc decides when to forward and backchain this pred
/*
                  
                  pfcWatches,   % pfc needs to know about new assertions
                  pfcCreates,   % pfc asserts 

                  pfcCallCode,  % called as prolog
                  pfcCallCodeAnte,   % called as prolog

                  pfcNegTrigger,
                  pfcPosTrigger,
                  pfcBcTrigger,
                  pfcRHS,
                  pfcLHS,
*/
                  prologNegByFailure,
                  prologIsFlag

                  )).


% :- listing(ttRelationType/1).

:- kb_local(do_and_undo/2).

do_and_undo(A,U):-cwc,atom(A),atom_concat('assert',Suffix,A),!,atom_concat('delete',Suffix,U),current_predicate(U/_).
do_and_undo(A,U):-cwc,atom(A),atom_concat('def',_,A),atom_concat('un',A,U),current_predicate(U/_).
do_and_undo(A,U):-cwc,strip_module(A,M,P),compound(P),P=..[F|ARGS],lookup_u(do_and_undo(F,UF)),UA=..[UF|ARGS], U = (M:UA).
ll:- cwc,call(listing,[isa/2,mtHybrid/1,col_as_unary/1, tRRP2/1,tRR/1,tRRP/1]). % ttTypeType,


:- mpred_notrace_exec.

arity(arity,2).
arity(functorIsMacro,1).
functorIsMacro(functorIsMacro).

((prologHybrid(F)/arity(F,A))==>{kb_local(F/A)}).
((arity(F,A)/prologHybrid(F))==>{kb_local(F/A)}).

:- sanity(ttRelationType(prologMultiValued)).

:- scan_missed_source.

:- mpred_notrace_exec.

hybrid_support(F,A)==> {kb_local(F/A)}.


pfcControlled(P),arity(P,A)==>hybrid_support(P,A).


rtArgsVerbatum(mpred_prop).
rtArgsVerbatum(listing).

rtNotForUnboundPredicates(~).
rtNotForUnboundPredicates(t).
rtNotForUnboundPredicates(call).



:- kb_shared(mpred_prop/3).

% ==> pfc_checking.



/*
% catching of misinterpreations
*/
pfc_checking ==> (mpred_prop(F,A,pfcPosTrigger)==>{warn_if_static(F,A)}).
pfc_checking ==> (mpred_prop(F,A,pfcNegTrigger)==>{warn_if_static(F,A)}).
pfc_checking ==> (mpred_prop(F,A,pfcBcTrigger)==>{warn_if_static(F,A)}).
mpred_prop(F,A,What)/(\+ ground(F/A))==>{trace_or_throw(mpred_prop(F,A,What))}.


prop_mpred(pfcCreates,F,A)==> 
 % {functor(P,F,A),notrace(make_dynamic(P)),kb_shared(F/A),create_predicate_istAbove(abox,F,A)},
  {kb_local(F/A)},
  {warn_if_static(F,A)}.
prop_mpred(pfcControlled,F,A)==> {kb_local(F/A)}.
prop_mpred(pfcWatches,F,A)==> {kb_local(F/A)}.


mpred_prop(F,A,pfcPosTrigger)==>prop_mpred(pfcWatches,F,A).
mpred_prop(F,A,pfcNegTrigger)==>prop_mpred(pfcWatches,F,A).
mpred_prop(F,A,pfcBcTrigger)==>prop_mpred(pfcCreates,F,A).
mpred_prop(F,A,pfcLHS)==> arity(F,A),functorIsMacro(F),prop_mpred(pfcWatches,F,A).
mpred_prop(F,A,pfcRHS)==> prop_mpred(pfcCreates,F,A).



mpred_prop(F,A,pfcCallCode)/predicate_is_undefined_fa(F,A)
    ==> prop_mpred(needsDefined,F,A).
/*
mpred_prop(F,A,pfcCallCodeAnte)/predicate_is_undefined_fa(F,A)
    ==> prop_mpred(pfcWatches,F,A).
*/

genlPreds(pfcRHS,pfcControlled).

genlPreds(prologSideEffects,rtNotForUnboundPredicates).

:- kb_shared(nondet/0).
:- kb_shared(typeCheckDecl/2).

==> nondet.


%% ~( ?VALUE1) is semidet.
%
%

((~(G):-  (cwc, neg_in_code(G)))).

:- kb_shared(warningsAbout/2).

prologHybrid(warningsAbout/2,rtArgsVerbatum).
warningsAbout(Msg,Why)==>{wdmsg(error(warningsAbout(Msg,Why))),break}.

%% t( ?CALL) is semidet.
%
% True Structure.
%
%:- kb_shared(t/1).
%t([P|LIST]):- cwc, !,mpred_plist_t(P,LIST).
%t(naf(CALL)):- cwc, !,not(t(CALL)).
%t(not(CALL)):- cwc, !,mpred_f(CALL).
t(CALL):- cwc, call(into_plist_arities(3,10,CALL,[P|LIST])),mpred_plist_t(P,LIST).


%% t( ?VALUE1, ?VALUE2) is semidet.
%
% True Structure.
%
% t(C,I):- cwc,  trace_or_throw(t(C,I)),t(C,I). % ,fail,loop_check_term(isa_backchaing(I,C),t(C,I),fail).
% t(P,A1):- vwc, isa(A1,P).
t(A,B):- atom(A),!,ABC=..[A,B],call_u(ABC).
%t(A,B):- (atom(A)->true;(no_repeats(arity(A,1)),atom(A))),ABC=..[A,B],loop_check(call_u(ABC)).
%t(A,B):- call_u(call(A,B)).
t(P,A1):-  mpred_fa_call(P,1,call(P,A1)).


%% t( ?P, ?A1, ?A2) is semidet.
%
% True Structure.
%
t(P,A1,A2):- cwc,  mpred_fa_call(P,2,call(P,A1,A2)).
%t(P,A1,A2):- cwc,  call_u(t(P,A1,A2)).



%% t( ?P, ?A1, ?A2, ?A3) is semidet.
%
% True Structure.
%
t(P,A1,A2,A3):- cwc,  mpred_fa_call(P,3,call(P,A1,A2,A3)).
%t(P,A1,A2,A3):- vwc,  t(P,A1,A2,A3).


%% t( ?P, ?A1, ?A2, ?A3, ?A4) is semidet.
%
% True Structure.
%
t(P,A1,A2,A3,A4):- cwc,  mpred_fa_call(P,4,call(P,A1,A2,A3,A4)).
%t(P,A1,A2,A3,A4):- cwc,  call_u(t(P,A1,A2,A3,A4)).



%% t( :PRED5P, ?A1, ?A2, ?A3, ?A4, ?A5) is semidet.
%
% True Structure.
%
t(P,A1,A2,A3,A4,A5):- cwc,  mpred_fa_call(P,5,call(P,A1,A2,A3,A4,A5)).
%t(P,A1,A2,A3,A4,A5):- cwc,  call_u(t(P,A1,A2,A3,A4,A5)).



%% t( :PRED6P, ?A1, ?A2, ?A3, ?A4, ?A5, ?A6) is semidet.
%
% True Structure.
%
t(P,A1,A2,A3,A4,A5,A6):- cwc,  mpred_fa_call(P,6,call(P,A1,A2,A3,A4,A5,A6)).
%t(P,A1,A2,A3,A4,A5,A6):- cwc,  call_u(t(P,A1,A2,A3,A4,A5,A6)).



%% t( :PRED7P, ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7) is semidet.
%
% True Structure.
%
t(P,A1,A2,A3,A4,A5,A6,A7):- cwc,  mpred_fa_call(P,7,call(P,A1,A2,A3,A4,A5,A6,A7)).
%t(P,A1,A2,A3,A4,A5,A6,A7):- cwc,  call_u(t(P,A1,A2,A3,A4,A5,A6,A7)).

%prologHybrid(C)==>{must(callable(C))}.
%pfcControlled(C)==>{must(callable(C))}.
:- multifile(typeCheckDecl/2).
typeCheckDecl(prologHybrid(C),callable(C)).
typeCheckDecl(pfcControlled(C),callable(C)).


arity(comment,2).
:- kb_shared(singleValuedInArg/2).
:- kb_shared(rtReformulatorDirectivePredicate/1).
:- kb_shared(support_hilog/2).
:- kb_shared(mpred_undo_sys/3).
:- kb_shared(arity/2).
:- kb_shared(alwaysGaf/1).
:- kb_shared(quasiQuote/1).



arity(alwaysGaf,1).
alwaysGaf(alwaysGaf).
alwaysGaf(pfcRHS).
alwaysGaf(pfcLHS).

%arity('$VAR',_).
%arity(is_never_type,1).
%arity(prologSingleValued,1).
%arity(Prop,1):- cwc, clause_b(ttRelationType(Prop)).
arity(F,A):- cwc, is_ftNameArity(F,A), current_predicate(F/A),A>1.
arity(F,1):- cwc, ttRelationType(F). % current_predicate(F/1)).  % is_ftNameArity(F,1), , (col_as_unary(F);ttTypeType(F)), \+((call((dif:dif(Z,1))), arity(F,Z))).


arity(rtArgsVerbatum,1).
arity(quasiQuote,1).
rtArgsVerbatum(spft).


% this mean to leave terms at EL:  foo('xQuoteFn'([cant,touch,me])).

quasiQuote('xQuoteFn').

rtArgsVerbatum('with_current_why').
rtArgsVerbatum('loop_check_term').
rtArgsVerbatum('loop_check_term_key').
rtArgsVerbatum('xQuoteFn').
rtArgsVerbatum('$VAR').
rtArgsVerbatum('NART').
rtArgsVerbatum(X):-atom(X),atom_concat(_,'Fn',X).

rtArgsVerbatum(ain).
rtArgsVerbatum(ruleRewrite).
rtArgsVerbatum(mpred_action).
rtArgsVerbatum(mpred_prop).
rtArgsVerbatum(ain).
rtArgsVerbatum(mpred_rem).
rtArgsVerbatum(added).
rtArgsVerbatum(call).
rtArgsVerbatum(call_u).
rtArgsVerbatum(clause_asserted_i).
rtArgsVerbatum(member).
rtArgsVerbatum( <- ).
rtArgsVerbatum(=..).
% rtArgsVerbatum({}). % Needs mpred_expansion to visit
rtArgsVerbatum(second_order).

% rtArgsVerbatum((':-')).




:- kb_shared(support_hilog/2).



% genlPreds(support_hilog,arity).


%prologBuiltin(resolveConflict/1).

% :- kb_local(bt/2).
bt(P,_)/nonvar(P) ==> (P:- mpred_bc_only(P)).

%redundantMaybe ==> ((prologHybrid(F),arity(F,A))==>prop_mpred(pfcVisible,F,A)).
%redundantMaybe ==> (prop_mpred(pfcVisible,F,A)==>prologHybrid(F),arity(F,A)).

% ((mpred_prop(F,A,pfcRHS)/(A\=0)) ==> {kb_local(F/A)}).
% ((mpred_prop(F,A,_)/(A\=0)) ==> {kb_local(F/A)}).

% pfcMustFC(F) ==> pfcControlled(F).
genlPreds(pfcMustFC, pfcControlled).

% pfcControlled(C)==>prologHybrid(C).
genlPreds(pfcControlled, prologHybrid).


do_and_undo(mpred_post_exactly,mpred_remove_exactly).




:- mpred_notrace_exec.


:- meta_predicate(without_depth_limit(0)).
without_depth_limit(G):- call_with_depth_limit(G,72057594037927935,Result),sanity(Result\==depth_limit_exceeded).
:- scan_missed_source.



:- dynamic(mpred_undo_sys/3).
pfcControlled(mpred_undo_sys(ftAssertion, ftCallable, ftCallable)).
mpred_undo_sys(P, WhenAdded, WhenRemoved) ==> (P ==> {WhenAdded}), mpred_do_and_undo_method(WhenAdded,WhenRemoved).

% DONT mpred_undo_sys(added(P),ain(P),mpred_retract(P)).
% mpred_undo_sys(asserted(P),assert_eq_quitely(PE),retract_eq_quitely(PE)):-expand_goal(P,PE).

/*
without_depth_limit(G):-
   ('$depth_limit'(72057594037927935,Was,_), 
    (Was == -1 -> call(G);  % Not inside cwdl
    (Was > 72000000000000000 -> call(G);  % We left Depth limit slightly messed
      call_cleanup(G,'$depth_limit'(Was,_,_))))).
*/

~(singleValuedInArg(arity,2)).
~(prologSingleValued(arity)).
~(prologSingleValued(support_hilog)).


%:- rtrace,dtrace.
%==>(prologBuiltin(mpred_select_hook/1)).
% :- nortrace,quietly.

:- kb_shared(conflict/1).
% a conflict triggers a Prolog action to resolve it.
conflict(C) ==> {must(with_mpred_trace_exec((resolveConflict(C),\+conflict(C))))}.


% meta rules to schedule inferencing.
% resolve conflicts asap
mpred_select_hook(conflict(X)) :- que(conflict(X),_Why).


%tPred(t,prologDynamic).
% tPred(member/2,prologBuiltin).
rtNotForUnboundPredicates(member/2).


% ===================================================================
%  Never Assert / Retraction checks
% ===================================================================

never_assert_u(prologSingleValued(BAD),var_prologSingleValued(BAD)):-is_ftVar(BAD).

never_assert_u(baseKB:mtProlog(baseKB),must(mtHybrid(baseKB))).

never_assert_u(A,test_sanity(A)):- never_assert_u(A).



:- kb_shared(never_retract_u/1).
:- kb_shared(never_retract_u/2).
never_retract_u(~(X),is_ftVar(X)):- cwc, is_ftVar(X).
never_retract_u(A,test_sanity(A)):- cwc, never_retract_u(A).
never_retract_u(X,is_ftVar(X)):- cwc, is_ftVar(X).
% P/never_assert_u(P,Why) ==> conflict(never_assert_u(P,Why))

prologHybrid(arity/2).
prologDynamic(term_expansion/2).
prologBuiltin(var/1).

