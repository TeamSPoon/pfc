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

:- kb_shared(never_assert_u/1).
:- kb_shared(never_assert_u/2).
:- kb_shared(never_retract_u/1).
:- kb_shared(never_retract_u/2).
:- kb_shared(predicateConventionMt/2).
:- kb_shared(prologOnly/1).
:- kb_shared(functorIsMacro/1).
:- kb_shared(pfcControlled/1).
:- kb_shared(arity/2).
:- kb_shared(tSet/1).
:- kb_shared(feature_setting/2).



% :- kb_local( ('~') /1).

:- kb_shared(col_as_unary/1).  % never used for arg2 of isa/2

:- kb_shared(prologHybrid/1).
:- kb_shared(startup_option/2).
:- kb_shared(tooSlow/0).
:- kb_shared(rtAvoidForwardChain/1).

:- kb_shared(meta_argtypes/1).
:- kb_shared(type_checking/0).
:- kb_shared(mpred_prop/3).
:- kb_shared(ttRelationType/1).
:- kb_shared(comment/2).
:- kb_shared(mudToCyc/2).
:- kb_shared(mtExact/1).

:- kb_shared(tCol/1).
:- kb_shared(quotedIsa/2).

:- forall(between(1,11,A),kb_shared(t/A)).

:- meta_predicate t(*,?).
:- meta_predicate t(*,?,?).
:- meta_predicate t(*,?,?,?).
:- meta_predicate t(*,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?,?,?).

%:- asserta(elmt:elmt_is_a_module).
%:- forall(between(4,9,N),kb_shared(elmt:exactlyAssertedELMT/N)).


% :- listing(ttRelationType/1).

% :- kb_local(do_and_undo/2).

do_and_undo(A,U):-cwc,atom(A),atom_concat('assert',Suffix,A),!,atom_concat('delete',Suffix,U),current_predicate(U/_).
do_and_undo(A,U):-cwc,atom(A),atom_concat('def',_,A),atom_concat('un',A,U),current_predicate(U/_).
do_and_undo(A,U):-cwc,strip_module(A,M,P),compound(P),P=..[F|ARGS],lookup_u(do_and_undo(F,UF)),UA=..[UF|ARGS], U = (M:UA).
ll:- cwc,call(listing,[isa/2,mtCycL/1,col_as_unary/1, tRRP2/1,tRR/1,tRRP/1]). % ttTypeType,


:- mpred_notrace_exec.

arity(arity,2).
arity(functorIsMacro,1).
functorIsMacro(functorIsMacro).
tSet(F)==>functorDeclares(F).
functorDeclares(Decl)==>functorIsMacro(Decl).
~tCol(functorDeclares).

((prologHybrid(F),arity(F,A))==>{kb_local(F/A)}).
tSet(F)==> ({kb_shared(F/1)},arity(F,1),prologHybrid(F)).

:- dynamic(baseKB:ttTypeType/1).
:- kb_shared(ttTypeType/1).
tSet(ttTypeType).
tSet(ttExpressionType).

ttTypeType(F)==>tSet(F).
ttTypeType(ttTypeType).



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

                  prologNegByFailure,
                  prologIsFlag,

                  rtArgsVerbatum,
                  prologSideEffects,
                  rtNotForUnboundPredicates,
                  rtAvoidForwardChain,
                  rtSymmetricBinaryPredicate,
                  predCanHaveSingletons,

                  pfcControlled,  % pfc decides when to forward and backchain this pred
                  pfcWatches,   % pfc needs to know about new assertions
                  pfcCreates,   % pfc asserts 

                  pfcCallCode,  % called as prolog
                  pfcCallCodeAnte,   % called as prolog

                  pfcNegTrigger,
                  pfcPosTrigger,
                  pfcBcTrigger,
                  pfcRHS,
                  pfcLHS)).

:- sanity(ttRelationType(prologMultiValued)).

:- scan_missed_source.

:- mpred_notrace_exec.

genls(prologSideEffects,rtNotForUnboundPredicates).

ttRelationType(RT)==> { kb_shared(RT/1), decl_rt(RT) },tSet(RT),completelyAssertedCollection(RT).
% ttRelationType(RT) ==> ( ~genls(RT,tFunction) <==> genls(RT,tPred)).

ttRelationType(tFunction).
ttRelationType(tPred).
completelyAssertedCollection(tRelation).
completelyAssertedCollection(tPred).
completelyAssertedCollection(tFunction).

hybrid_support(P,A)==> {kb_shared(F/A)}.


pfcControlled(P),arity(P,A)==>hybrid_support(P,A).
ttRelationType(X)/sanity(atom(X))==>(arity(X,1),pfcControlled(X)).

ttTypeType(C)==>completelyAssertedCollection(C).
completelyAssertedCollection(ttTypeType).
% (isa(Inst,Type), tCol(Inst)) ==> isa(Type,ttTypeType).

% tCols are either syntactic or existential
completelyAssertedCollection(ttExpressionType).  % syntactic
completelyAssertedCollection(tSet). % existential

%ttExpressionType(T)==>completelyDecidableCollection(T).

% relations are predsor functions
completelyAssertedCollection(tRelation).
completelyAssertedCollection(tPred).
completelyAssertedCollection(tFunction).

completelyAssertedCollection(functorIsMacro).

completelyAssertedCollection(tPred).
~completelyAssertedCollection(meta_argtypes).
completelyAssertedCollection(tTemporalThing).
completelyAssertedCollection(tInferInstanceFromArgType).
completelyAssertedCollection(ttNotTemporalType).
completelyAssertedCollection(ttSpatialType).
completelyAssertedCollection(ttTemporalType).
completelyAssertedCollection(ttTypeType).
completelyAssertedCollection(ttUnverifiableType).

tSet(rtNotForUnboundPredicates).
tSet(tPred).
tSet(tRelation).
tSet(prologBuiltin).
tSet(tFunction).
tSet(ttTemporalType).
tSet(functorIsMacro).

tPred(P) :- cwc, tRelation(P), \+ tFunction(P).

(((tRelation(P), \+ tFunction(P)) ==> tPred(P))).

rtArgsVerbatum(mpred_prop).
rtArgsVerbatum(listing).

rtNotForUnboundPredicates(~).
rtNotForUnboundPredicates(t).
rtNotForUnboundPredicates(call).

:- kb_shared(disjointWith/2).
rtSymmetricBinaryPredicate(disjointWith).

ttRelationType(compilerDirective).
compilerDirective(F)==>{kb_local(F/0)}.

:- kb_shared(hardCodedExpansion/0).
compilerDirective(hardCodedExpansion,comment("Is Already Implemented From Code")).
:- kb_shared(codeTooSlow/0).
compilerDirective(codeTooSlow,comment("A faster more incomplete version is filling in for it")).


compilerDirective(type_checking,comment("Probably not needed at first")).
compilerDirective(disjoint_type_checking,comment("Typecheck semantics")).
compilerDirective(pass2,comment("Probably not needed at first")).
compilerDirective(tooSlow,comment("eeded at first")).
compilerDirective(redundantMaybe,comment("Probably redundant")).
compilerDirective(isRedundant,comment("Redundant")).
compilerDirective(isRuntime,comment("Only use rule at runtime")).

% @TODO decide how to best impl the next line

% propagate and query swapped args - @TODO find a way to enforce as last pred
rtSymmetricBinaryPredicate(F)==> {fxy_args_swapped(F,X,Y,P1,P2),nop(was_singleton(X,Y))}, 
                                                                % ( P1 ==>{loop_check(mpred_fwc1( P2),true)}),
                                                                % (~P1 ==>{loop_check(mpred_fwc1(~P2),true)}),
                                                                  ( P1/ (X @< Y) ==>{mpred_fwc1( P2)}),
                                                                  (~P1/ (X @< Y) ==>{mpred_fwc1(~P2)}),
                                                                  (~P1:- loop_check(~P2)),
                                                                  ( P1:- loop_check( P2)).



:- kb_shared(mpred_prop/3).

% ==> type_checking.



/*
% catching of misinterpreations
type_checking ==> (mpred_prop(F,A,pfcPosTrigger)==>{warn_if_static(F,A)}).
type_checking ==> (mpred_prop(F,A,pfcNegTrigger)==>{warn_if_static(F,A)}).
type_checking ==> (mpred_prop(F,A,pfcBcTrigger)==>{warn_if_static(F,A)}).
*/

prop_mpred(pfcCreates,F,A)==> {kb_local(F/A)}.
prop_mpred(pfcControlled,F,A)==> {kb_local(F/A)}.

mpred_prop(F,A,pfcPosTrigger)/(\+ ground(F/A))==>{trace_or_throw(mpred_prop(F,A,pfcPosTrigger))}.
mpred_prop(F,A,pfcPosTrigger)==>prop_mpred(pfcWatches,F,A).
mpred_prop(F,A,pfcNegTrigger)==>prop_mpred(pfcWatches,F,A).
mpred_prop(F,A,pfcBcTrigger)==>prop_mpred(pfcCreates,F,A).
mpred_prop(F,A,pfcLHS)==>arity(F,A),functorIsMacro(F),prop_mpred(pfcWatches,F,A).
/*mpred_prop(F,A,pfcRHS)==>
  {functor(P,F,A),notrace(make_dynamic(P)),kb_shared(F/A),
    create_predicate_istAbove(abox,F,A)},
    prop_mpred(pfcCreates,F,A).*/
mpred_prop(F,A,pfcRHS)==> {kb_local(F/A)}.
mpred_prop(F,A,pfcLHS)==> {kb_local(F/A)}.



mpred_prop(F,A,pfcCallCode)/predicate_is_undefined_fa(F,A)
    ==> prop_mpred(needsDefined,F,A).
/*
mpred_prop(F,A,pfcCallCodeAnte)/predicate_is_undefined_fa(F,A)
    ==> prop_mpred(pfcWatches,F,A).
*/

genls(pfcRHS,pfcControlled).


%:- meta_predicate(mp_test_agr(?,+,-,*,^,:,0,1,5,9)).
%mp_test_agr(_,_,_,_,_,_,_,_,_,_).
%:- mpred_test(predicate_property(mp_test_agr(_,_,_,_,_,_,_,_,_,_),meta_predicate(_))).
% becomes         mp_test_agr(+,+,-,?,^,:,0,1,0,0)


%((prop_mpred(pfcWatches,F,A)/is_ftNameArity(F,A),prologHybrid(F)))==>prop_mpred(pfcVisible,F,A).





%% completelyAssertedCollection( ?VALUE1) is semidet.
%
% Completely Asserted Collection.
%

completeExtentAsserted(functorIsMacro).
completelyAssertedCollection(completeExtentAsserted).
mpred_database_term(F,_,_)==>completeExtentAsserted(F).
prologNegByFailure(prologNegByFailure).

completelyAssertedCollection(functorIsMacro).  % Items read from a file might be a special Macro Head
completelyAssertedCollection(ttRelationType).  % Or they might be a predciate declarer
% completelyAssertedCollection(functorDeclares).  % or they might declare other things
% completelyAssertedCollection(functorIsMacro).  % or they might declare other things




~(singleValuedInArg(arity,2)).
~(prologSingleValued(arity)).

==> nondet.


%% ~( ?VALUE1) is semidet.
%
%

~(tCol('$VAR')).
((~(G):-  (cwc, neg_in_code(G)))).

:- kb_shared(warningsAbout/2).

prologHybrid(warningsAbout/2,rtArgsVerbatum).
warningsAbout(Msg,Why)==>{wdmsg(error(warningsAbout(Msg,Why))),break}.

%% t( ?CALL) is semidet.
%
% True Structure.
%
:- kb_shared(t/1).
%t([P|LIST]):- cwc, !,mpred_plist_t(P,LIST).
%t(naf(CALL)):- cwc, !,not(t(CALL)).
%t(not(CALL)):- cwc, !,mpred_f(CALL).
t(CALL):- cwc, call(into_plist_arities(3,10,CALL,[P|LIST])),mpred_plist_t(P,LIST).


%% t( ?VALUE1, ?VALUE2) is semidet.
%
% True Structure.
%
:- kb_shared(t/2).
((t(T,I):- cwc, I==T,completelyAssertedCollection==I,!)).
((t(T,I):- cwc, I==T,completeExtentAsserted==I,!)).
((t(T,I):- ((cwc, I==T,ttExpressionType==I,!,fail)))).
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


% :- rtrace((ain_expanded(tCol(tCol)))).

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

arity(alwaysGaf,1).
alwaysGaf(alwaysGaf).
alwaysGaf(pfcRHS).
alwaysGaf(pfcLHS).

%arity('$VAR',_).
arity(is_never_type,1).
%arity(prologSingleValued,1).
%arity(Prop,1):- cwc, clause_b(ttRelationType(Prop)).
arity(meta_argtypes,1).
arity(F,A):- cwc, is_ftNameArity(F,A), current_predicate(F/A),A>1.
arity(F,1):- cwc, tCol(F). % current_predicate(F/1)).  % is_ftNameArity(F,1), , (col_as_unary(F);ttTypeType(F)), \+((call((dif:dif(Z,1))), arity(F,Z))).


ttExpressionType(ftCallable).
ttExpressionType(ftString).
ttExpressionType(ftAtom).
ttExpressionType(ftProlog).

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
rtArgsVerbatum(meta_argtypes).
rtArgsVerbatum(ruleRewrite).
rtArgsVerbatum(mpred_action).
rtArgsVerbatum(mpred_prop).
rtArgsVerbatum(ain).
rtArgsVerbatum(mpred_rem).
rtArgsVerbatum(added).
rtArgsVerbatum(call).
rtArgsVerbatum(call_u).
rtArgsVerbatum(member).
rtArgsVerbatum( <- ).
rtArgsVerbatum(=..).
% rtArgsVerbatum({}). % Needs mpred_expansion to visit
rtArgsVerbatum(second_order).
rtArgsVerbatum(ftSpec).
rtArgsVerbatum(vtActionTemplate).
% rtArgsVerbatum((':-')).




meta_argtypes(support_hilog(tRelation,ftInt)).


% genlPreds(support_hilog,arity).


((codeTooSlow,((tPred(F),
 arity(F,A)/
  (is_ftNameArity(F,A),A>1, 
      \+ prologBuiltin(F), 
      % sanity(mpred_must(\+ arity(F,1))),
      sanity(mpred_must(\+ tCol(F)))))) )
   ==> (~(tCol(F)),support_hilog(F,A))).

:- kb_shared(support_hilog/2).

/*
((codeTooSlow,(support_hilog(F,A)
  /(is_ftNameArity(F,A),
    \+ is_static_predicate(F/A), \+ prologDynamic(F)))) ==>
   (prop_mpred(pfcVisible,F,A), 
    {% functor(Head,F,A) ,Head=..[F|TTs], TT=..[t,F|TTs],
    %  (CL = (Head :- cwc, call(second_order(TT,CuttedCall)), ((CuttedCall=(C1,!,C2)) -> (C1,!,C2);CuttedCall)))
    CL = arity(F,A)
    },
   (CL))).
*/


%:- kb_shared(hybrid_support/2).
%prologBuiltin(resolveConflict/1).

% :- kb_local(bt/2).
bt(P,_)/nonvar(P) ==> (P:- mpred_bc_only(P)).

%redundantMaybe ==> ((prologHybrid(F),arity(F,A))==>prop_mpred(pfcVisible,F,A)).
%redundantMaybe ==> (prop_mpred(pfcVisible,F,A)==>prologHybrid(F),arity(F,A)).

% ((mpred_prop(F,A,pfcRHS)/(A\=0)) ==> {kb_local(F/A)}).
% ((mpred_prop(F,A,_)/(A\=0)) ==> {kb_local(F/A)}).

% pfcMustFC(F) ==> pfcControlled(F).
genls(pfcMustFC, pfcControlled).

% pfcControlled(C)==>prologHybrid(C).
genls(pfcControlled, prologHybrid).


do_and_undo(mpred_post_exactly,mpred_remove_exactly).




:- mpred_notrace_exec.


:- meta_predicate(without_depth_limit(0)).
without_depth_limit(G):- call_with_depth_limit(G,72057594037927935,Result),sanity(Result\==depth_limit_exceeded).
:- scan_missed_source.


:- kb_shared(startup_option/2).

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
% Type checker system / Never Assert / Retraction checks
% ===================================================================

type_checking ==> (( typeCheckDecl(Each,Must), Each, {\+ Must}) ==> failed_typeCheckDecl(Each,Must)).

failed_typeCheckDecl(Each,Must)==>{trace_or_throw(failed_typeCheckDecl(Each,Must))}.

never_assert_u(vtVerb(BAD),vtVerbError):- BAD=='[|]'.
never_assert_u(prologSingleValued(BAD),var_prologSingleValued(BAD)):-is_ftVar(BAD).

never_assert_u(baseKB:mtProlog(baseKB),must(mtCycL(baseKB))).
never_assert_u(meta_argtypes(tSet(ftAssertable)),badRules).


never_assert_u(A,test_sanity(A)):- never_assert_u(A).



:- kb_shared(never_retract_u/1).
:- kb_shared(never_retract_u/2).
never_retract_u(~(X),is_ftVar(X)):- cwc, is_ftVar(X).
never_retract_u(A,test_sanity(A)):- cwc, never_retract_u(A).
never_retract_u(X,is_ftVar(X)):- cwc, is_ftVar(X).
% P/never_assert_u(P,Why) ==> conflict(never_assert_u(P,Why))

prologHybrid(arity/2).
prologDynamic(is_never_type/1).
prologDynamic(term_expansion/2).
prologBuiltin(var/1).

