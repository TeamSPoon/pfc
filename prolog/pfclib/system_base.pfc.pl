:- if( current_prolog_flag(xref,true) ).
:- module(system_base,[]).
:- else.
:- module(system_base,[]).
:- endif.
:- set_module(class(development)).
:- use_module(library(pfc)).
/** <module> system_base
% =============================================
% File 'system_base.pfc'
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
:- '$set_source_module'(baseKB).
:- mpred_unload_file.

:- set_prolog_flag(runtime_debug, 1). % 2 = important but dont sacrifice other features for it

:- if((current_prolog_flag(runtime_debug,D),D>1)).
:- '$def_modules'([clause_expansion/2],O),dmsg(O),nl.
:- make:list_undefined([]).
:- endif.

:- style_check(-discontiguous).
%:- set_prolog_flag(runtime_speed,0). % 0 = dont care
:- set_prolog_flag(runtime_speed, 1). % 1 = default
:- set_prolog_flag(runtime_debug, 1). % 2 = important but dont sacrifice other features for it
:- set_prolog_flag(runtime_safety, 3).  % 3 = very important
:- set_prolog_flag(unsafe_speedups, false).

:- kb_shared(tCol/1).


:- kb_shared(never_assert_u/1).
:- kb_shared(never_retract_u/1).
:- kb_shared(predicateConventionMt/2).
:- kb_shared(prologOnly/1).
:- kb_shared(functorIsMacro/1).
:- kb_shared(pfcControlled/1).
:- kb_shared(arity/2).
:- kb_shared(tSet/1).
:- kb_shared( ('~') /1).

:- kb_shared(quotedIsa/2).

:- kb_shared(col_as_unary/1).  % never used for arg2 of isa/2

:- kb_shared(meta_argtypes/1).
:- kb_shared(type_checking/0).
:- kb_shared(mpred_prop/3).
:- kb_shared(ttRelationType/1).
:- kb_shared(comment/2).
:- kb_shared(mudToCyc/2).
:- kb_shared(mtExact/1).

% :- xlisting( (==>) /2 ).

:- kb_shared(ttTypeFacet/1).
:- kb_shared(ttActionType/1). 
:- kb_shared(ttAgentType/1). 

:- kb_shared(prologHybrid/1).
:- kb_shared(startup_option/2).
:- kb_shared(argQuotedIsa/3).
:- kb_shared(ttExpressionType/1). % hard coded like: compound/1
:- kb_shared(tAtemporalNecessarilyEssentialCollectionType/1).
:- kb_shared(completelyAssertedCollection/1).
:- kb_shared(tooSlow/0).
:- kb_shared(rtAvoidForwardChain/1).
:- kb_shared(ttTypeType/1). 
:- kb_shared(typeGenls/2).
:- kb_shared(genls/2).
:- kb_shared(typeProps/2).

:- forall(between(1,11,A),kb_shared(t/A)).

:- meta_predicate t(*,?).
:- meta_predicate t(*,?,?).
:- meta_predicate t(*,?,?,?).
:- meta_predicate t(*,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?,?).
:- meta_predicate t(*,?,?,?,?,?,?,?).

:- begin_pfc.

:- mpred_notrace_exec.

arity(arity,2).
arity(functorIsMacro,1).
functorIsMacro(functorIsMacro).
functorDeclares(Decl)==>functorIsMacro(Decl).
~tCol(functorDeclares).

((prologHybrid(F),arity(F,A))==>{kb_shared(F/A)}).

% ======================================================================================= %
% Types/Sets/Collections
% ======================================================================================= %

% We assume we know our own classification system 
completelyAssertedCollection(completelyAssertedCollection).

% all completely asserted collections are finite sets
completelyAssertedCollection(A)==>tSet(A).



% tSets are part of the KR expressions language and are types of collections
(tSet(A) ==> (tCol(A), \+ ttExpressionType(A))).

% all indiviuals combined make up a set containing individuals
tSet(tIndividual).

% Types/Sets/Collections are not themselves individuals and are usable always as arity 1
% tCol(A),{sanity(atom(A))} ==> ~tIndividual(A),{decl_type(A), kb_shared(A/1)}.

~tIndividual(A):- is_ftNonvar(A), loop_check(tCol(A)).
tCol(A) ==> {decl_type(A), kb_shared(A/1)}.


% KR expressions exists outside of the logic and are types of collections
ttExpressionType(A)==> ( tCol(A), \+ tSet(A) ).

% ======================================================================================= %
% ttTypeFacet - Every type (tCol) has at least two facets below
% ======================================================================================= %
completelyAssertedCollection(ttTypeFacet).


ttTypeFacet(T)==>tSet(T).


% "Type describes aspects of types":::: 
ttTypeFacet(ttTypeType).

% "Type describes aspects of individuals (non-types)"::::
ttTypeFacet(ttIndividualType).

% Type describes a quoted expression in KR (has no finite instances)
ttTypeFacet(ttExpressionType). 

% Type describes finite instance members in KR 
ttTypeFacet(tSet).             

% New members of this type should not be deduced merely by position in a formula
ttTypeFacet(ttUnverifiableType).  

% This type exists even in impossible worlds
ttTypeFacet(tAtemporalNecessarilyEssentialCollectionType).  

% This type''s finite instance members are all known 
ttTypeFacet(completelyAssertedCollection).  

% ======================================================================================= %
% ttTypeType - Type types are disjoint from each other (facets are not)
% ======================================================================================= %
completelyAssertedCollection(ttTypeType).  % from ttTypeFacet(completelyAssertedCollection). 

% Facets for types are also type types
ttTypeType(ttTypeFacet). 

% "Facet based" type instances are known to be known
genls(ttTypeFacet,completelyAssertedCollection). 

% "if something is a type facet, then *that something* is known as set with finite members"
typeGenls(ttTypeFacet,tCol). 

% All type-types are enumerated eventually
ttTypeType(RT)==>completelyAssertedCollection(RT). 

% NOTE:  KEEP PREDS AND COLS Separate completelyAssertedCollection(RT)==>completeExtentAsserted(RT).

% ======================================================================================= %
% Sub-instance caching
% ======================================================================================= %
(typeGenls(TT,ST) ==>
  (ttTypeType(TT) , tSet(ST) , (isa(Inst,TT) ==> genls(Inst,ST)))).


tooSlow ==> (((typeGenls(SUBCOLTYPE ,SUBCOL),genls(SUBCOLTYPE,COLTYPE),typeGenls(COLTYPE ,COL)) ==>
   genls(SUBCOL,COL))).

genls(C,P) ==> (tCol(C), tCol(P)).
isa(_,C) ==> tCol(C).

tooSlow ==> ((genls(C,P)/(C\=P, \+ ttExpressionType(C) , \+ ttExpressionType(P) , \+ rtAvoidForwardChain(P) )) ==> genlsFwd(C,P)).

% (genls(C,P)/(C\=P), completelyAssertedCollection(P))  ==> genlsFwd(C,P).

tooSlow ==>  ((genlsFwd(C,P)/(C\=P) ==> ((isa(I,C) ==> isa(I,P))))).

%(\+ tooSlow) ==>  ((genls(C,P)/sanity(C\=P) ==> ((isa(I,C) ==> isa(I,P))))).
(\+ tooSlow) ==>  ((genls(C,P)/(C\=P) ==> ((isa(I,C) ==> isa(I,P))))).


tooSlow ==> 
(((genls(C1,C2), ( \+ genlsFwd(C1,C2)))==>
 ({get_functor(C1,F1),get_functor(C2,F2), F2\==F1, 
    P1 =.. [F1,X], P2 =.. [F2,X], 
   asserta_if_new(baseKB:((P2:-loop_check(P1))))}))).

% genls(ttRelationType,completelyAssertedCollection).

% ======================================================================================= %
% Instances of ttTypeType
% ======================================================================================= %
ttTypeType(TT)==>tSet(TT).

tSet(RT)==>functorDeclares(RT).
% tCol(P)==>{sanity(atom(P))},functorIsMacro(P).

% ~ ttRelationType(col_as_unary).
%ttTypeType(ttExpressionType).
%ttTypeType(ttTypeType).

:-discontiguous(completeExtentAsserted/1).
ttTypeType(ttActionType,comment("Types of actions such PostureChangingAction")).
ttTypeType(ttAgentType,comment("Types of agents such tHuman")).
ttTypeType(ttEventType,comment("Events such StartRaining")).

:- mpred_notrace_exec.

ttTypeType(ttExpressionType).
ttTypeType(ttItemType).
ttTypeType(ttMicrotheoryType).
ttTypeType(ttRegionType).
ttTypeType(ttRelationType).
ttTypeType(ttSituationType).
ttTypeType(ttSpatialType).
ttTypeType(ttTemporalType).
ttTypeType(ttTopicType).
ttTypeType(ttValueType).
% ttTypeType(ttQuantityType).
% ttTypeType(ttTypeType).
ttTypeType(ttIndividualType).

tSet(tFunction).
tSet(tPred).

% ttUnverifiableType(ftDice).
% ttUnverifiableType(ftDiceFn(ftInt,ftInt,ftInt)).
% ttUnverifiableType(ftListFn(ftTerm)).
%ttUnverifiableType(ftListFn).
:- dynamic(tItem/1).
:- dynamic(ttItemType/1).
genls(tSpatialThing,tTemporalThing).
genls(ttItemType,ttObjectType).
genls(ttObjectType,ttSpatialType).
genls(ttRegionType,ttSpatialType).

genls(ttTemporalType,ttIndividualType).
genls(tTemporalThing,tIndividual).

ttUnverifiableType(vtDirection).

typeGenls(ttRelationType,tRelation).
typeGenls(ttExpressionTypeType,ttExpressionType).
typeGenls(ttIndividualType,tIndividual).
typeGenls(ttTypeFacet,tCol).
typeGenls(ttValueType,vtValue).

typeGenls(ttSpatialType,tSpatialThing).
typeGenls(ttAgentType,tAgent).
typeGenls(ttObjectType,tObj).
typeGenls(ttRegionType,tRegion).
typeGenls(ttItemType,tItem).
tSet(tItem).

ttTypeType(TT)==>(isa(C,TT)==>tCol(C)).

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

tPred(P) :- cwc, tRelation(P), \+ tFunction(P).


:- ain(((tRelation(P), \+ tFunction(P)) ==> tPred(P))).

rtArgsVerbatum(mpred_prop).
rtArgsVerbatum(listing).

rtNotForUnboundPredicates(~).
rtNotForUnboundPredicates(t).
rtNotForUnboundPredicates(call).

:- kb_shared(disjointWith/2).
rtSymmetricBinaryPredicate(disjointWith).

ttRelationType(compilerDirective).
compilerDirective(F)==>{kb_shared(F/0)}.
compilerDirective(type_checking,comment("Probably not needed at first")).
compilerDirective(disjoint_type_checking,comment("Typecheck semantics")).

compilerDirective(pass2,comment("Probably not needed at first")).
compilerDirective(tooSlow,comment("eeded at first")).
compilerDirective(redundantMaybe,comment("Probably redundant")).
compilerDirective(isRedundant,comment("Redundant")).
compilerDirective(hardCodedExpansion,comment("Is Already Implemented From Code")).
compilerDirective(codeTooSlow,comment("A faster more incomplete version is filling in for it")).
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


disjointWith(C,D)==> tCol(C),tCol(D).

:- if(false). % true,false
:- listing(disjointWith/2).
:- listing( (~) /1).
:- mpred_notrace_exec.
:- endif.

% disjointWith(ttRegionType,ttAgentType).
% disjointWith(ttRelationType,ttTypeType).

((typeGenls(COLTYPE1,COL1),disjointWith(COL1,COL2),
  typeGenls(COLTYPE2,COL2)/dif(COLTYPE1,COLTYPE2)) ==> disjointWith(COLTYPE1,COLTYPE2)).

((typeGenls(COLTYPE1,COL1),disjointWith(COLTYPE1,COLTYPE2)/(ttTypeType(COLTYPE2)),
  typeGenls(COLTYPE2,COL2)/dif(COL1,COL2)) ==> disjointWith(COL1,COL2)).

rtArgsVerbatum(disjointPartition).
arity(disjointPartition,1).


% disjointWith(P1,P2) ==> ((~isa(C,P2):- loop_check(isa(C,P1))), (~isa(C,P1):- loop_check(isa(C,P2)))).
disjointWith(P1,P2) ==> ((~isa(C,P2):- is_ftNonvar(C),loop_check(isa(C,P1)))).

disjointWith(ttRelationType,ttTypeType).

:- if(false). % true,false
:- listing(disjointWith/2).
:- listing( ( ~ )/1).
:- mpred_notrace_exec.
:- endif.

% :- ain((disjointWith(P1,P2) , genls(C1,P1)) ==>  disjointWith(C1,P2)).
disjointWith(C1,P2):- cwc, C1\=P2,disjointWith(P1,P2),C1\=P1,genls(C1,P1),!.


% :- ain(disjointWith(P1,P2) ==> {writeln(disjointWith(P1,P2))}).

disjointPartition(
 [ttIndividualType, 
  ttTypeType, 
  ttValueType]).

(disjointPartition(List), {member(L,List),dif(L,R),member(R,List)})==> disjointWith(L,R).

:- kb_shared(warningsAbout/2).

prologHybrid(warningsAbout/2,rtArgsVerbatum).
warningsAbout(Msg,Why)==>{wdmsg(error(warningsAbout(Msg,Why))),break}.

disjoint_type_checking ==> (disjointWith(C1,C2) ==> (isa(Inst,C1)/isa(Inst,C2) ==> warningsAbout(isa(Inst,disjointWith(C1,C2)),type_checking))).

% ==> disjoint_type_checking.

disjointPartition(
 [ttActionType,
  ttAgentType, 
  ttEventType, 
  ttExpressionType, 
  ttItemType, 
  ttMicrotheoryType, 
  ttRegionType, 
  ttRelationType, 
  ttSituationType, 
  ttTopicType, 
  % ttTypeFacet,
  ttValueType]).

ttAgentType(tHuman).

:- if(false).
isa(mobAgent6,tHuman).
:- xlisting(mobAgent6).
:- endif.
/*
disjointPartition([
 ttActionType, ttEventType, ttExpressionType, ttIndividualType, ttMicrotheoryType, 
 ttAgentType,ttItemType, ttRegionType, 
  ttRelationType, ttSituationType, ttSpatialType, ttTemporalType, ttTopicType, %   ttTypeType, ttValueType]).
*/



% :- listing(ttRelationType/1).

:- kb_shared(do_and_undo/2).

do_and_undo(A,U):-cwc,atom(A),atom_concat('assert',Suffix,A),!,atom_concat('delete',Suffix,U),current_predicate(U/_).
do_and_undo(A,U):-cwc,atom(A),atom_concat('def',_,A),atom_concat('un',A,U),current_predicate(U/_).
do_and_undo(A,U):-cwc,strip_module(A,M,P),compound(P),P=..[F|ARGS],lookup_u(do_and_undo(F,UF)),UA=..[UF|ARGS], U = (M:UA).
ll:- cwc,call(listing,[isa/2,mtCycL/1,col_as_unary/1, tRRP2/1,tRR/1,tRRP/1]). % ttTypeType,


~(singleValuedInArg(arity,2)).
~(prologSingleValued(arity)).


isa(iExplorer2,C):- cwc, C==rtArgsVerbatum,!,fail.
isa(I,C):- cwc, no_repeats(loop_check(isa_backchaing(I,C))), \+ isa(C,ttExpressionType).

==> nondet.

%  % :- mpred_trace_exec.
:- mpred_notrace_exec.

:- kb_shared(mpred_prop/3).

% ==> type_checking.

:- kb_shared(hardCodedExpansion/0).


/*
% catching of misinterpreations
type_checking ==> (mpred_prop(F,A,pfcPosTrigger)==>{warn_if_static(F,A)}).
type_checking ==> (mpred_prop(F,A,pfcNegTrigger)==>{warn_if_static(F,A)}).
type_checking ==> (mpred_prop(F,A,pfcBcTrigger)==>{warn_if_static(F,A)}).
*/

prop_mpred(pfcCreates,F,A)==> {kb_shared(F/A)}.
prop_mpred(pfcControlled,F,A)==> {kb_shared(F/A)}.

mpred_prop(F,A,pfcPosTrigger)/(\+ ground(F/A))==>{trace_or_throw(mpred_prop(F,A,pfcPosTrigger))}.
mpred_prop(F,A,pfcPosTrigger)==>prop_mpred(pfcWatches,F,A).
mpred_prop(F,A,pfcNegTrigger)==>prop_mpred(pfcWatches,F,A).
mpred_prop(F,A,pfcBcTrigger)==>prop_mpred(pfcCreates,F,A).
mpred_prop(F,A,pfcLHS)==>arity(F,A),functorIsMacro(F),prop_mpred(pfcWatches,F,A).
/*mpred_prop(F,A,pfcRHS)==>
  {functor(P,F,A),notrace(make_dynamic(P)),kb_shared(F/A),
    create_predicate_istAbove(abox,F,A)},
    prop_mpred(pfcCreates,F,A).*/
mpred_prop(F,A,pfcRHS)==> {kb_shared(F/A)}.
mpred_prop(F,A,pfcLHS)==> {kb_shared(F/A)}.



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


%% ~( ?VALUE1) is semidet.
%
%

~(tCol('$VAR')).
((~(G):-  (cwc, neg_in_code(G)))).


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
t(P,A1):- cwc,  mpred_fa_call(P,1,call(P,A1)).


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


%col_as_unary(Col)==>tCol(Col).
%:- nortrace.
%:-break.

functorIsMacro(props).
functorIsMacro(tiProps).

%% mudEquals( ?X, ?Y) is semidet.
%
% Application Equals.
%

:- multifile(mudEquals/2).
:- kb_shared(mudEquals/2).
:- export(mudEquals/2).
mudEquals(X,Y):-equals_call(X,Y).




% ((prologHybrid(C),{must(callable(C)),get_functor(C,F,A),C\=F}) ==> arity(F,A)).




% :- assert_if_new((isa(I,T):- cwc, visit_isa(I,T))).

% :- mpred_notrace_exec.


:- do_gc.

%:- set_fileAssertMt(baseKB).

:- kb_shared(agent_call_command/2).
:- export(agent_call_command/2).
:- system:import(agent_call_command/2).


:- kb_shared(decided_not_was_isa/2).



% :-  abolish(yall:'/' / 2).

% :- expand_file_search_path(pack(logicmoo_nlu/prolog/pldata),X),exists_directory(X),!,assert_if_new(user:file_search_path(pldata,X)).

%^ :- ensure_loaded(logicmoo(logicmoo_plarkc)).




%:- rtrace.
%:- kb_shared(mpred_prop/3).
:- kb_shared(mpred_prop/3).
%:- nortrace.



tAtemporalNecessarilyEssentialCollectionType(ANECT)==>
       decontextualizedCollection(ANECT).


:- kb_shared(marker_supported/2).
:- kb_shared(pass2/0).
:- kb_shared(sometimesSlow/0).
:- kb_shared(sometimesBuggy/0).
:- kb_shared(redundantMaybe/0).

%interArgIsaSome(isa(tRelation,ttRelationType)).
%interArgIsaSome(isa(tAgent,ttAgentType)).
%interArgIsa1_2(isa,tAgent,ttAgentType).

% NEVER (P/mpred_non_neg_literal(P) ==> { remove_negative_version(P) } ).

%:- kb_shared(mpred_mark_C/1).
:- kb_shared(tCol/1).

:- kb_shared(subFormat/2).

:- kb_shared(singleValuedInArg/2).
:- kb_shared(rtReformulatorDirectivePredicate/1).
:- kb_shared(support_hilog/2).
:- kb_shared(mpred_undo_sys/3).
:- kb_shared(arity/2).
:- kb_shared(genlsFwd/2).
arity(comment,2).

% prologHybrid(arity/2).

:- begin_pfc.
:- sanity(get_lang(pfc)).
:- set_file_lang(pfc).
% :- mpred_ops.

arity(alwaysGaf,1).
alwaysGaf(alwaysGaf).
alwaysGaf(pfcRHS).
alwaysGaf(pfcLHS).



:- mpred_notrace_exec.


/*
Unneeded yet

ttTypeType(C)/( is_never_type(C) ; decided_not_was_isa(C,W)) ==> (conflict((ttTypeType(C)/( decided_not_was_isa(C,W);is_never_type(C))))).
*/

/*
tCol(tCol).
tCol(tPred).
% :- sanity(listing(tCol/1)).
tSet(ttTemporalType).
tSet(ttExpressionType).
*/

%ttExpressionType(ftList(ftInt)).

%:- sanity((fix_mp(clause(assert,sanity),arity(apathFn,2),M,O),M:O=arity(apathFn,2))).

:- kb_shared(ttRelationType/1).

arity(tCol,1).
arity(xyzFn,4).
arity(isKappaFn,2).
arity(isInstFn,1).
arity(ftListFn,1).
arity(argsIsa, 2).
arity(argIsa, 3).
arity(apathFn,2).
arity('<=>',2).
%arity('$VAR',_).
arity(is_never_type,1).
%arity(prologSingleValued,1).
arity(meta_argtypes,1).
%arity(Prop,1):- cwc, clause_b(ttRelationType(Prop)).
arity(F,A):- cwc, is_ftNameArity(F,A), current_predicate(F/A),A>1.
arity(F,1):- cwc, tCol(F). % current_predicate(F/1)).  % is_ftNameArity(F,1), , (col_as_unary(F);ttTypeType(F)), \+((call((dif:dif(Z,1))), arity(F,Z))).

%  % :- mpred_trace_exec.
tCol(F)==>arity(F,1).
:- mpred_notrace_exec.

/*
?- fully_expand((==> (ftSpec(ftListFn(_72012)):- cwc,callable(_72012),ftSpec(_72012))),O).

?- fully_expand_head(clause(asserta,once),(==> (ftSpec(ftListFn(_72012)):- cwc,callable(_72012),ftSpec(_72012))),O).
*/
tCol(ftListFn(Atom)):- cwc, nonvar(Atom),tCol(Atom).
ftSpec(ftListFn(Atom)):- cwc, nonvar(Atom),ftSpec(Atom).
ttExpressionType(ftListFn(Atom)):- cwc, nonvar(Atom),!,ttExpressionType((Atom)).
tSet(ftListFn(Atom)):- cwc, nonvar(Atom),!,tSet(Atom).

% :- mpred_trace_exec.
ttExpressionType(ftAssertable).
ttExpressionType(ftAskable).
ttExpressionType(ftCallable).
ttExpressionType(ftString).
ttExpressionType(ftAtom).
ttExpressionType(ftProlog).

ttTypeType(ttModuleType,mudToCyc('MicrotheoryType')).
typeGenls(ttModuleType,tMicrotheory).

arity(rtArgsVerbatum,1).
arity(quasiQuote,1).
rtArgsVerbatum(spft).


% this mean to leave terms at EL:  foo('xQuoteFn'([cant,touch,me])).

quasiQuote('xQuoteFn').

rtArgsVerbatum('loop_check_term').
rtArgsVerbatum('loop_check_term_key').
rtArgsVerbatum('xQuoteFn').
rtArgsVerbatum('$VAR').

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

:- kb_shared(codeTooSlow/0).

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

:- kb_shared(bt/2).
bt(P,_)/nonvar(P) ==> (P:- mpred_bc_only(P)).

%redundantMaybe ==> ((prologHybrid(F),arity(F,A))==>prop_mpred(pfcVisible,F,A)).
%redundantMaybe ==> (prop_mpred(pfcVisible,F,A)==>prologHybrid(F),arity(F,A)).

% ((mpred_prop(F,A,pfcRHS)/(A\=0)) ==> {kb_shared(F/A)}).
% ((mpred_prop(F,A,_)/(A\=0)) ==> {kb_shared(F/A)}).

% pfcMustFC(F) ==> pfcControlled(F).
genls(pfcMustFC, pfcControlled).

% pfcControlled(C)==>prologHybrid(C).
genls(pfcControlled, prologHybrid).



% NAUTs
tSet(tUnreifiableFunction,
genls(tFunction),
comment("
A specialization of Function-Denotational instances of which are such that their values 
are not reified in the Cyc system. More precisely, an instance of UnreifiableFunction 
is such that closed \"NA[R|U]Ts\" (see CycLNonAtomicTerm) 
built from its standard CycL name are _not_ instances of #$HLReifiedDenotationalTerm. 
Constrast with ReifiableFunction. Usually it is more efficient to make functions reifiable; 
but it is not desirable to reify every non-atomic term, such as those built from (names of) 
instances of MathematicalFunctionOnScalars. For example, it would be cumbersome to
 reify every term of the form (Inch N) that happened to appear in a CycL assertion."
)).

% NARTs
tSet(tReifiableFunction,comment("A specialization of Function-Denotational. Each instance of ReifiableFunction is denoted by a 
CycL constant that can stand in the 0th (or \"arg0\") position in a CycLReifiableNonAtomicTerm (q.v.). For example, GovernmentFn is a 
reifiable function, so the term `(GovernmentFn France)' is a reifiable non-atomic term (or \"NAT\"). And since this particular 
term actually _is_ reified in the Cyc Knowledge Base, it is, more specifically, a CycLNonAtomicReifiedTerm 
(or \"NART\"). The NART `(GovernmentFn France)' is treated more or less the same as if it were a CycL constant 
(named, say, `GovernmentOfFrance'). Similary, the constant for GovernmentFn can be applied to the constant (or other reified or 
reifiable term) for _any_ instance of GeopoliticalEntity to form a reifiable NAT that denotes that region's government; and should 
 this NAT appear in a sentence that is asserted to the KB, it will thereby become a NART. Note, however, that not all NATs are such that it 
is desireable that they should become reified (i.e. become NARTs) if they appear in assertions; for more on this see UnreifiableFunction."
),
genls(tFunction)).


tSet(vtLinguisticObject).
vtLinguisticObject(vtVerb).

tReifiableFunction(aVerbFn).
conceptuallyRelated("go",actMove).
arity(aVerbFn,1).
resultIsa(aVerbFn(ftString),vtVerb).

:- kb_shared(genls/2).


:- kb_shared( ( =@=> ) /2 ).
:- kb_shared( ( macroExpandExact ) /3 ).

:- op(1185,yfx, ( =@=> )).
tiProps(C,I)=@=>isa(I,C).
tiProps(C,I,P1)=@=>props(I,[C,P1]).
tiProps(C,I,P1,P2)=@=>props(I,[C,P1,P2]).
tiProps(C,I,P1,P2,P3)=@=>props(I,[C,P1,P2,P3]).
tiProps(C,I,P1,P2,P3,P4)=@=>props(I,[C,P1,P2,P3,P4]).

'=@=>'((I,{PreReq}),O) ==> macroExpandExact(I,PreReq,O).
('=@=>'(I,O) / (I\=(_,_))) ==> macroExpandExact(I,true,O).

% '=@=>'(I,O) ==> ('==>'(I,O)).

macroExpandExact(P,PreReq,Q) ==>
(  P, { PreReq,mpred_why(P,Why) } ==> {ignore(retract(P)),mpred_ain(Q,Why)}).


isRegisteredCycPred(apply,maplist,3).

:- kb_shared(isRegisteredCycPred/3).

/*
:- ((rtrace, dtrace)).

(({fail,current_module(Mt),
   predicate_property(Mt:P,defined), 
 \+ predicate_property(Mt:P,imported_from(_)),
 functor(P,F,A)})
  ==>isRegisteredCycPred(Mt,F,A)).
*/

/* prolog_listing:listing */
% :- printAll(isRegisteredCycPred/3).

% ~(tCol({})).

:- unload_file(library(yall)).



% Unneeded yet
% pass2



/*

doRemoveMe ==> ~ removeMe(_,_).

removeMe(1,2).
removeMe(1,3).

doRemoveMe.



doRedelMe ==>  {redelMe(A,B)}, \+ redelMe(A,B).

redelMe(1,2).
redelMe(1,3).

doRedelMe.

 % :- listing(removeMe/2).
 % :- listing(redelMe/2).

:- dbreak.
*/

%  % :- set_prolog_flag(dialect_pfc,cwc).
%  % :- mpred_trace_exec.

% isa(I,C)==>{wdmsg(isa(I,C))}.


do_and_undo(mpred_post_exactly,mpred_remove_exactly).

%:- if( \+ flag_call(runtime_speed==true)).
%(((CI,{was_mpred_isa(CI,I,C)},\+ ~isa(I,C)) ==> actn(mpred_post_exactly(isa(I,C))))).
%:- endif.

% :- abolish(system:arity,2).
% :- system:import(arity/2).


tSet(tFoo).
isa(iBar,tFoo).
:- sanity(isa(iBar,tFoo)).


:- mpred_notrace_exec.

:- scan_missed_source.

