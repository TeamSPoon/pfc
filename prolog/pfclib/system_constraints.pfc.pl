:- module(system_constraints,[]).
:- if('$set_source_module'(baseKB)).
:- endif.
/** <module> system_constraints
% =============================================
% File 'system_constraints.pfc'
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


:- file_begin(pfc).

:- kb_shared(predicate_relaxed/1).

% if we can assert clauses with attvars
:- if(current_prolog_flag(assert_attvars,true)).

:- use_module(library(clause_attvars)).

predicate_relaxed(Spec),{ mpred_functor(Spec,F,A),functor(P,F,A)} ==>  
   macroExpandExact(P, relax_goal(P,Q),Q).
       
:- else.

predicate_relaxed(Spec),{ mpred_functor(Spec,F,A),functor(LOOP,F,A)} ==>  
 (((LOOP:-
    awc,    % awc means this rule is always first
      \+ is_looping(LOOP),!,
       loop_check_term(
         (relax(LOOP),LOOP),
         LOOP,fail))),
  prologOrdered(F)).  % Prolog Ordered is secondary insurance new assertions use assertz

% make sure current bug is caught
prologOrdered(F),predSingleValued(F)? {trace_or_throw(unsupported(prologOrdered(F),predSingleValued(F))}.

:- endif.

% ?- G=(loves(X,Y),~knows(Y,tHuman(X))),relax_goal(G,Out),writeq(Out).

predicate_relaxed(test_weak/2).

test_weak(vWeak1,vWeak2).

:- listing(test_weak/2).

