/*  
% ===================================================================
% File 'mpred_type_constraints.pl'
% Purpose: For Emulation of OpenCyc for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface' 1.0.0
% Revision:  $Revision: 1.9 $
% Revised At:   $Date: 2002/06/27 14:13:20 $
% ===================================================================
% File used as storage place for all predicates which change as
% the world is run.
%
%
% Dec 13, 2035
% Douglas Miles
*/


% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/mpred/mpred_type_constraints.pl
:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(mpred_type_constraints,
          [ add_iza/2,
            arg_to_var/3,
            attempt_attribute_args/3,
            attempt_attribute_args/5,
            attempt_attribute_one_arg/4,
            attribs_to_atoms/2,
            attribs_to_atoms0/2,
            cmp_memberchk/2,
            cmp_memberchk0/2,
            comp_type/3,
            dom/2,
            extend_dom/2,
            extend_domain/2,
            init_dom/2,
            inst_isac/2,
            isa_pred_l/3,
            isa_pred_l/4,
            isac/2,
            isac_chk/2,
            isac_gen/2,
            iza_to_isa/2,
            map_subterms/3,
            max_isa/3,
            max_isa_l/2,
            mdif/2,
            min_isa/3,
            min_isa_l/2,
            promp_yn/2,
            same/2,
            same_arg/3,
            samef/2,
            to_functor/2,
            type_size/2,
            extract_conditions/2,

            dom_lbl/1, dom_member/1,

            lazy/1,lazy/2,
            weaken/1,weaken_goal/2,thaw/1,
            mpred_type_constraints_file/0
          ]).

:- include('mpred_header.pi').

:- endif.
 :- meta_predicate isa_pred_l(+,*,*),
              isa_pred_l(+,*,*,*),
              map_subterms(+,?,?),
              dom_member(0),
              boxlog_goal_expansion(*,*).

:- meta_predicate
  thaw(?),
  lazy(0),
  weaken(0),
  weaken_goal(0,0),
  lazy(?,0).



%% extract_conditions( +PFCSentence, -Conds) is semidet.
%
% Datalog Preconditional Expansion.
%
extract_conditions(Sentence,Conds):- 
 copy_term(Sentence,Sentence,Goals),
 list_to_conjuncts(Goals,Conds),!.

%% boxlog_goal_expansion( ?G, ?GG) is semidet.
%
% Datalog Goal Expansion.
%
boxlog_goal_expansion(weaken(G),GG):-!,weaken_goal(G,GG).
/* 
boxlog_goal_expansion(G,_):- % \+ source_location(_,_),
  wdmsg(g_s(G)),fail.
*/




%% weaken( :GoalG) is semidet.
%
% Weaken.
%
weaken(G):- weaken_goal(G,GG) -> GG.




%% weaken_goal( :GoalG, :GoalGGG) is semidet.
%
% Weaken Goal.
%
weaken_goal(G,GGG):- copy_term(G,GG,Gs),G=GG,G=..[_|ARGS],weaken_args(GG,1,ARGS),   GGG=(GG,maplist(dom_member,Gs)).




%% weaken_arg( ?G, ?N, ?A) is semidet.
%
% Weaken Argument.
%
weaken_arg(G,N,A):- dom(AA,[A]),!,setarg(N,G,AA).
weaken_arg(G,N,A):- (var(A)->true;(dom(AA,[A]),setarg(N,G,AA))).




%% weaken_args( ?G, ?N, :TermA) is semidet.
%
% Weaken Arguments.
%
weaken_args(G,N,[A]):-weaken_arg(G,N,A),!.
weaken_args(G,N,[A|RGS]):-weaken_arg(G,N,A),N2 is N + 1,weaken_args(G,N2,RGS).




%% lazy( :GoalG) is semidet.
%
% Lazy.
%
lazy(G):- term_variables(G,Vs),(Vs==[]->G;lazy(Vs,G)).



%% lazy( ?V, :GoalG) is semidet.
%
% Lazy.
%
lazy([V],G):-!,freeze(V,G).
lazy([V|Vs],G):-freeze(V,G),!,lazy(Vs,G).




%% thaw( ?G) is semidet.
%
% Thaw.
%
thaw(G):- call_residue_vars(G,Vs),maplist(melt,Vs).




%% melt( ?G) is semidet.
%
% melt.
%
melt(V):-frozen(V,G),call(G).




%% attribs_to_atoms( ?ListA, ?List) is semidet.
%
% Attribs Converted To Atoms.
%
attribs_to_atoms(ListA,List):-map_subterms(attribs_to_atoms0,ListA,List).




%% map_subterms( :PRED2Pred, ?I, ?O) is semidet.
%
% Map Subterms.
%
map_subterms(Pred,I,O):-call(Pred,I,O).
map_subterms(Pred,I,O):-is_list(I),!,maplist(map_subterms(Pred),I,O).
map_subterms(Pred,I,O):-compound(I),!,I=..IL,maplist(map_subterms(Pred),IL,OL),O=..OL.
map_subterms(_Pred,IO,IO).




%% iza_to_isa( :TermAA, :TermAB) is semidet.
%
% iza Converted To  (isa/2).
%
iza_to_isa(Iza,ftTerm):-var(Iza),!.
iza_to_isa((A,B),isAnd(ListO)):-!,conjuncts_to_list((A,B),List),list_to_set(List,Set),min_isa_l(Set,ListO).
iza_to_isa((A;B),isOr(Set)):-!,conjuncts_to_list((A,B),List),list_to_set(List,Set).
iza_to_isa(AA,AB):-must(AA=AB).



%%  argisa:attribute_goals(+Var)// is semidet.
%
%
argisa:attribute_goals(_) --> [true].



%% attr_unify_hook( ?X, ?Other) is semidet.
%
% Hook To [dom:attr_unify_hook/2] For Module Mpred_type_constraints.
% Attr Unify Hook.
%
argisa:attr_unify_hook(_, _).




%% attribs_to_atoms0( ?Var, ?Isa) is semidet.
%
% Attribs Converted To Atoms Primary Helper.
%
attribs_to_atoms0(Var,Isa):-get_attr(Var,argisa,Iza),!,must(iza_to_isa(Iza,Isa)).
attribs_to_atoms0(O,O):-not(compound(O)).





%% min_isa_l( ?List, ?ListO) is semidet.
%
% min  (isa/2) (List version).
%
min_isa_l(List,ListO):-isa_pred_l(lambda(Y,X,genls(X,Y)),List,ListO).



%% max_isa_l( ?List, ?ListO) is semidet.
%
% max  (isa/2) (List version).
%
max_isa_l(List,ListO):-isa_pred_l(genls,List,ListO).





%% isa_pred_l( :PRED2Pred, ?List, ?ListO) is semidet.
%
%  (isa/2) Predicate (List version).
%
isa_pred_l(Pred,List,ListO):-isa_pred_l(Pred,List,List,ListO).




%% isa_pred_l( :PRED2Pred, ?UPARAM2, ?List, ?UPARAM4) is semidet.
%
%  (isa/2) Predicate (List version).
%
isa_pred_l(_Pred,[],_List,[]).
isa_pred_l(Pred,[X|L],List,O):-member(Y,List),X\=Y,call_u(call(Pred,X,Y)),!,isa_pred_l(Pred,L,List,O).
isa_pred_l(Pred,[X|L],List,[X|O]):-isa_pred_l(Pred,L,List,O).




%% min_isa( :TermHintA, ?HintA, ?HintA) is semidet.
%
% min  (isa/2).
%
min_isa(HintA,HintA,HintA):- !.
min_isa(HintA,HintB,HintA):- call_u(genls(HintA,HintB)),!.
min_isa(HintB,HintA,HintA):- call_u(genls(HintA,HintB)),!.
min_isa((A,B),HintC,HintO):- min_isa(A,HintC,HintA),min_isa(B,HintC,HintB),conjoin(HintA,HintB,HintO).
min_isa(HintA,HintB,HintO):- conjoin(HintA,HintB,HintO).




%% max_isa( :TermHintA, ?HintA, ?HintA) is semidet.
%
% max  (isa/2).
%
max_isa(HintA,HintA,HintA):- !.
max_isa(HintA,HintB,HintB):- genls(HintA,HintB),!.
max_isa(HintB,HintA,HintB):- genls(HintA,HintB),!.
max_isa((A,B),HintC,HintO):- max_isa(A,HintC,HintA),max_isa(B,HintC,HintB),conjoin(HintA,HintB,HintO).
max_isa(HintA,HintB,HintO):- conjoin(HintA,HintB,HintO).





%% add_iza( ?Var, ?HintA) is semidet.
%
% Add Iza.
%
add_iza(Var,HintA):- var(Var),
  (get_attr(Var,argisa,HintB)
    ->min_isa(HintA,HintB,Hint);Hint=HintA), 
     put_attr(Var,argisa,Hint).
add_iza(Var,Hint):- ignore(show_failure(why,call_u(isa(Var,Hint)))).

:- style_check(-singleton).




%% dom_lbl( ?X) is semidet.
%
% Domain Labeling (residuals).
%
dom_lbl(X):-copy_term(X,X,Gs),maplist(dom_member,Gs).




%% dom_member( :GoalG) is semidet.
%
% Domain Member.
%
dom_member(dom(X,List)):-!,member(X,List).
dom_member(G):-G.




%% attempt_attribute_args( ?AndOr, ?Hint, :TermVar) is semidet.
%
% Attempt Attribute Arguments.
%
attempt_attribute_args(AndOr,Hint,Var):- var(Var),add_iza(Var,Hint),!.
attempt_attribute_args(AndOr,Hint,Grnd):-ground(Grnd),!.
attempt_attribute_args(AndOr,Hint,Term):-not(compound(Term)),!.
attempt_attribute_args(AndOr,Hint,+(A)):-!,attempt_attribute_args(AndOr,Hint,A).
attempt_attribute_args(AndOr,Hint,-(A)):-!,attempt_attribute_args(AndOr,Hint,A).
attempt_attribute_args(AndOr,Hint,?(A)):-!,attempt_attribute_args(AndOr,Hint,A).
attempt_attribute_args(AndOr,Hint,(A,B)):-!,attempt_attribute_args(AndOr,Hint,A),attempt_attribute_args(AndOr,Hint,B).
attempt_attribute_args(AndOr,Hint,[A|B]):-!,attempt_attribute_args(AndOr,Hint,A),attempt_attribute_args(AndOr,Hint,B).
attempt_attribute_args(AndOr,Hint,(A;B)):-!,attempt_attribute_args(';'(AndOr),Hint,A),attempt_attribute_args(';'(AndOr),Hint,B).
attempt_attribute_args(AndOr,Hint,Term):- use_was_isa(Term,I,C), add_iza(I,C).
attempt_attribute_args(AndOr,Hint,Term):- Term=..[F,A],tCol(F),!,attempt_attribute_args(AndOr,F,A).
attempt_attribute_args(AndOr,Hint,Term):- Term=..[F|ARGS],!,attempt_attribute_args(AndOr,Hint,F,1,ARGS).




%% attempt_attribute_args( ?AndOr, ?Hint, ?F, ?N, :TermARG5) is semidet.
%
% Attempt Attribute Arguments.
%
attempt_attribute_args(AndOr,_Hint,_F,_N,[]):-!.
attempt_attribute_args(AndOr,Hint,t,1,[A]):-attempt_attribute_args(AndOr,callable,A).
attempt_attribute_args(AndOr,Hint,t,N,[A|ARGS]):-atom(A),!,attempt_attribute_args(AndOr,Hint,A,N,ARGS).
attempt_attribute_args(AndOr,Hint,t,N,[A|ARGS]):-not(atom(A)),!.
attempt_attribute_args(AndOr,Hint,F,N,[A|ARGS]):-attempt_attribute_one_arg(Hint,F,N,A),N2 is N+1,attempt_attribute_args(AndOr,Hint,F,N2,ARGS).




%% attempt_attribute_one_arg( ?Hint, ?F, ?N, ?A) is semidet.
%
% Attempt Attribute One Argument.
%
attempt_attribute_one_arg(Hint,F,N,A):-call_u(argIsa(F,N,Type)),Type\=ftTerm,not(compound(Type)),!,attempt_attribute_args(AndOr,Type,A).
attempt_attribute_one_arg(Hint,F,N,A):-call_u(argQuotedIsa(F,N,Type)),Type\=ftTerm,not(compound(Type)),!,attempt_attribute_args(AndOr,Type,A).
attempt_attribute_one_arg(Hint,F,N,A):-call_u(argIsa(F,N,Type)),Type\=ftTerm,!,attempt_attribute_args(AndOr,Type,A).
attempt_attribute_one_arg(Hint,F,N,A):-attempt_attribute_args(AndOr,argi(F,N),A).



% mdif(A,B):- tlbugger:attributedVars,!,dif(A,B).



%% mdif( ?A, ?B) is semidet.
%
% Mdif.
%
mdif(A,B):-A\==B.

:- was_export((samef/2,same/2)).



%% same( ?X, ?Y) is semidet.
%
% Same.
%
same(X,Y):- samef(X,Y),!.
same(X,Y):- compound(X),arg(1,X,XX)->same(XX,Y),!.
same(Y,X):- compound(X),arg(1,X,XX),!,same(XX,Y).




%% samef( ?X, ?Y) is semidet.
%
% Samef.
%
samef(X,Y):- quietly(((to_functor(X,XF),to_functor(Y,YF),(XF=YF->true;string_equal_ci(XF,YF))))).




%% to_functor( ?A, ?O) is semidet.
%
% Converted To Functor.
%
to_functor(A,O):-is_ftVar(A),!,A=O.
to_functor(A,O):-compound(A),get_functor(A,F),!,to_functor(F,O).
to_functor(A,A).

:- was_export(arg_to_var/3).



%% arg_to_var( ?Type, ?String, ?Var) is semidet.
%
% Argument Converted To Variable.
%
arg_to_var(_Type,_String,_Var).

:- was_export(same_arg/3).




%% same_arg( ?How, ?X, ?Y) is semidet.
%
% Same Argument.
%
same_arg(_How,X,Y):-var(X),var(Y),!,X=Y.
same_arg(equals,X,Y):-!,equals_call(X,Y).
same_arg(tCol(_Type),X,Y):-!, unify_with_occurs_check(X,Y).

same_arg(ftText,X,Y):-(var(X);var(Y)),!,X=Y.
same_arg(ftText,X,Y):-!, string_equal_ci(X,Y).

same_arg(same_or(equals),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(genls),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(genls),Sub,Sup):- holds_t(genls,Sub,Sup),!.
same_arg(same_or(isa),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(isa),I,Sup):- !, holds_t(Sup,I),!.

same_arg(same_or(_Pred),X,Y):- same_arg(equals,X,Y).
same_arg(same_or(Pred),I,Sup):- holds_t(Pred,I,Sup),!.

% same_arg(I,X):- promp_yn('~nSame Objects: ~q== ~q ?',[I,X]).



%% promp_yn( ?Fmt, ?A) is semidet.
%
% Promp Yn.
%
promp_yn(Fmt,A):- format(Fmt,A),get_single_char(C),C=121.

:- set_prolog_flag(generate_debug_info, true).


% :-swi_module(dom, [ dom/2  ]). % Var, ?Domain
:- use_module(library(ordsets)).
:- was_export(dom/2).



%% dom( ?X, ?Dom) is semidet.
%
% Domain.
%
dom(X, Dom) :-
      var(Dom), !,
      get_attr(X, dom, Dom).
dom(X, List) :-
      list_to_ord_set(List, Domain),
      put_attr(Y, dom, Domain),
      X = Y.

:- was_export(extend_domain/2).



%% extend_domain( ?X, ?DomL) is semidet.
%
% Extend Domain.
%
extend_domain(X, DomL):- init_dom(X, Dom2), ord_union(Dom2, DomL, NewDomain),put_attr( X, dom, NewDomain ).

:- was_export(extend_dom/2).



%% extend_dom( ?X, ?DomE) is semidet.
%
% Extend Domain.
%
extend_dom(X, DomE):-  init_dom(X, Dom2),ord_add_element(Dom2, DomE, NewDomain),put_attr( X, dom, NewDomain ).

:- was_export(init_dom/2).



%% init_dom( ?X, ?Dom) is semidet.
%
% Init Domain.
%
init_dom(X,Dom):-get_attr(X, dom, Dom),!.
init_dom(X,Dom):-Dom =[_], put_attr(X, dom, Dom),!.

% An attributed variable with attribute value Domain has been
% assigned the value Y
dom:attr_unify_hook(Domain, Y) :-
   ( get_attr(Y, dom, Dom2)
   -> ord_intersection(Domain, Dom2, NewDomain),
   ( NewDomain == []
   -> fail
   ; NewDomain = [Value]
   -> Y = Value
   ; put_attr(Y, dom, NewDomain)
   )
   ; var(Y)
   -> put_attr( Y, dom, Domain )
   ; (\+ \+ (cmp_memberchk(Y, Domain)))
).



% Translate attributes from this module to residual goals
dom:attribute_goals(X) -->
      { get_attr(X, dom, List) },
      [dom(X, List)].





%% cmp_memberchk( ?X, ?Y) is semidet.
%
% Cmp Memberchk.
%
cmp_memberchk(X,Y):-numbervars(X,0,_,[attvars(skip)]),member(X,Y),!.



%% cmp_memberchk0( ?Item, :TermX1) is semidet.
%
% Cmp Memberchk Primary Helper.
%
cmp_memberchk0(Item, [X1,X2,X3,X4|Xs]) :- !,
	compare(R4, Item, X4),
	(   R4 = (>) -> cmp_memberchk0(Item, Xs)
	;   R4 = (<) ->
	    compare(R2, Item, X2),
	    (   R2 = (>) -> Item = X3
	    ;   R2 = (<) -> Item = X1
	    ;/* R2 = (=),   Item = X2 */ true
	    )
	;/* R4 = (=) */ true
	).
cmp_memberchk0(Item, [X1,X2|Xs]) :- !,
	compare(R2, Item, X2),
	(   R2 = (>) -> cmp_memberchk0(Item, Xs)
	;   R2 = (<) -> Item = X1
	;/* R2 = (=) */ true
	).
cmp_memberchk0(Item, [X1]) :-
	Item = X1.



:- was_export(isac/2).



%% isac( ?X, ?Dom) is semidet.
%
% Isac.
%
isac(X, Dom) :-
      var(Dom), !,
      get_attr(X, isac, Dom).
isac(X, Domain) :-
      put_attr(Y, isac, Domain),!,
      X = Y.




%% type_size( ?VALUE1, :PRED1000VALUE2) is semidet.
%
% Type Size.
%
type_size(C,S):-a(completeExtentEnumerable,C),!,setof(E,t(C,E),L),length(L,S).
type_size(C,1000000):-a(ttExpressionType,C),!.
type_size(_,1000).

/*

?-  Z #=:= 2 + X, Z #< 2 .

succ(succ(0)).

S2I
I2E

2
2
2
E2S

S = succ/1.
I = integer
E = 2

a:p(1).

a:p(X):-b:p(X).
b:p(X):-c:p(X).

b:p(2).

*/ 


%% comp_type( ?Comp, ?Col1, ?Col2) is semidet.
%
% Comp Type.
%
comp_type(Comp,Col1,Col2):-type_size(Col1,S1),type_size(Col2,S2),compare(Comp,S1,S2).




%% inst_isac( ?X, ?List) is semidet.
%
% Inst Isac.
%
inst_isac(X, List):- predsort(comp_type,List,SList),isac_gen(X,SList).

% An attributed variable with attribute value DVar has been
% assigned the value Y
isac:attr_unify_hook(DVar, Y):-
   ( get_attr(Y, isac, Dom2)
   -> ord_union(DVar, Dom2, NewDomain),
   ( (fail,NewDomain == [])
   -> fail
   ; (fail,NewDomain = [Value])
   -> Y = Value
   ; put_attr(Y, isac, NewDomain)
   )
   ; var(Y)
   -> put_attr( Y, isac, DVar )
   ;  isac_chk(Y,DVar)).




%% isac_chk( ?E, ?Cs) is semidet.
%
% Isac Checking.
%
isac_chk(E,Cs):-once(isac_gen(E,Cs)).




%% isac_gen( ?VALUE1, :TermARG2) is semidet.
%
% Isac Gen.
%
isac_gen(_, []).
isac_gen(Y, [H|List]):-call_u(isa(Y,H)),!,isac_gen(Y, List).



% Translate attributes from this module to residual goals
isac:attribute_goals(X) -->
      { get_attr(X, isac, List) },
      [isac(X, List)].

:- fixup_exports.

mpred_type_constraints_file.


%% goal_expansion( ?LC, ?LCOO) is semidet.
%
% Hook To [system:goal_expansion/2] For Module Mpred_type_constraints.
% Goal Expansion.
%
% system:goal_expansion(G,O):- \+ current_prolog_flag(xref,true),\+ pldoc_loading, nonvar(G),boxlog_goal_expansion(G,O).


