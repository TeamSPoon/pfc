

/*

% fix_mp(Why,Unassertable,_,_):- Why = clause(_,_), unassertable(Unassertable),!,trace_or_throw(unassertable_fix_mp(Why,Unassertable)).

*/
system_between(A,B,C):-call(call,between,A,B,C).

pfc_truth_value(Call,vTrue,vAsserted):-clause_b(Call),!.
pfc_truth_value(Call,vTrue,vDeduced):-call_u(Call),!.
pfc_truth_value(_Call,vUnknown,vFailed).

convention_to_mt(From,Why,F,A,RealMt):-convention_to_symbolic_mt_ec(From,Why,F,A,Mt),to_real_mt(Why,Mt,RealMt).

get_unnegated_mfa(M:G,M,F,A):-!,get_unnegated_functor(G,F,A).
get_unnegated_mfa(G,M,F,A):- strip_module(G,M0,_),get_unnegated_functor(G,F,A),
                 convention_to_mt(M0,get_unnegated_mfa(G,M,F,A),F,A,M).

get_unnegated_functor(G,F,A):- strip_module(G,_,GO),
   get_assertion_head_unnegated(GO,Unwrap),
   nonvar(Unwrap),
   safe_functor(Unwrap,F,A),
   ignore(show_failure(\+ bad_head_pred(F))),!.
   

:- module_transparent( (get_assertion_head_unnegated)/2).

get_assertion_head_unnegated(Head,Unwrap):-
  get_assertion_head(Head,Mid),
  maybe_unnegated(Mid,Unwrap).

   
maybe_unnegated(Head,Head):- \+ compound(Head),!.
maybe_unnegated(~ Head,Unwrap):- \+ is_ftVar(Head),!, get_assertion_head(Head,Unwrap).
maybe_unnegated( \+ Head,Unwrap):- \+ is_ftVar(Head),!, get_assertion_head(Head,Unwrap).
maybe_unnegated(Head,Unwrap):- get_assertion_head(Head,Unwrap).


get_assertion_head(Head,Head):- \+ compound(Head),!.
get_assertion_head(Head,Unwrap):- is_ftVar(Head),!,Head=Unwrap.
get_assertion_head( ( Head :- _ ),Unwrap):- nonvar(Head), !, get_assertion_head(Head,Unwrap).
get_assertion_head(Head,Unwrap):- strip_module(Head,_,HeadM),Head\=@=HeadM,!,get_assertion_head(HeadM,Unwrap).
% Should?
get_assertion_head( ( _,Head),Unwrap):- \+ is_ftVar(Head),!, get_assertion_head(Head,Unwrap).
% Should?
get_assertion_head((P/_),PP):- \+ is_ftVar(P),!,get_assertion_head(P,PP).
% Should?
% NOOOO get_assertion_head((P<-_),PP):-compound(P),!,get_assertion_head(P,PP).
% disabled
get_assertion_head( Head,UnwrapO):- fail, pfc_rule_hb(Head,Unwrap,_),nonvar(Unwrap),
  Head \=@= Unwrap,!,get_assertion_head(Unwrap,UnwrapO).
get_assertion_head(P,P).


get_head_term(Form,Form):-var(Form),!.
get_head_term(F/A,Form):- integer(A),safe_functor(Form,F,A),!.
get_head_term(Form0,Form):- get_assertion_head_unnegated(Form0,Form).

bad_head_pred([]).
bad_head_pred('[]').
bad_head_pred((.)).
bad_head_pred('{}').
bad_head_pred('[|]').
bad_head_pred(',').
bad_head_pred(':').
bad_head_pred('/').
bad_head_pred(':-').
bad_head_pred(';').
bad_head_pred( \+ ).
bad_head_pred_neg('~').

% bad_head_pred('=>').
% bad_head_pred('<-').
% bad_head_pred('==>').
% Probably bad_head_pred('==>').

% the next line transforms to pfc_lib:convention_to_symbolic_mt(_From,_Why,A, _, B) :- call(ereq, predicateConventionMt(A, B)), !.

convention_to_symbolic_mt_ec(From,Why,F,A,Mt):-convention_to_symbolic_mt(From,Why,F,A,Mt).

/*convention_to_symbolic_mt(_From,_Why,predicateConventionMt,2,baseKB):-!.
convention_to_symbolic_mt(_From,_Why,genlMt,2,baseKB):-!.
convention_to_symbolic_mt(_From,_Why,mtNonAssertable,1,baseKB):-!.
convention_to_symbolic_mt(_From,_Why,mtProlog,1,baseKB):-!.
convention_to_symbolic_mt(_From,_Why,functorDeclares,1,baseKB):-!.
convention_to_symbolic_mt(_From,_Why,functorIsMacro,1,baseKB):-!.
*/

convention_to_symbolic_mt(_From,_Why,mtHybrid,1,baseKB):-!.
convention_to_symbolic_mt(From,_Why,F,_,Mt):-  clause_b(From:predicateConventionMt(F,Mt)),!.
convention_to_symbolic_mt(_From,_Why,F,A,M):- lmcache:already_decl(kb_global,M,F,A),!.




% convention_to_symbolic_mt(From,Why,F,A,Error):- bad_head_pred(F),!,dumpST,dmsg_pretty(bad_head_pred(F)),break,trace_or_throw_ex(error_convention_to_symbolic_mt(From,Why,F,A,Error)).
convention_to_symbolic_mt(_From,_Why,F,A,M):- lmcache:already_decl(kb_global,M,F,A),!.
convention_to_symbolic_mt(_From,_Why,F,A,abox):- pfc_database_term_syntax(F,A,_).
convention_to_symbolic_mt(_From,_Why,F,A,abox):- lmcache:already_decl(kb_shared,_,F,A),!.
convention_to_symbolic_mt(_From,_Why,F,A,abox):- lmcache:already_decl(kb_local,_,F,A),!.

convention_to_symbolic_mt(_From,_Why,F,A,Mt):-  safe_functor(P,F,A),show_success(predicate_property(P,imported_from(Mt))),!.
convention_to_symbolic_mt(_From,_Why,F,A,   M):- lmcache:already_decl(kb_global,M,F,A),!.
convention_to_symbolic_mt(_From,_Why,F,A,abox):- pfc_database_term(F,A,_).
convention_to_symbolic_mt(_From,_Why,F,A,abox):- clause_b(safe_wrap(_M,F,A,ereq)).


convention_to_symbolic_mt(From,Why,F,A,Error):- bad_head_pred(F),!,Error = From,
  if_interactive((
   dumpST,dmsg_pretty(bad_head_pred(F)),break,trace_or_throw(error_convention_to_symbolic_mt(From,Why,F,A,Error)))).


% convention_to_symbolic_mt(_From,_Why,_,_,M):- atom(M),!.

full_transform_warn_if_changed(_,MH,MHH):-!,MH=MHH.
full_transform_warn_if_changed(Why,MH,MHH):- full_transform(Why,MH,MHH),!,sanity(MH=@=MHH).
full_transform_warn_if_same(Why,MH,MHH):- full_transform(Why,MH,MHH),!,sanity(MH \=@= MHH).

%% pred_head( :PRED1Type, ?P) is semidet.
%
% Predicate Head.
%
pred_head(Type,P):- no_repeats(P,(call(Type,P),\+ nonfact_metawrapper(P),is_ftCompound(P))).


%% pred_head_all( +P) is semidet.
%
% Predicate Head All.
%
pred_head_all(P):- pred_head(pred_all,P).


%% nonfact_metawrapper( :TermP) is semidet.
%
% Nonfact Metawrapper.
%
nonfact_metawrapper(~(_)).
nonfact_metawrapper(pt(_,_)).
nonfact_metawrapper(bt(_,_,_)).
nonfact_metawrapper(nt(_,_)).
nonfact_metawrapper(spft(_,_,_)).
nonfact_metawrapper(added(_)).
% we use the arity 1 forms is why 
nonfact_metawrapper(term_expansion(_,_)).
nonfact_metawrapper(P):- \+ current_predicate(_,P).
nonfact_metawrapper(M:P):-atom(M),!,nonfact_metawrapper(P).
nonfact_metawrapper(P):- get_functor(P,F,_), 
   (a(prologSideEffects,F);a(rtNotForUnboundPredicates,F)).
nonfact_metawrapper(P):-rewritten_metawrapper(P).


%% rewritten_metawrapper( +C) is semidet.
%
% Rewritten Metawrapper.
%
rewritten_metawrapper(_):-!,fail.
%rewritten_metawrapper(isa(_,_)).
rewritten_metawrapper(C):-is_ftCompound(C),functor(C,t,_).


%% meta_wrapper_rule( :TermARG1) is semidet.
%
% Meta Wrapper Rule.
%
meta_wrapper_rule((_<-_)).
meta_wrapper_rule((_<==>_)).
meta_wrapper_rule((_==>_)).
meta_wrapper_rule((_:-_)).



%% pred_all( +P) is semidet.
%
% Predicate All.
%
pred_all(P):-pred_u0(P).
pred_all(P):-pred_t0(P).
pred_all(P):-pred_r0(P).


%% pred_u0( +P) is semidet.
%
% Predicate For User Code Primary Helper.
%
pred_u0(P):-pred_u1(P),has_db_clauses(P).
pred_u0(P):-pred_u2(P).

%% pred_u1( +VALUE1) is semidet.
%
% Predicate For User Code Secondary Helper.
%
pred_u1(P):-a(pfcControlled,F),arity_no_bc(F,A),functor(P,F,A).
pred_u1(P):-a(prologHybrid,F),arity_no_bc(F,A),functor(P,F,A).
pred_u1(P):-a(prologDynamic,F),arity_no_bc(F,A),functor(P,F,A).

%% pred_u2( +P) is semidet.
%
% Predicate For User Code Extended Helper.
%
pred_u2(P):- compound(P),functor(P,F,A),sanity(no_repeats(arity_no_bc(F,A))),!,has_db_clauses(P).
pred_u2(P):- no_repeats(arity_no_bc(F,A)),functor(P,F,A),has_db_clauses(P).



%% has_db_clauses( +PI) is semidet.
%
% Has Database Clauses.
%
has_db_clauses(PI):-modulize_head(PI,P),
   predicate_property(P,number_of_clauses(NC)),\+ predicate_property(P,number_of_rules(NC)), \+ \+ clause(P,true).



%% pred_t0(+ ?P) is semidet.
%
% Predicate True Stucture Primary Helper.
%
pred_t0(P):-mreq('==>'(P)).
pred_t0(P):-mreq(pt(P,_)).
pred_t0(P):-mreq(bt(P,_)).
pred_t0(P):-mreq(nt(P,_,_)).
pred_t0(P):-mreq(spft(P,_,_)).

%pred_r0(-(P)):- call_u(-(P)).
%pred_r0(~(P)):- mreq(~(P)).


%% pred_r0( :TermP) is semidet.
%
% Predicate R Primary Helper.
%
pred_r0(P==>Q):- mreq(P==>Q).
pred_r0(P<==>Q):- mreq(P<==>Q).
pred_r0(P<-Q):- mreq(P<-Q).

mreq(G):- clause_b(G).


:- user:use_module(library(clpfd),['#='/2]).
%% get_arity( :TermTerm, ?F, ?A) is semidet.
%
% Get Arity.
%
get_arity(Term,F,A):- atom(Term),F=Term,!,ensure_arity(F,A).
get_arity(F/A,F,A):-!,atom(F),ensure_arity(F,A),!,(A>0).
get_arity(F // A,F,A2):- must(integer(A)),!, atom(F), is(A2 , A+2), ensure_arity(F,A2),!,(A2>0).
get_arity(F // A,F,A2):- use_module(library(clpfd),['#='/2]),!, atom(F), clpfd:call(#=(A2 , A+2)), ensure_arity(F,A2),!,(A2>0).
get_arity(M:FA,F,A):-atom(M),!,get_arity(FA,F,A).
get_arity(FA,F,A):- get_functor(FA,F,A),must(A>0).

% arity_no_bc(F,A):- call_u(arity(F,A)).
arity_no_bc(F,A):- clause_b(arity(F,A)).
arity_no_bc(F,A):- clause_b(support_hilog(F,A)).
arity_no_bc(F,A):- clause_b(functorDeclares(F)),!,A=1.
arity_no_bc(completeExtentAsserted,1).
arity_no_bc(home,2).
arity_no_bc(record,2).
arity_no_bc(F,A):- suggest_m(M),clause_b(mpred_prop(M,F,AA,_)),nonvar(AA),A=AA.
%arity_no_bc(F,A):- current_predicate(F/A)
% arity_no_bc(F,A):- current_predicate(_:F/A),\+(current_predicate(_:F/AA),AA\=A). =

%% ensure_arity( ?VALUE1, ?VALUE2) is semidet.
%
% Ensure Arity.
%
ensure_arity(F,A):- 
 one_must(
   arity_no_bc(F,A),
   one_must(
    (current_predicate(F/A),(A>0),assert_arity(F,A)),
    (ground(F:A),(A>0),assert_arity(F,A)))),
  !.


%=

%% assert_arity( ?F, :PRED2A) is semidet.
%
% Assert Arity.
%

assert_arity(F,A):- sanity(\+ ((bad_arity(F,A), trace_or_throw(assert_arity(F,A))))), arity_no_bc(F,A),!.
assert_arity(F,A):- arity_no_bc(F,AA), A\=AA,dmsg_pretty(assert_additional_arity(F,AA->A)),!,ain_fast(arity(F,A)).
assert_arity(F,A):- ain_fast(arity(F,A)),!.

bad_arity(F,_):- \+ atom(F).
bad_arity(_,A):- \+ integer(A).
bad_arity('[|]',_).
bad_arity(typeProps,0).
bad_arity(argIsa,2).
bad_arity(isEach,_).
bad_arity(_,0).
bad_arity(prologDynamic,2).
bad_arity(F,A):- \+ good_pred_relation_name(F,A).


%=

%% good_pred_relation_name( ?F, ?A) is semidet.
%
% Good Predicate Relation Name.
%
good_pred_relation_name(F,A):- \+ bad_pred_relation_name0(F,A).


%=

%% bad_pred_relation_name0( ?V, ?VALUE2) is semidet.
%
% Bad Predicate Relation Name Primary Helper.
%
bad_pred_relation_name0(V,_):- \+ atom(V),!.
bad_pred_relation_name0('[]',_).
bad_pred_relation_name0('',_).
bad_pred_relation_name0('!',_).
bad_pred_relation_name0('{}',_).
bad_pred_relation_name0(',',_).
bad_pred_relation_name0('[|]',_).

%=

%% bad_pred_relation_name1( ?X, ?Y) is semidet.
%
% Bad Predicate Relation Name Secondary Helper.
%
bad_pred_relation_name1(X,Y):-bad_pred_relation_name0(X,Y).
bad_pred_relation_name1(F,A):-must_det((atom_codes(F,[C|_]),to_upper(C,U))),!, U == C, A>1.
bad_pred_relation_name1(F,A):-arity_no_bc(F,AO), A \= AO.

% :-after_boot(writeq("Seen Mpred_props at start!\n")),!.

%=

%% functor_check_univ( ?G1, ?F, ?List) is semidet.
%
% Functor Check Univ.
%
functor_check_univ(M:G1,F,List):-atom(M),member(M,[dbase,user]),!,functor_check_univ(G1,F,List),!.
functor_check_univ(G1,F,List):-must_det(compound(G1)),must_det(G1 \= _:_),must_det(G1 \= _/_),G1=..[F|List],!.

full_transform(Why,MH,MHH):-
 must_det(fully_expand_real(change(assert,Why),MH,MHH)),!,
 nop(sanity(on_f_debug(same_modules(MH,MHH)))).

same_modules(MH,MHH):- strip_module(MH,HM,_),strip_module(MHH,HHM,_),!,
   HM==HHM.

:- system:import(full_transform/3).


%% sub_term_eq( +H, ?HH) is semidet.
%
% Sub Term Using (==/2) (or =@=/2) ).
%
sub_term_eq(H,HH):-H==HH,!.
sub_term_eq(H,HH):-each_subterm(HH,ST),ST==H,!.


%% sub_term_v( +H, ?HH) is semidet.
%
% Sub Term V.
%
sub_term_v(H,HH):-H=@=HH,!.
sub_term_v(H,HH):-each_subterm(HH,ST),ST=@=H,!.

%% all_different_head_vals(+Clause) is det.
%
% Enforces All Different Head Vals.
%
all_different_head_vals(HB):- (\+ compound(HB) ; ground(HB)),!.
all_different_head_vals(HB):- 
  pfc_rule_hb(HB,H,B),
  term_slots(H,Slots),  
  (Slots==[]->
     all_different_head_vals(B);
    (lock_vars(Slots),all_different_head_vals_2(H,Slots),unlock_vars(Slots))),!.
  

all_different_head_vals_2(_H,[]):-!.
all_different_head_vals_2(H,[A,R|EST]):-get_assertion_head_arg(_,H,E1),E1 ==A,dif(A,E2),get_assertion_head_arg(_,H,E2),\+ occurs:contains_var(A,E2),all_different_vals(dif_matrix,[A,E2,R|EST]),!.
all_different_head_vals_2(_H,[A,B|C]):-all_different_vals(dif_matrix,[A,B|C]),!.
all_different_head_vals_2(HB,_):- \+ compound(HB),!.
all_different_head_vals_2(H,[A]):-get_assertion_head_arg(_,H,E1),E1 ==A, H=..[_|ARGS], all_different_vals(dif_matrix,ARGS),!.
all_different_head_vals_2(H,[A]):-get_assertion_head_arg(_,H,E1),E1 ==A,  get_assertion_head_arg(_,H,E2), A\==E2, \+ occurs:contains_var(A,E2), dif(A,E2),!.
all_different_head_vals_2(H,[A]):-get_assertion_head_arg(_,H,E1),E1\==A, compound(E1), occurs:contains_var(A,E1), all_different_head_vals_2(E1,[A]),!.
all_different_head_vals_2(_,_).
   	 

%% pfc_rule_hb( +Outcome, ?OutcomeO, ?AnteO) is semidet.
%
% Calculate PFC Rule Head+body.
%
pfc_rule_hb(Outcome,OutcomeO,Body):- nonvar(OutcomeO),!,pfc_rule_hb(Outcome,OutcomeN,Body),must(OutcomeO=OutcomeN).
pfc_rule_hb(Outcome,OutcomeO,BodyO):- nonvar(BodyO),!,pfc_rule_hb(Outcome,OutcomeO,BodyN),must(BodyN=BodyO).
pfc_rule_hb(Outcome,OutcomeO,AnteO):- 
  quietly((pfc_rule_hb_0(Outcome,OutcomeO,Ante),
  pfc_rule_hb_0(Ante,AnteO,_))).
% :-pfc_trace_nochilds(pfc_rule_hb/3).


%% pfc_rule_hb_0( +Rule, -Head, -Body) is nondet.
%
% Calculate PFC rule Head+Body  Primary Helper.
%


pfc_rule_hb_0(Outcome,OutcomeO,true):-is_ftVar(Outcome),!,OutcomeO=Outcome.
pfc_rule_hb_0(Outcome,OutcomeO,true):- \+compound(Outcome),!,OutcomeO=Outcome.
pfc_rule_hb_0((Outcome1,Outcome2),OutcomeO,AnteO):- pfc_rule_hb(Outcome1,Outcome1O,Ante1),pfc_rule_hb(Outcome2,Outcome2O,Ante2),
                   conjoin(Outcome1O,Outcome2O,OutcomeO),
                   conjoin(Ante1,Ante2,AnteO).
pfc_rule_hb_0((Ante1==>Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(=>(Ante1,Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Ante1->Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Ante1*->Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
% pfc_rule_hb_0((Outcome/Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(rhs([Outcome]),OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
% pfc_rule_hb_0(rhs([OutcomeH|OutcomeT]),OutcomeO,Ante2):- !, pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0({Outcome},OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Outcome<-Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(&(Ante1 , Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Ante1 , Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Outcome<==>Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Ante1<==>Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(_::::Outcome,OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb_0(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(bt(Outcome,Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(pt(Ante1,Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(pk(Ante1a,Ante1b,Outcome),OutcomeO,(Ante1a,Ante1b,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(nt(Ante1a,Ante1b,Outcome),OutcomeO,(Ante1a,Ante1b,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(spft(Outcome,Ante1a,Ante1b),OutcomeO,(Ante1a,Ante1b,Ante2)):- (nonvar(Outcome)-> ! ; true),pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(que(Outcome,_),OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
% pfc_rule_hb_0(pfc Default(Outcome),OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Outcome:-Ante),Outcome,Ante):-(nonvar(Outcome)-> ! ; true).
pfc_rule_hb_0(Outcome,Outcome,true).


%:- multifile(get_current_default_tbox/1).
%:- dynamic(get_current_default_tbox/1).
%get_current_default_tbox(baseKB).
:- if(current_predicate(get_current_default_tbox/1)).
:- redefine_system_predicate(get_current_default_tbox/1).
:- endif.
:- module_transparent(get_current_default_tbox/1).
get_current_default_tbox(TBox):- defaultAssertMt(ABox)->current_module(ABox)->clause(ABox:defaultTBoxMt(TBox),B),call(B),!.
get_current_default_tbox(baseKB).
:- sexport(get_current_default_tbox/1).


to_real_mt(_Why,abox,ABOX):- defaultAssertMt(ABOX),!.
to_real_mt(_Why,tbox,TBOX):- get_current_default_tbox(TBOX),!.
to_real_mt(_Why,BOX,BOX).

