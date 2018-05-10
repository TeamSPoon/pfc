
% :- throw(module(pfc_umt,[umt/1])).
:- module(pfc_umt,[umt/1]).

:- 
    op(1050,xfx,('==>')),
    op(1050,xfx,'<==>'),
    op(1050,xfx,('<-')),
    op(1050,xfx,('<==')),
    op(1100,fx,('==>')).


:- op(1050,xfx,('<-')).
:- op(1199,fx,('==>')).
:- op(1190,xfx,('::::')).
:- op(1180,xfx,('==>')).
:- op(1170,xfx,'<==>').
:- op(1160,xfx,('<-')).
:- op(1150,xfx,'=>').
:- op(1140,xfx,'<=').
:- op(1130,xfx,'<=>').
:- op(1100,fx,('nesc')).
:- op(300,fx,'-').
:- op(300,fx,'~').
:- op(600,yfx,'&'). 
:- op(600,yfx,'v').
:- op(1075,xfx,'<-').
:- op(350,xfx,'xor').

nb_current_no_nil(N,V):- nb_current(N,V),V\==[].

set_fileAssertMt(M):- nb_setval(defaultQueryMt,M),nb_setval(defaultAssertMt,M),nb_setval(fileAssertMt,M),maybe_ensure_abox(M).

% :- use_module(pfcsyntax).

defaultQueryMt(M):- nb_current_no_nil(defaultQueryMt,M)->true;(defaultQueryMt0(M)->nb_setval(defaultQueryMt,M)),!.
defaultQueryMt(M):- M=baseKB.
defaultQueryMt0(M):- nb_current_no_nil(fileAssertMt,M),!.
defaultQueryMt0(M):- nb_current_no_nil(defaultAssertMt,M),!.
defaultQueryMt0(M):- strip_module(module,M,module),M \==user,!.
defaultQueryMt0(M):- prolog_load_context(module,M),M \==user,!.
defaultQueryMt0(M):- '$current_typein_module'(M),M \==user,!.

set_defaultAssertMt(M):- nb_setval(defaultAssertMt,M),maybe_ensure_abox(M).

defaultAssertMt(M):- nb_current_no_nil(defaultAssertMt,M)->true;(defaultAssertMt0(M)->nb_setval(defaultAssertMt,M)),!.
defaultAssertMt(M):- M=baseKB.
defaultAssertMt0(M):- nb_current_no_nil(fileAssertMt,M),!.
defaultAssertMt0(M):- nb_current_no_nil(defaultQueryMt,M),!.
defaultAssertMt0(M):- 'strip_module'(module,M,module),M \==user,!.
defaultAssertMt0(M):- '$current_typein_module'(M),M \==user,!.
defaultAssertMt0(M):- prolog_load_context(module,M), M \==user,!.

fileAssertMt(M):- nb_current_no_nil(fileAssertMt,M)->true;(fileAssertMt0(M)->nb_setval(fileAssertMt,M)),!.
fileAssertMt(M):- M=baseKB.
fileAssertMt0(M):- nb_current_no_nil(defaultAssertMt,M),!.
fileAssertMt0(M):- nb_current_no_nil(defaultQueryMt,M),!.
fileAssertMt0(M):- prolog_load_context(module,M),M \==user,!.
fileAssertMt0(M):- '$current_typein_module'(M),M \==user,!.
fileAssertMt0(M):- 'strip_module'(module,M,module),M \==user,!.

fix_mp(_OpType,MP,M,P):-strip_module(MP,M,P).

get_clause_head(H,H):- \+ compound(H),!.
get_clause_head(P:-_,H):-!,get_clause_head(P,H).
get_clause_head(_:P,H):- get_clause_head(P,H).
get_clause_head(H,H).

get_unnegated_head(P,H):- get_clause_head(P,M),((current_predicate(pfc_negation/2),
  pfc_negation(M,H))->true;M=H).

get_unnegated_functor(P,F,A):-get_unnegated_head(P,H),!,functor(H,F,A).

:- module_transparent( (get_unnegated_head_arg)/3).
get_unnegated_head_arg(N,P,E):-get_unnegated_head(P,H),!,arg(N,H,E).


mpred_trace :- pfcWatch.
mpred_trace_exec :- pfcWatch.


%% erase_w_attvars( +Data0, ?Ref) is semidet.
%
% Erase W Attribute Variables.
%
erase_w_attvars(Data0,Ref):- attempt_side_effect(erase(Ref)),add_side_effect(erase,Data0).

ensure_abox(Mt):- maybe_ensure_abox(Mt).

:- meta_predicate(maybe_ensure_abox(:)).

maybe_ensure_abox(Mt):- 
 strip_module(Mt,I,M), 
 dmsg(maybe_ensure_abox(strip_module(Mt,I,M))),
 must(maybe_ensure_abox(M,M)).

:- multifile(pfc_umt:pfcDatabaseTerm_DYN/1).
:- dynamic(pfc_umt:pfcDatabaseTerm_DYN/1).

%quietly_ex(G):- quietly(G),!.
quietly_ex(G):- quietly(umt((G))),!.

%trace_or_throw_ex(G):- trace_or_throw_ex(G).

trace_or_throw_ex(G):- log_failure,trace_or_throw_ex(G).

%pfc_umt:pfcDatabaseTerm_DYN(FA):- pfcDatabaseTerm(FA).
pfc_umt:pfcDatabaseTerm_DYN(FA):- member(FA,[never_retract_u/2,never_retract_u/1,never_assert_u/2,never_assert_u/1]).
%% check_never_assert(+Pred) is semidet.
%
% Check Never Assert.
%

%check_never_assert(_Pred):-!.

check_never_assert(Pred):- quietly_ex(ignore(( copy_term_and_varnames(Pred,Pred_2),umt(never_assert_u(Pred_2,Why)),variant_u(Pred,Pred_2),trace_or_throw_ex(never_assert_u(Pred,Why))))).

%check_never_assert(Pred):- quietly_ex(ignore(( copy_term_and_varnames(Pred,Pred_2),umt(never_assert_u(Pred_2)),variant_u(Pred,Pred_2),trace_or_throw_ex(never_assert_u(Pred))))).
%check_never_assert(Pred):- quietly_ex((( copy_term_and_varnames(Pred,Pred_2),umt(never_assert_u(Pred_2,Why)), variant_u(Pred,Pred_2),trace_or_throw_ex(never_assert_u(Pred,Why))))),fail.

%% check_never_retract(+Pred) is semidet.
%
% Check Never Retract.
%

%check_never_retract(_Pred):-!.
check_never_retract(Pred):- quietly_ex(ignore(( copy_term_and_varnames(Pred,Pred_2),umt(never_retract_u(Pred_2,Why)),variant_u(Pred,Pred_2),trace_or_throw_ex(never_retract_u(Pred,Why))))).


:- thread_local(t_l:noDBaseMODs/1).
:- thread_local(t_l:side_effect_buffer/3).


kb_shared_local(_,_, ('=>' / _ )):- dumpST,throw_depricated,!.
kb_shared_local(_,_, _: ('=>' / _ )):- dumpST,throw_depricated,!.
kb_shared_local(_,_, ( _ :  '=>' / _ )):- dumpST,throw_depricated,!.
kb_shared_local(M,I,F/A):- I:kb_local(M:F/A),functor(P,F,A),
  (\+ clause(M:P,_) -> true;
  must((
   sanity((
   
   clause(M:P,_,Ref),
   clause_property(Ref,module(CM)),
   nop(listing(M:P)),
   CM==M))))).
 
maybe_ensure_abox(M,I) :-
  add_import_module(M,pfc_lib,end),
  M:import(pfccore:pfcDefault/2),
  I:import(pfccore:pfcDefault/2),
 % pfc_umt:abox_pred_list(PREDS)-> must_maplist(kb_shared_local(M,I),PREDS),
 forall(no_repeats(pfc_umt:pfcDatabaseTerm_DYN(F/A)),show_call(kb_shared_local(M,I,F/A))).



maybe_ensure_abox(M,I) :-
 pfc_umt:abox_pred_list(PREDS),
  M:module_transparent(PREDS),
  M:dynamic(PREDS),
   M:import(pfccore:pfcDefault/2),
   I:import(pfccore:pfcDefault/2),
 (I==M -> true ;
   ((M:export(M:PREDS),I:import(M:PREDS)))).

pfc_umt:abox_pred_list((([
     ('=>')/2,
     ('::::')/2,
%     '<=>'/2,
pfcTraced/1,
pfcSpied/2,
pfcTraceExecution/0,
pfcWarnings/1,
     'pt'/2,
     'nt'/3,
     'bt'/2,
t_l:whybuffer/2,
     fcUndoMethod/2,
     spft/3,
     fcAction/2,
     fcTmsMode/1,
     pfcQueue/1,
     pfcCurrentDb/1,     
     pfcHaltSignal/1,
     pfcDebugging/0,
     pfcSelect/2,
     pfcSearch/1]))).


red_line(Failed):- quietly((
  format('~N',[]),
  quietly_ex((doall((between(1,3,_),
  ansifmt(red,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find ~q in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n",[Failed]),
  ansifmt(yellow,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find red_line in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"))))))).








%% umt( +H ) is nondet.
%
% Clause Or Call.
%

:- meta_predicate(umt(*)).
umt(M:Goal):- !, umt(M,Goal).
umt(Goal):-  defaultQueryMt(M),umt(M,Goal).

%% umt( +M, +H ) is nondet.
%
% Clause Or Call.
%

:- meta_predicate(umt(+,*)).
umt(M,Goal):-
  (M:(((predicate_property(Goal,built_in)->call(Goal); 
      ((predicate_property(Goal, defined)->call(Goal);
         pfc_call(Goal))))))).
/*
umt(M,Goal):- 
  (M:(((predicate_property(Goal,built_in)->call(Goal); 
    ((predicate_property(Goal,defined)->call(Goal))*->true);pfc_call(Goal))))).
*/
%% clause_or_call( +H, ?B) is semidet.
%
% Clause Or Call.
%
clause_or_call(M:H,B):-is_ftVar(M),!,no_repeats(M:F/A,(f_to_mfa(H,M,F,A))),M:clause_or_call(H,B).
clause_or_call(isa(I,C),true):-!,umt(isa_asserted(I,C)).
clause_or_call(genls(I,C),true):-!,on_x_log_throw(umt(genls(I,C))).
clause_or_call(H,B):- clause(src_edit(_Before,H),B).
clause_or_call(H,B):- predicate_property(H,number_of_clauses(C)),predicate_property(H,number_of_rules(R)),((R*2<C) -> (clause_u(H,B)*->!;fail) ; clause_u(H,B)).
clause_or_call(H,true):- umt(should_call_for_facts(H)),no_repeats(on_x_log_throw(H)).


% as opposed to simply using clause(H,true).

%% should_call_for_facts( +H) is semidet.
%
% Should Call For Facts.
%
should_call_for_facts(H):- get_functor(H,F,A),umt(should_call_for_facts(H,F,A)).



%% should_call_for_facts( +VALUE1, ?F, ?VALUE3) is semidet.
%
% Should Call For Facts.
%
should_call_for_facts(_,F,_):- a(prologSideEffects,F),!,fail.
should_call_for_facts(H,_,_):- modulize_head(H,HH), \+ predicate_property(HH,number_of_clauses(_)),!.
should_call_for_facts(_,F,A):- clause_b(mpred_prop(_M,F,A,pfcRHS)),!,fail.
should_call_for_facts(_,F,A):- clause_b(mpred_prop(_M,F,A,pfcMustFC)),!,fail.
should_call_for_facts(_,F,_):- a(prologDynamic,F),!.
should_call_for_facts(_,F,_):- \+ a(pfcControlled,F),!.




a(C,I):-umt(((current_predicate(C/1),call(C,I)))).



%% is_relative( :TermV) is semidet.
%
% If Is A Relative.
%
is_relative(V):- (\+is_ftCompound(V)),!,fail.
is_relative(update(_)).
is_relative(replace(_)).
is_relative(rel(_)).
is_relative(+(X)):- \+ is_ftVar(X).
is_relative(-(X)):- \+ is_ftVar(X).
is_relative(*(X)):- \+ is_ftVar(X).



% ======================= 
% user''s program''s database
% ======================= 

%% update_single_valued_arg(+Module, +P, ?N) is semidet. 
%
% Update Single Valued Argument.
%
:- module_transparent( (update_single_valued_arg)/3).

update_single_valued_arg(M,M:Pred,N):-!,update_single_valued_arg(M,Pred,N).

update_single_valued_arg(world,P,N):- !, update_single_valued_arg(baseKB,P,N).
update_single_valued_arg(M,P,N):- \+ clause_b(mtHybrid(M)), clause_b(mtHybrid(M2)),!,update_single_valued_arg(M2,P,N).

update_single_valued_arg(M,P,N):- 
  get_unnegated_head_arg(N,P,UPDATE),
  is_relative(UPDATE),!,
  dtrace,
  replace_arg(P,N,OLD,Q),
  must_det_l((clause_u(Q),update_value(OLD,UPDATE,NEW),\+ is_relative(NEW), replace_arg(Q,N,NEW,R))),!,
  update_single_valued_arg(M,R,N).


update_single_valued_arg(M,P,N):- 
 umt((must_det_l((

  umt(mtHybrid(M)),
  mpred_type_args \= M,
  mpred_kb_ops \= M,
  get_unnegated_head_arg(N,P,UPDATE),
  replace_arg(P,N,Q_SLOT,Q),
  var(Q_SLOT),
  same_functors(P,Q),
  % get_source_ref1(U),
  must_det_l((
     % rtrace(attvar_op(assert_if_new,M:spft(P,U,ax))),
     % (umt(P)->true;(op_dir_mu(assert,assertz,P))),
     op_dir_mu(assert,assertz,M,P),
     doall((
          lookup_u(M:Q,E),
          UPDATE \== Q_SLOT,
          op_dir_mu(retract,erase(E),M,Q),         
          mpred_unfwc1(M:Q))))))))).


% ======================= 
% user''s program''s source reason
% ======================= 


%% get_source_ref( :TermU) is det.
%
% Get Source Ref (Current file or User)
%
:- module_transparent((get_source_ref)/1).
get_source_ref(O):- quietly_ex((current_why(U),(U=(_,_)->O=U;O=(U,ax)))),!.
get_source_ref(O):- quietly_ex((get_source_ref1(U),(U=(_,_)->O=U;O=(U,ax)))),!.

get_source_ref_stack(O):- findall(U,current_why(U),Whys),Whys\==[],!, U=(_,_),(Whys=[U]->O=U;O=(Whys,ax)),!.
get_source_ref_stack(O):- get_source_ref1(U),(U=(_,_)->O=U;O=(U,ax)),!.

get_startup_uu((mfl(baseKB, user_input, _), ax)):-true.

is_user_reason((_,U)):-atomic(U).

is_user_fact(P):-get_first_user_reason(P,UU),is_user_reason(UU).

lookup_spft(P,F,T):- umt(spft(P,F,T)).

get_first_real_user_reason(P,UU):- nonvar(P), UU=(F,T),
  quietly_ex((  ((((lookup_spft(P,F,T))),is_user_reason(UU))*-> true;
    ((((lookup_spft(P,F,T))), \+ is_user_reason(UU))*-> (!,fail) ; fail)))).

get_first_user_reason(P,(F,T)):-
  UU=(F,T),
  ((((lookup_spft(P,F,T))),is_user_reason(UU))*-> true;
    ((((lookup_spft(P,F,T))), \+ is_user_reason(UU))*-> (!,fail) ;
       (clause_asserted_u(P),get_source_ref(UU),is_user_reason(UU)))),!.
get_first_user_reason(_,UU):-get_source_ref_stack(UU),is_user_reason(UU),!.
get_first_user_reason(_,UU):- get_source_ref_stack(UU),!.
get_first_user_reason(P,UU):- must(ignore(((get_first_user_reason0(P,UU))))),!.
get_first_user_reason0(_,(M,ax)):-get_source_ref10(M).

%get_first_user_reason(_,UU):- get_source_ref(UU),\+is_user_reason(UU). % ignore(get_source_ref(UU)).

%% get_source_ref1(+Mt) is semidet.
%
% Get Source Ref Secondary Helper.
%
:- module_transparent((get_source_ref1)/1).
:- module_transparent((get_source_ref10)/1).
% get_source_ref1(M):- atom(M),must((get_source_ref10(N),atom(N))),!,M=N.
get_source_ref1(M):- ground(M),!.
get_source_ref1(M):- get_source_ref10(M),!.
get_source_ref1(_).

get_source_ref10(M):- current_why(M), nonvar(M) , M =mfl(_,_,_).
get_source_ref10(mfl(M,F,L)):- defaultAssertMt(M), source_location(F,L).

get_source_ref10(mfl(M,F,L)):- defaultAssertMt(M), current_source_file(F:L).
get_source_ref10(mfl(M,F,_L)):- defaultAssertMt(M), current_source_file(F).
get_source_ref10(mfl(M,_F,_L)):- defaultAssertMt(M).
%get_source_ref10(M):- (defaultAssertMt(M)->true;(atom(M)->(module_property(M,class(_)),!);(var(M),module_property(M,class(_))))).
get_source_ref10(M):- fail,dtrace,
 ((defaultAssertMt(M) -> !;
 (atom(M)->(module_property(M,class(_)),!);
    mpred_error(no_source_ref(M))))).

is_source_ref1(_).


% ======================= 
% user''s program''s database
% ======================= 
%clause_u(X,Y,Z):-umt(clause(X,Y,Z)).
clause_u(A,B,C):- umt(clause_i(A,B,C)).
%clause_u(X,Y):-umt(clause(X,Y)).
clause_u(A,B):- umt(clause_i(A,B)).
clause_u(A):- clause_i(A).
clause_asserted_u(A) :- clause_asserted_i(A).


%% assert_u(:X) is det.
%% asserta_u(:X) is det.
%% assertz_u(:X) is det.
%
% Assert For User Code.
%
assert_u(MH):-  fix_mp(clause(assert,assert_u),MH,M,H),get_unnegated_functor(H,F,A),assert_mu_fa(M,H,F,A).
asserta_u(MH):- fix_mp(clause(assert,asserta_u),MH,M,H),op_dir_mu(assert,asserta,M,H).
assertz_u(MH):- fix_mp(clause(assert,assertz_u),MH,M,H),op_dir_mu(assert,assertz,M,H).

%% asserta_mu(+M, ?X) is det.
%% assertz_mu(+M, ?X) is det.
%% assertz_mu(+M, ?X) is det.
%
% Assert(a/z/?) Module Unit.
%
assert_mu(M,P):- get_unnegated_functor(P,F,A),assert_mu_fa(M,P,F,A).
asserta_mu(M,P):- op_dir_mu(assert,asserta,M,P).
assertz_mu(M,P):- op_dir_mu(assert,assertz,M,P).


% :- kb_shared(baseKB:singleValuedInArg/2).
:- thread_local(t_l:assert_to/1).

%% assert_mu_fa(+Module, +Pred, +Functor, +Arity) is semidet.
%
% Assert For User Code 
% (Functor/Arity) on Module helps resolve specially typed predicates
%
assert_mu_fa(M,M2:Pred,F,A):- M == M2,!, assert_mu(M,Pred,F,A).
assert_mu_fa(M,_:Pred,F,A):- dtrace,sanity(\+ is_ftVar(Pred)),!, assert_mu(M,Pred,F,A).

%assert_mu_fa(M,Pred,F,_):- clause_b(singleValuedInArg(F,SV)),!,must(update_single_valued_arg(M,Pred,SV)),!.
%assert_mu_fa(M,Pred,F,A):- a(prologSingleValued,F),!,must(update_single_valued_arg(M,Pred,A)),!.

assert_mu_fa(M,Pred,F,_):- a(prologOrdered,F),!,op_dir_mu(assert,assertz,M,Pred).
assert_mu_fa(M,Pred,_,_):- t_l:assert_to(Where),!, (Where = a -> op_dir_mu(assert,asserta,M,Pred); op_dir_mu(assert,assertz,M,Pred)).
assert_mu_fa(M,Pred,_,1):- !, op_dir_mu(assert,assertz,M,Pred),!.
assert_mu_fa(M,Pred,_,_):- op_dir_mu(assert,asserta,M,Pred).


%% retract_u(:TermX) is nondet.
%
% Retract For User Code.
%
retract_u(MH):- fix_mp(clause(retract,retracta),MH,M,H),retract_mu(M,H).
retractall_u(MH):- fix_mp(clause(retract,retractall),MH,M,H),retractall_mu(M,H).

retractall_mu(M,PRED):- expand_to_hb(PRED,H,_), (PRED\==H ->retract_all_mu(M,H);retract_all_mu(M,PRED)).

retract_all_mu(M,H):- retract_mu(M,H),fail.
retract_all_mu(_).

%% retract_mu(M, :TermX) is semidet.
%
% Retract For User Code in Module.
%
retract_mu(M,(H:-B)):-!,clause_u(H,B,R),op_dir_mu(retract,erase(R),M,(H:-B)).
retract_mu(M,(H)):- clause_u(H,true,R),op_dir_mu(retract,erase(R),M,H).

%retract_mu(M,~(X)):-!,show_success(why,retract_eq_quitely_f(~(X))),must((expire_tabled_list(~(X)))),must((expire_tabled_list((X)))).
%retract_mu(M,(X)):-!,show_success(why,retract_eq_quitely_f((X))),must((expire_tabled_list(~(X)))),must((expire_tabled_list((X)))).


:- baseKB:multifile(baseKB:mtExact/1).
:- baseKB:dynamic(baseKB:mtExact/1).
:- baseKB:export(baseKB:mtExact/1).


% ============================================

%% correct_module( ?M, ?X, ?T) is semidet.
%
% Correct Module.
%
correct_module(M,G,T):-functor(G,F,A),quietly_must(correct_module(M,G,F,A,T)),!.

%% correct_module( ?M, ?Goal, ?F, ?A, ?T) is semidet.
%
% Correct Module.
%
correct_module(abox,G,F,A,T):- !, defaultAssertMt(M),correct_module(M,G,F,A,T).
correct_module(tbox,G,F,A,T):- !, fileAssertMt(M),correct_module(M,G,F,A,T).
correct_module(user,G,F,A,T):- fail,!,defaultAssertMt(M),correct_module(M,G,F,A,T).
correct_module(HintMt,_,_,_,HintMt):-!.  % TODO KEEP IT SIMPLE

correct_module(HintMt,Goal,F,A,OtherMt):-var(Goal),functor(Goal,F,A),!,correct_module(HintMt,Goal,F,A,OtherMt).
correct_module(HintMt,Goal,_,_,OtherMt):- predicate_property(HintMt:Goal,imported_from(OtherMt)).
correct_module(_,Goal,_,_,OtherMt):- predicate_property(Goal,imported_from(OtherMt)).
correct_module(HintMt,_,_,_,HintMt):- a(mtExact,HintMt).
correct_module(HintMt,Goal,_,_,HintMt):- predicate_property(HintMt:Goal,exported).
correct_module(_,Goal,_,_,OtherMt):- var(OtherMt),!, predicate_property(OtherMt:Goal,file(_)).
correct_module(_,Goal,_,_,OtherMt):- a(mtGlobal,OtherMt), predicate_property(OtherMt:Goal,file(_)).
correct_module(MT,_,_,_,MT):-!.

% =============================================================
%                 SIDE EFFECT PROCESSING
%
% TODO ISSUE https://github.com/TeamSPoon/PrologMUD/issues/7
% =============================================================


%% pfc_nochaining( +Goal) is semidet.
%
% PFC No Chaining.
%
pfc_nochaining(Goal):- locally(t_l:no_attempt_side_effects,call(Goal)).


%% pfc_with_chaining( +Goal) is semidet.
%
% PFC No Chaining.
%
pfc_with_chaining(Goal):- locally(- t_l:no_attempt_side_effects,call(Goal)).



%% op_dir_mu(+Op,+Type,+M, ?X) is det.
%
% Op(Assert/Retract) in Ordered in Module Unit.
%
:- module_transparent(op_dir_mu/4).
op_dir_mu(Op,Type,M,spft(P,mfl(KB,F,L),T)):-M\==KB,!,op_dir_mu(Op,Type,KB,spft(P,mfl(KB,F,L),T)).
op_dir_mu(Op,Type,M,X):- correct_module(M,X,T),T\==M,!,op_dir_mu(Op,Type,T,X).
op_dir_mu(Op,Type,M,M2:Pred):- sanity(M == M2),!, op_dir_mu(Op,Type,M,Pred).
op_dir_mu(Op,Type,M,X):- 
    strip_module(X,_,P), 
    sanity(Op==assert->check_never_assert(M:P);check_never_retract(M:P)), 
    must((expire_tabled_list(M:P),
    must(attvar_op(db_op_call(Op,Type),M:P)))).


:- module_transparent(attvar_op/2).

% % attvar_op(Op,Data):- deserialize_attvars(Data,Data0), attvar_op(Op,Data0).
attvar_op(Op,MData):-
 must_det_l((
   strip_module(Op,_,OpA), sanity( \+ atom(OpA)),
   fix_mp(clause(Op,OpA),MData,M,Data),
   add_side_effect(OpA,M:Data),
   quietly(current_prolog_flag(assert_attvars,true)->deserialize_attvars(Data,Data0);Data=Data0))),!,
   attempt_side_effect_mpa(M,OpA,Data0).


:- thread_local((t_l:use_side_effect_buffer , t_l:verify_side_effect_buffer)).

%% record_se is semidet.
%
% Record Se.
%
record_se:- (t_l:use_side_effect_buffer ; t_l:verify_side_effect_buffer).



%% add_side_effect( +Op, ?Data) is semidet.
%
% Add Side Effect.
%
add_side_effect(_,_):- ( \+  record_se ),!.
add_side_effect(Op,Data0):-get_source_ref1(Why),serialize_attvars(Data0,Data),assert(t_l:side_effect_buffer(Op,Data,Why)).



:- meta_predicate(db_op_call(*,*,?)).
db_op_call(_What,erase(E),_Data):- !, erase(E).
db_op_call(_What,How,Data):- call(How,Data).

% attempt_side_effect_mpa(M,OpA,Data):- record_se,!,add_side_effect(OpA,M:Data).
attempt_side_effect_mpa(M,db_op_call(_,retract_u0),Data0):- \+ lookup_u(M:Data0),!,fail.
attempt_side_effect_mpa(M,OpA,Data0):- \+ record_se, is_side_effect_disabled,!,mpred_warn('no_attempt_side_effects ~p',attempt_side_effect_mpa(M,OpA,Data0)).
% @TODO BROKEN phys ical_side_effect_call(M,assertz_i,Data0):- must((compile_aux_clauses(M:Data0))),!.
attempt_side_effect_mpa(M,OpA,Data0):- show_failure(M:call(M:OpA,M:Data0)).










:- thread_local(t_l:no_attempt_side_effects/0).

%% attempt_side_effect( +PSE) is semidet.
%
% Physical Side Effect.
%
attempt_side_effect(PSE):- to_physical_mpa(PSE,M,P,A),!,attempt_side_effect_mpa(M,P,A).

to_physical_mpa(PSE,M,P,A):- strip_module(PSE,M,PA),to_physical_pa(PA,P,A).
to_physical_pa(PA,P,A):-PA=..[P,A],!. to_physical_pa(PA,call,PA).


/*

  b_setval(th_asserts,[]),
  umt(G),
  b_getval(th_asserts,List).

attempt_side_effect_mpa(C) :- 
   b_getval(th_asserts,List),
   b_setval(th_asserts,[C|List]),!.



*/



%% no_side_effects( +P) is semidet.
%
% No Side Effects.
%
no_side_effects(P):-  (\+ is_side_effect_disabled->true;(get_functor(P,F,_),a(prologSideEffects,F))).



:-thread_local(t_l:side_effect_ok/0).
%% is_side_effect_disabled is semidet.
%
% If Is A Side Effect Disabled.
%
is_side_effect_disabled:- t_l:no_attempt_side_effects,!.
is_side_effect_disabled:- t_l:side_effect_ok,!,fail.
is_side_effect_disabled:- t_l:noDBaseMODs(_),!.






















:- fixup_exports.


