/** <module> mpred_terms
% Provides a common set of operators in translation between the several logical languages
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
:- module(pfc_ex,
   [begin_pfc/0,
          op(1050,xfx,('==>')),
          op(1050,xfx,'<==>'),
          op(1050,xfx,('<-')),
          op(1050,xfx,('<==')),
          op(1100,fx,('==>')),
          any_to_number/2,
          is_ftText/1,
          any_to_value/2,
          atom_to_value/2,
          mpred_test/1
          ]).

%:- use_module(library('pfc2.3/pfcsyntax')).

begin_pfc :- use_module(library(pfc_lib)).


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

:- meta_predicate on_x_rtrace(*).
on_x_rtrace(G):-on_x_debug(G).

:- meta_predicate 
   ain_expanded(:),
   mpred_add(:),
   mpred_ain(:),
   mpred_aina(:),
   mpred_ainz(:),
   mpred_ain(:,*),
   mpred_aina(:,*),
   mpred_ainz(:,*),
   mpred_retract(:),
   mpred_retractall(:).


mpred_axiom(Ax):-axiom(Ax).
file_begin(_).
repropagate(_).
otherwise.

%% mpred_ainz(+G, ?S) is semidet.
%
% PFC Ainz.
%
mpred_ainz(G):- locally(t_l:assert_to(z),mpred_ain(G)).
mpred_ainz(G,S):- locally(t_l:assert_to(z),mpred_ain(G,S)).

%% mpred_aina(+G, ?S) is semidet.
%
% PFC Aina.
%
mpred_aina(G):- locally(t_l:assert_to(a),mpred_ain(G)).
mpred_aina(G,S):- locally(t_l:assert_to(a),mpred_ain(G,S)).

%%  mpred_ain(P,S)
%
%  asserts P into the dataBase with support from S.
%
%  mpred_ain/2 and mpred_post/2 are the proper ways to add new clauses into the
%  database and have forward reasoning done.
%
mpred_ain(_:P):- P==end_of_file,!.
mpred_ain(MPRED):- must((mpred_to_pfc(MPRED,PFC),pfc_add(PFC))).
mpred_ain(MPRED,SUP):- must((mpred_to_pfc(MPRED+SUP,PFC+PFCSUP),pfc_add(PFC,PFCSUP))).


%%  ain_expanded(P,S)
%
%  asserts P into the dataBase with support from S.
%
ain_expanded(IIIOOO):- mpred_ain((IIIOOO)).
ain_expanded(IIIOOO,S):- mpred_ain(IIIOOO,S).
mpred_add(P):-mpred_ain(P).


mpred_withdraw(MPRED):- mpred_to_pfc(MPRED,PFC),pfc_rem(PFC).
mpred_withdraw(MPRED,S0):- mpred_to_pfc(MPRED+S0,PFC+S1),pfc_rem(PFC,S1).

mpred_retract(MPRED):- mpred_to_pfc(MPRED,PFC),pfc_clause(PFC),pfc_rem2(PFC).
mpred_retract_all(MPRED):- doall(mpred_retract(MPRED)).

mpred_retractall(MPRED):- expand_to_hb(MPRED,H,_),mpred_retract_all(H).




mpred_why(MPRED):- mpred_to_pfc(MPRED,PFC),!,(show_call(pfcWhy(PFC)*->true);(red_line,!,fail)).

mpred_test(MPRED):- mpred_to_pfc(MPRED,PFC),!,(show_call(umt(PFC)*->true);(pfc_call(PFC)*->true;red_line,!,fail)).

% mpred_test(MPRED):- mpred_to_pfc(MPRED,PFC),(show_success(pfcWhy(PFC))->true;(once(show_call(umt(PFC)))*->true;(red_line,!,fail))).

quietly_ex(G):- quietly(umt((G))),!.

trace_or_throw_ex(G):- trace_or_throw_ex(G).


is_asserted(P):- mpred_to_pfc(P,PP), pfc_clause(PP).


pp_DB :- umt((ignore(pfcPrintDB),listing)).


mpred_literal(MPRED):- mpred_to_pfc(MPRED,PFC), pfc_literal(PFC).


/*
pfc_term_expansion((P=>Q),(:- add((P=>Q)))).
pfc_term_expansion((P=>Q),(:- add(('<='(Q,P))))).  % speed-up attempt
pfc_term_expansion(('<='(P,Q)),(:- add(('<='(P,Q))))).
pfc_term_expansion((P<=>Q),(:- add((P<=>Q)))).
pfc_term_expansion((RuleName :::: Rule),(:- add((RuleName :::: Rule)))).
pfc_term_expansion(=>(P),(:- add(P))).
pfc_term_expansion(P,(:- add(P))).
*/

call_u(MPRED):- strip_module(MPRED,M,PRED),mpred_to_pfc(PRED,PFC),!,umt(M,PFC).





:- set_prolog_flag(pfc_ready,false).

:- op(500,fx,'~').
:- op(1050,xfx,('=>')).
:- op(1050,xfx,'<=>').
:- op(1050,xfx,('<=')).
:- op(1100,fx,('=>')).
:- op(1150,xfx,('::::')).


% :- use_module(library(pfc_lib)).
% :- use_module(library(pfc_ex)).



:- module_transparent(pfc_feature/1).
:- dynamic(pfc_feature/1).
:- export(pfc_feature/1).

pfc_feature(test_a_feature).

:- module_transparent(pfc_test_feature/2).
:- export(pfc_test_feature/2).

pfc_test_feature(Feature,Test):- pfc_feature(Feature)*-> mpred_test(Test) ; true.

:- system:import(pfc_feature/1).
:- system:export(pfc_feature/1).
:- system:import(pfc_test_feature/2).
:- system:export(pfc_test_feature/2).

:- system:import(pfc_feature/1).
:- system:export(pfc_feature/1).
:- baseKB:import(pfc_test_feature/2).
:- baseKB:export(pfc_test_feature/2).






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DUMPST ON WARNINGS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

skip_warning(informational).
skip_warning(information).
skip_warning(debug).

skip_warning(discontiguous).
skip_warning(query).
skip_warning(banner).
skip_warning(silent).
skip_warning(debug_no_topic).
skip_warning(break).
skip_warning(io_warning).
skip_warning(interrupt).
skip_warning(statistics).
% skip_warning(check).
skip_warning(compiler_warnings).


skip_warning(T):- \+ compound(T),!,fail.
skip_warning(_:T):- !, compound(T),functor(T,F,_),skip_warning(F).
skip_warning(T):-compound(T),functor(T,F,_),skip_warning(F).
base_message(T1,T2,_):- skip_warning(T1);skip_warning(T2);(thread_self(M),M\==main).
base_message(_,_,_):- \+ current_predicate(dumpST/0),!.
base_message(T,Type,Warn):- dmsg(message_hook(T,Type,Warn)),dumpST,dmsg(message_hook(T,Type,Warn)),!,fail.

:- multifile prolog:message//1, user:message_hook/3.
:- discontiguous(user:message_hook/3).
user:message_hook(T,Type,Warn):- fail, ( \+ current_prolog_flag(runtime_debug,0)),
   catch(once(base_message(T,Type,Warn)),_,fail),fail.


:- dynamic(system:test_results/3).

maybe_message_hook(compiler_warnings(_,[always(true,var,_),always(false,integer,_),
   always(false,integer,_),always(true,var,_),always(false,integer,_),always(false,integer,_)]),warning,[]):- !.

maybe_message_hook(import_private(_,_),_,_).
maybe_message_hook(check(undefined(_, _)),_,_).
maybe_message_hook(ignored_weak_import(header_sane,_),_,_).
% maybe_message_hook(_,warning,_).
maybe_message_hook(T,Type,Warn):-
  ignore(source_location(File,Line)),
  once((nl,dmsg(message_hook(T,Type,Warn)),nl,
  assertz(system:test_results(File:Line/T,Type,Warn)),dumpST,nl,dmsg(message_hook(File:Line:T,Type,Warn)),nl)),
  fail.

maybe_message_hook(_,error,_):- current_prolog_flag(runtime_debug, N),N>2,break.
maybe_message_hook(_,warning,_):- current_prolog_flag(runtime_debug, N),N>2,break.

system:test_completed:- list_problems,test_completed_exit_maybe(4).
system:test_retake:- list_problems,test_completed_exit_maybe(7).


list_problems:-listing(system:test_results/3),
  foo:listing(header_sane:_),
  nop((listing(user:_))).

test_completed_exit(4):- halt(4).
test_completed_exit(5):- halt(5).
test_completed_exit(N):- (debugging-> break ; true), halt(N).

test_completed_exit_maybe(_):- system:test_results(_,error,_),test_completed_exit(9).
test_completed_exit_maybe(_):- system:test_results(_,warning,_),test_completed_exit(3).
test_completed_exit_maybe(_):- system:test_results(_,warn,_),test_completed_exit(3).
test_completed_exit_maybe(N):- test_completed_exit(N).

set_file_abox_module(User):- '$set_typein_module'(User), '$set_source_module'(User),set_fileAssertMt(User).

set_file_abox_module_wa(User):- set_file_abox_module(User),set_defaultAssertMt(User).


:- multifile prolog:message//1, user:message_hook/3.
% user:message_hook(import_private(pfc_lib,_:_/_),warning,_):- source_location(_,_),!.
user:message_hook(io_warning(_,'Illegal UTF-8 start'),warning,_):- source_location(_,_),!.
user:message_hook(T,Type,Warn):-
  ((current_prolog_flag(runtime_debug, N),N>2) -> true ; source_location(_,_)),
  memberchk(Type,[error,warning]),once(maybe_message_hook(T,Type,Warn)),fail.



mpred_loader_file.
%system:term_expansion(end_of_file,_):-must(check_clause_counts),fail.
%system:term_expansion(EOF,_):-end_of_file==EOF,must(check_clause_counts),fail.





:- meta_predicate(mpred_to_pfc(*,*)).
mpred_to_pfc(MPRED,PFC):- must(=(MPRED,PFC)),!.
mpred_to_pfc(MPRED,PFC):- must(mp2pfc(MPRED,PFC)),!.



mpred_info(I):-mpred_to_pfc(I,O),!,
 % get_unnegated_functor(O,F,A),
 with_output_to(user_error,
 ((dmsg("======================================================================="),
  listing(O),
  dmsg("======================================================================="),
  maplist(mp_printAll(O),
 [+pfcType(O,v),
  call(pfcWhy(O)),
  +pfcChild(O,v),
  pfcFact(O),
  axiom(O),
  wellFounded(O),
  pfcSupported(local,O),
  pfcSupported(cycles,O),
  assumption(O),
  pfcTraced(O)])),
 dmsg("======================================================================="))).


mp_printAll(S,call(O)):- !,
  subst(O,S,s,NAME),
  nl,flush_output,fmt("=================="),wdmsg(NAME),wdmsg("---"),flush_output,
  doall(((flush_output,O,flush_output)*->true;wdmsg(false=NAME))),fmt("=================="),nl,flush_output.

mp_printAll(S,+(O)):- !,
  subst(O,S,s,NAME),subst(O,v,V,CALL),functor(O,F,_),
  nl,flush_output, fmt("=================="),wdmsg(NAME),wdmsg("---"),flush_output,
  doall(((flush_output,CALL,flush_output)*->fmt9(V);(fail=F))),nl,fmt("=================="),nl,flush_output.

mp_printAll(S,(O)):-  !,  functor(O,F,A),mp_nnvv(S,O,F,A),flush_output.

mp_nnvv(_,(O),F,1):- !, doall(((flush_output,O,flush_output)*->wdmsg(+F);wdmsg(-F))).
mp_nnvv(S,(O),_,_):- !, subst(O,S,s,NAME), doall(((flush_output,O,flush_output)*->wdmsg(-NAME);wdmsg(+NAME))).


mpred_must(G):- must(mpred_test(G)).



%% match_source_ref1( :TermARG1) is semidet.
%
% Match Source Ref Secondary Helper.
%
match_source_ref1(ax):-!.
match_source_ref1(mfl(_,_,_)).

%% make_uu_remove( :TermU) is semidet.
%
% Make Uu Remove.
%
make_uu_remove((_,ax)).


%% has_functor( :TermC) is semidet.
%
% Has Functor.
%
has_functor(_):-!,fail.
has_functor(F/A):-!,is_ftNameArity(F,A),!.
has_functor(C):- (\+ is_ftCompound(C)),!,fail.
has_functor(C):-is_ftCompound(C),\+is_list(C).


%% mpred_each_literal( +P, ?E) is semidet.
%
% PFC Each Literal.
%
mpred_each_literal(P,E):-is_ftNonvar(P),P=(P1,P2),!,(mpred_each_literal(P1,E);mpred_each_literal(P2,E)).
mpred_each_literal(P,P). %:-conjuncts_to_list(P,List),member(E,List).



%% retract_eq_quitely( +H) is semidet.
%
% Retract Using (==/2) (or =@=/2) ) Quitely.
%
retract_eq_quitely(H):- umt(retract_eq_quitely_f(H)).

%% retract_eq_quitely_f( +H) is semidet.
%
% Retract Using (==/2) (or =@=/2) ) Quitely False.
%
retract_eq_quitely_f((H:-B)):- !,clause_asserted_i(H,B,Ref),erase(Ref).
retract_eq_quitely_f(pfclog(H)):- retract_eq_quitely_f(H),fail.
retract_eq_quitely_f((H)):- clause_asserted_i(H,true,Ref),erase(Ref).


%% assert_eq_quitely( +H) is semidet.
%
% Assert Using (==/2) (or =@=/2) ) Quitely.
%
assert_eq_quitely(H):- attvar_op(db_op_call(assert,assert_if_new),H).


%% mpred_is_tautology( +Var) is semidet.
%
% PFC If Is A Tautology.
%
% :- module_transparent( (mpred_is_tautology)/1).
mpred_is_tautology(V):- (is_ftVar(V) -> true;(copy_term_nat(V,VC),numbervars(VC),mpred_is_taut(VC))),!.



%% mpred_is_taut( :TermA) is semidet.
%
% PFC If Is A Taut.
%
mpred_is_taut(A):-var(A),!.
mpred_is_taut(A:-B):-!,mpred_is_taut(B==>A).
mpred_is_taut(A<-B):-!,mpred_is_taut(B==>A).
mpred_is_taut(A<==>B):-!,(mpred_is_taut(A==>B);mpred_is_taut(B==>A)).
mpred_is_taut(A==>B):- A==B,!.
mpred_is_taut((B,_)==>A):- mpred_is_assertable(B),mpred_is_taut(A==>B),!.
mpred_is_taut((_,B)==>A):- mpred_is_assertable(B),mpred_is_taut(A==>B),!.
mpred_is_taut(B==>(A,_)):- mpred_is_assertable(A),mpred_is_taut(A==>B),!.
mpred_is_taut(B==>(_,A)):- mpred_is_assertable(A),mpred_is_taut(A==>B),!.


% baseKB:decl_database_hook(Op,Hook):- loop_check_nr(pfc_provide_storage_op(Op,Hook)).


%% is_retract_first( +VALUE1) is semidet.
%
% If Is A Retract First.
%
is_retract_first(one).
is_retract_first(a).






clause_u(A,B,C):- clause_i(A,B,C).
clause_u(A,B):- clause_i(A,B).
clause_u(A):- clause_i(A).
clause_asserted_u(A) :- clause_asserted_i(A).



%% mpred_is_assertable( +X) is semidet.
%
% PFC If Is A Assertable.
%
mpred_is_assertable(X):- mpred_literal_nv(X),\+ functor(X,{},_).

%% mpred_literal_nv( +X) is semidet.
%
% PFC Literal Nv.
%
mpred_literal_nv(X):-is_ftNonvar(X),mpred_literal(X).



if_missing1(Q):- mpred_literal_nv(Q), umt( \+ ~ Q), if_missing_mask(Q,R,Test),!, lookup_u(R), Test.


%% if_missing_mask( +Q, ?R, ?Test) is semidet.
%
% If Missing Mask.
%

if_missing_mask(M:Q,M:R,M:Test):- nonvar(Q),!,if_missing_mask(Q,R,Test).
if_missing_mask(Q,~Q,\+Q):- \+ is_ftCompound(Q),!.

if_missing_mask(ISA, ~ ISA, \+ ISA):- functor(ISA,F,1),(F==tSwim;umt(functorDeclares(F))),!.
if_missing_mask(HB,RO,TestO):- once(mpred_rule_hb(HB,H,B)),B\==true,HB\==H,!,if_missing_mask(H,R,TestO),subst(HB,H,R,RO).
if_missing_mask(Q,R,Test):-
   which_missing_argnum(Q,N),
   if_missing_n_mask(Q,N,R,Test),!.
if_missing_mask(ISA, ~ ISA, \+ ISA).


%% if_missing_n_mask( +Q, ?N, ?R, ?Test) is semidet.
%
% If Missing Mask.
%
if_missing_n_mask(Q,N,R,Test):-
  get_unnegated_head_arg(N,Q,Was),
  (nonvar(R)-> (which_missing_argnum(R,RN),get_unnegated_head_arg(RN,R,NEW));replace_arg(Q,N,NEW,R)),!,
   Test=dif:dif(Was,NEW).

/*
Old version
if_missing_mask(Q,N,R,dif:dif(Was,NEW)):- 
 must((is_ftNonvar(Q),acyclic_term(Q),acyclic_term(R),functor(Q,F,A),functor(R,F,A))),
  (singleValuedInArg(F,N) -> 
    (get_unnegated_head_arg(N,Q,Was),replace_arg(Q,N,NEW,R));
    ((get_unnegated_head_arg(N,Q,Was),is_ftNonvar(Was)) -> replace_arg(Q,N,NEW,R);
        (N=A,get_unnegated_head_arg(N,Q,Was),replace_arg(Q,N,NEW,R)))).
*/


%% which_missing_argnum( +VALUE1, ?VALUE2) is semidet.
%
% Which Missing Argnum.
%
which_missing_argnum(Q,N):-
 must((acyclic_term(Q),is_ftCompound(Q),get_functor(Q,F,A))),
 F\=t,
  (umt(singleValuedInArg(F,N)) -> true;
    ((get_unnegated_head_arg(N,Q,Was),is_ftNonvar(Was)) -> true; ( A>1 -> N=A ; fail))).



:- export(any_to_number/2).
%% any_to_value( ?Var, ?Var) is semidet.
%
% Any Converted To Value.
%
any_to_value(Var,Var):-var(Var),!.
any_to_value(V,Term):-atom(V),!,atom_to_value(V,Term).
any_to_value(A,V):-any_to_number(A,V).
any_to_value(A,A).


%% any_to_number( :TermN, ?N) is semidet.
%
% Any Converted To Number.
%
any_to_number(N,N):- number(N),!.
any_to_number(ftDiceFn(A,B,C),N):- ground(A),if_defined(roll_dice(A,B,C,N)),!.
any_to_number(A,N):-atom(A),atom_to_value(A,V),A\=V,any_to_number(V,N).
any_to_number(A,N):- catch(number_string(N,A),_,fail).

%% atom_to_value( ?V, :TermTerm) is semidet.
%
% Atom Converted To Value.
%
atom_to_value(V,Term):-not(atom(V)),!,any_to_value(V,Term).
% 56
atom_to_value(V,Term):- catch((read_term_from_atom(V,Term,[variable_names([])])),_,fail),!.
% 18d18+4000
atom_to_value(V,ftDiceFn(T1,T2,+T3)):- atomic_list_concat_safe([D1,'d',D2,'+',D3],V), atom_to_value(D1,T1),atom_to_value(D2,T2),atom_to_value(D3,T3),!.
atom_to_value(V,ftDiceFn(T1,T2,-T3)):- atomic_list_concat_safe([D1,'d',D2,'-',D3],V), atom_to_value(D1,T1),atom_to_value(D2,T2),atom_to_value(D3,T3),!.



%% is_ftText( ?Arg) is semidet.
%
% If Is A Format Type Text.
%
is_ftText(Arg):- string(Arg),!.
is_ftText(Arg):- \+ compound(Arg),!,fail.
is_ftText(Arg):- functor(Arg,s,_),!.
is_ftText([Arg|_]):-string(Arg),!.
is_ftText(Arg):- is_ftVar(Arg),!,fail.
is_ftText(Arg):- text_to_string_safe(Arg,_),!.
is_ftText(Arg):- functor(Arg,S,_), ereq(resultIsa(S,ftText)).

:- kb_global(baseKB:ftText/1).
:- assert_if_new(baseKB:(ftText(A):- !, if_defined(term_is_ft(A, ftText),is_ftText(A)),!)).

% =======================================================
% term utils
% =======================================================

:- was_export(inverse_args/2).



%% inverse_args( ?AR, ?GS) is semidet.
%
% Inverse Arguments.
%
inverse_args([AR,GS],[GS,AR]):-!.
inverse_args([AR,G,S],[S,G,AR]):-!.
inverse_args([A,R,G,S],[S,R,G,A]):-!.
inverse_args([P,A,R,G,S],[S,A,R,G,P]):-!.

:- was_export(same_vars/2).



%% same_vars( ?T1, ?T2) is semidet.
%
% Same Variables.
%
same_vars(T1,T2):-term_variables(T1,V1),term_variables(T2,V2),!,V1==V2.




%% replace_arg( ?C, :PRED3A, ?VAR, ?CC) is semidet.
%
% Replace Argument.
%
replace_arg(C,A,_VAR,_CC):-sanity((is_ftCompound(C),integer(A))),fail.
replace_arg((C:-B),A,VAR,(CC:-B)):-!,replace_arg(C,A,VAR,CC).
replace_arg(~ (C),A,VAR,~(CC)):-!,replace_arg(C,A,VAR,CC).
replace_arg( \+ (C),A,VAR,~(CC)):-!,replace_arg(C,A,VAR,CC).
replace_arg(M:(C),A,VAR,M:(CC)):-!,replace_arg(C,A,VAR,CC).
replace_arg(C,0,VAR,CC):-!, C=..[_|ARGS],CC=..[VAR|ARGS].
replace_arg(C,1,VAR,CC):-!, C=..[F,_|ARGS],CC=..[F,VAR|ARGS].
replace_arg(C,2,VAR,CC):-!, C=..[F,A,_|ARGS],CC=..[F,A,VAR|ARGS].
replace_arg(C,3,VAR,CC):-!, C=..[F,A,B,_|ARGS],CC=..[F,A,B,VAR|ARGS].
% replace_arg(C,A,VAR,CO):- duplicate_term(C,CC),setarg(A,CC,VAR),!,CC=CO.
replace_arg(C,A,VAR,CC):- C=..FARGS,replace_nth_arglist(FARGS,A,VAR,FARGO),!,CC=..FARGO.

% :- mpred_trace_nochilds(replace_arg/4).

%% replace_nth_arglist(+List, +Index, +Element, -NewList) is det[private]
% Replace the Nth (1-based) element of a list.
% :- mpred_trace_nochilds(replace_nth_arglist/4).



%% replace_nth_arglist( :TermARG1, ?VALUE2, ?VAR, :TermVAR) is semidet.
%
% Replace Nth Arglist.
%
replace_nth_arglist([],_,_,[]):- !.
replace_nth_arglist([_|ARGO],0,VAR,[VAR|ARGO]):- !.
replace_nth_arglist([T|FARGS],A,VAR,[T|FARGO]):- 
    A2 is A-1,replace_nth_arglist(FARGS,A2,VAR,FARGO).





%% replace_nth_ref( :TermARG1, ?N, ?OldVar, ?NewVar, :TermARG5) is semidet.
%
% Replace Nth Ref.
%
replace_nth_ref([],_N,_OldVar,_NewVar,[]):- !,trace_or_throw_ex(missed_the_boat).
replace_nth_ref([OldVar|ARGS],1,OldVar,NewVar,[NewVar|ARGS]):- !.
replace_nth_ref([Carry|ARGS],Which,OldVar,NewVar,[Carry|NEWARGS]):- 
 Which1 is Which-1,
 replace_nth_ref(ARGS,Which1,OldVar,NewVar,NEWARGS),!.


% :- mpred_trace_nochilds(update_value/3).



%% update_value( ?OLD, ?NEW, ?NEXT) is semidet.
%
% Update Value.
%
update_value(OLD,NEW,NEXT):- var(NEW),!,trace_or_throw_ex(logicmoo_bug(update_value(OLD,NEW,NEXT))).
update_value(OLD,NEW,NEWV):- var(OLD),!,compute_value_no_dice(NEW,NEWV).
update_value(OLD,X,NEW):- is_list(OLD),!,list_update_op(OLD,X,NEW),!.
update_value(OLDI,+X,NEW):- compute_value(OLDI,OLD),number(OLD),catch(NEW is OLD + X,_,fail),!.
update_value(OLDI,-X,NEW):- compute_value(OLDI,OLD),number(OLD),catch(NEW is OLD - X,_,fail),!.
update_value(OLDI,X,NEW):- number(X),X<0,compute_value(OLDI,OLD),number(OLD),catch(NEW is OLD + X,_,fail),!.
update_value(_,NEW,NEWV):- compute_value_no_dice(NEW,NEWV),!.




%% flatten_append( ?First, ?Last, ?Out) is semidet.
%
% Flatten Append.
%
flatten_append(First,Last,Out):-flatten([First],FirstF),flatten([Last],LastF),append(FirstF,LastF,Out),!.




%% list_update_op( ?OLDI, :TermX, ?NEW) is semidet.
%
% List Update Oper..
%
list_update_op(OLDI,+X,NEW):-flatten_append(OLDI,X,NEW),!.
list_update_op(OLDI,-X,NEW):-flatten([OLDI],OLD),flatten([X],XX),!,list_difference_eq(OLD,XX,NEW),!.




%% compute_value_no_dice( ?NEW, ?NEW) is semidet.
%
% Compute Value No Dice.
%
compute_value_no_dice(NEW,NEW):- compound(NEW),functor_catch(NEW,ftDiceFn,_),!.
compute_value_no_dice(NEW,NEW):- compound(NEW),functor_catch(NEW,ftDice,_),!.
compute_value_no_dice(NEW,NEWV):-compute_value(NEW,NEWV).




%% compute_value( ?NEW, ?NEWV) is semidet.
%
% Compute Value.
%
compute_value(NEW,NEWV):-catch(NEWV is NEW,_,fail),!.
compute_value(NEW,NEWV):-catch(any_to_value(NEW,NEWV),_,fail),!.
compute_value(NEW,NEW).




%% insert_into( :TermARGS, ?VALUE2, ?Insert, :TermInsert) is semidet.
%
% Insert Converted To.
%
insert_into(ARGS,0,Insert,[Insert|ARGS]):- !.
insert_into([Carry|ARGS],After,Insert,[Carry|NEWARGS]):- 
   After1 is After - 1,
   insert_into(ARGS,After1,Insert,NEWARGS).



% ========================================
% is_holds_true/is_holds_false
% ========================================


:- was_export(into_plist/2).

%= 	 	 

%% into_plist( ?In, ?Out) is semidet.
%
% Converted To Plist.
%
into_plist(In,Out):-into_plist_arities(2,12,In,Out).

:- was_export(into_plist_arities/4).

%= 	 	 

%% into_plist_arities( ?Min, ?Max, ?PLIST, ?PLISTO) is semidet.
%
% Converted To Plist Arities.
%
into_plist_arities(Min,Max,PLIST,PLISTO):- var(PLIST),!,between(Min,Max,X),length(PLIST,X),PLISTO=PLIST.
into_plist_arities(_,_,[P|LIST],[P|LIST]):-var(P),!.
into_plist_arities(_,_,[(t)|PLIST],PLIST):-!.  % t is our versuion of '$holds' or call/N
into_plist_arities(_,_,plist(P,LIST),[P|LIST]):-!.
into_plist_arities(_,_,Call,PLIST):- Call=..PLIST. % finally the fallthrue



%= 	 	 

%% never_mpred_tcall( ?VALUE1) is semidet.
%
% Never Managed Predicate Managed Predicate.
%

never_mpred_tcall(mpred_prop).
never_mpred_tcall(isa).
never_mpred_tcall(arity).


local_qh_mpred_prop(M,F,A,C):- umt(mpred_prop(M,F,A,C)).


% :- setup_mpred_ops.


                   
%= 	 	 

:- meta_predicate(if_result(0,0)).

%= 	 	 

%% if_result( :GoalTF, :Goal) is semidet.
%
% If Result.
%
if_result(TF,Call):-(TF->Call;true).




%= 	 	 

%% mpred_plist_t( ?P, :TermLIST) is semidet.
%
% Managed Predicate Plist True Stucture.
%
/* mpred_plist_t(P,[]):-!,t(P). */
mpred_plist_t(P,LIST):-var(P),!,is_list(LIST),CALL=..[t,P|LIST],on_x_debug((CALL)).
mpred_plist_t(t,[P|LIST]):-!, mpred_plist_t(P,LIST).
%mpred_plist_t(mpred_isa,[C,_A,I]):-!,ground(I:C),local_qh_mpred_isa(C,I).
mpred_plist_t(isa,[I,C]):-!,call(call,t,C,I).
mpred_plist_t(P,_):-never_mpred_tcall(P),!,fail.
mpred_plist_t(P,[L|IST]):-is_holds_true(P),!,mpred_plist_t(L,IST).
mpred_plist_t(P,LIST):-is_holds_false(P),!,umt(mpred_f(LIST)).
mpred_plist_t(P,LIST):- CALL=..[t,P|LIST],on_x_debug(CALL).


:- meta_predicate(mpred_fa_call(?,?,0)).



%= 	 	 

%% mpred_fa_call( ?F, ?UPARAM2, :Goal) is semidet.
%
% Managed Predicate Functor-arity Call.
%
mpred_fa_call(F,A,Call):- var(F),!,
 no_repeats(F,(clause_b(support_hilog(F,A));clause_b(arity(F,A)))), 
   once((F\==t, 
   \+ a(rtNotForUnboundPredicates,F),current_predicate(F,M:_OtherCall))),
    on_x_debug(M:Call).
mpred_fa_call(M:F,A,Call):- nonvar(M),!,mpred_fa_call(F,A,M:Call).
mpred_fa_call(F,_,Call):-F\==t,current_predicate(F,M:_OtherCall),!,M:Call.


%= 	 	 

%% mpred_fact_arity( ?VALUE1, ?VALUE2) is semidet.
%
% Managed Predicate Fact Arity.
%
mpred_fact_arity(F,A):- umt(arity(F,A)),
  suggest_m(M),
  once(local_qh_mpred_prop(M,F,A,prologHybrid);
     local_qh_mpred_prop(M,F,A,pfcControlled);
     local_qh_mpred_prop(M,F,A,prologPTTP);
     local_qh_mpred_prop(M,F,A,prologKIF)),!.


%= 	 	 

%% prologHybridFact( ?G) is semidet.
%
% Prolog Hybrid Fact.
%
prologHybridFact(G):- (var(G)->(mpred_fact_arity(F,A),functor(G,F,A));true),into_mpred_form(G,M),!,no_repeats(umt(M)).





%% mpred_pbody( +H, ?B, ?R, ?BIn, ?WHY) is semidet.
%
% PFC Pbody.
%
mpred_pbody(H,B,_R,fail,deduced(backchains)):- get_bc_clause(H,(H:-B)),!.
mpred_pbody(H,infoF(INFO),R,B,Why):-!,mpred_pbody_f(H,INFO,R,B,Why).
mpred_pbody(H,B,R,BIn,WHY):- is_true(B),!,BIn=B,get_why(H,H,R,WHY).
mpred_pbody(H,B,R,B,asserted(R,(H:-B))).


%% get_why( +VALUE1, ?CL, ?R, :TermR) is semidet.
%
% Get Generation Of Proof.
%
get_why(_,CL,R,asserted(R,CL:-U)):- clause_u(spft(CL, U, ax),true),!.
get_why(H,CL,R,deduced(R,WHY)):- (mpred_get_support(H,WH)*->WHY=(H=WH);(mpred_get_support(CL,WH),WHY=(CL=WH))).

mpred_get_support(P,S):-pfcGetSupport(P,S).


%% mpred_pbody_f( +H, ?CL, ?R, ?B, ?WHY) is semidet.
%
% PFC Pbody False.
%
mpred_pbody_f(H,CL,R,B,WHY):- CL=(B==>HH),sub_term_eq(H,HH),!,get_why(H,CL,R,WHY).
mpred_pbody_f(H,CL,R,B,WHY):- CL=(HH<-B),sub_term_eq(H,HH),!,get_why(H,CL,R,WHY).
mpred_pbody_f(H,CL,R,B,WHY):- CL=(HH<==>B),sub_term_eq(H,HH),get_why(H,CL,R,WHY).
mpred_pbody_f(H,CL,R,B,WHY):- CL=(B<==>HH),sub_term_eq(H,HH),!,get_why(H,CL,R,WHY).
mpred_pbody_f(H,CL,R,fail,infoF(CL)):- trace_or_throw_ex(mpred_pbody_f(H,CL,R)).


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
  mpred_rule_hb(HB,H,B),
  term_slots(H,Slots),  
  (Slots==[]->
     all_different_head_vals(B);
    (lock_vars(Slots),all_different_head_vals_2(H,Slots),unlock_vars(Slots))),!.
  

all_different_head_vals_2(_H,[]):-!.
all_different_head_vals_2(H,[A,R|EST]):-get_unnegated_head_arg(_,H,E1),E1 ==A,dif(A,E2),get_unnegated_head_arg(_,H,E2),\+ contains_var(A,E2),all_different_vals(dif_matrix,[A,E2,R|EST]),!.
all_different_head_vals_2(_H,[A,B|C]):-all_different_vals(dif_matrix,[A,B|C]),!.
all_different_head_vals_2(HB,_):- \+ compound(HB),!.
all_different_head_vals_2(H,[A]):-get_unnegated_head_arg(_,H,E1),E1 ==A, H=..[_|ARGS], all_different_vals(dif_matrix,ARGS),!.
all_different_head_vals_2(H,[A]):-get_unnegated_head_arg(_,H,E1),E1 ==A, get_unnegated_head_arg(_,H,E2), A\==E2, \+ contains_var(A,E2), dif(A,E2),!.
all_different_head_vals_2(H,[A]):-get_unnegated_head_arg(_,H,E1),E1\==A, compound(E1), contains_var(A,E1), all_different_head_vals_2(E1,[A]),!.
all_different_head_vals_2(_,_).
   	 

%% mpred_rule_hb( +Outcome, ?OutcomeO, ?AnteO) is semidet.
%
% Calculate PFC Rule Head+body.
%
mpred_rule_hb(Outcome,OutcomeO,Body):- nonvar(OutcomeO),!,mpred_rule_hb(Outcome,OutcomeN,Body),must(OutcomeO=OutcomeN).
mpred_rule_hb(Outcome,OutcomeO,BodyO):- nonvar(BodyO),!,mpred_rule_hb(Outcome,OutcomeO,BodyN),must(BodyN=BodyO).
mpred_rule_hb(Outcome,OutcomeO,AnteO):- 
  quietly((mpred_rule_hb_0(Outcome,OutcomeO,Ante),
  mpred_rule_hb_0(Ante,AnteO,_))).
% :-mpred_trace_nochilds(mpred_rule_hb/3).


%% mpred_rule_hb_0( +Rule, -Head, -Body) is nondet.
%
% Calculate PFC rule Head+Body  Primary Helper.
%


mpred_rule_hb_0(Outcome,OutcomeO,true):-is_ftVar(Outcome),!,OutcomeO=Outcome.
mpred_rule_hb_0(Outcome,OutcomeO,true):- \+compound(Outcome),!,OutcomeO=Outcome.
mpred_rule_hb_0((Outcome1,Outcome2),OutcomeO,AnteO):- mpred_rule_hb(Outcome1,Outcome1O,Ante1),mpred_rule_hb(Outcome2,Outcome2O,Ante2),
                   conjoin(Outcome1O,Outcome2O,OutcomeO),
                   conjoin(Ante1,Ante2,AnteO).
mpred_rule_hb_0((Ante1==>Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Ante1=>Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Ante1->Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Ante1*->Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
% mpred_rule_hb_0((Outcome/Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(rhs([Outcome]),OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
% mpred_rule_hb_0(rhs([OutcomeH|OutcomeT]),OutcomeO,Ante2):- !, mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0({Outcome},OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Outcome<-Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Ante1 & Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Ante1 , Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Outcome<==>Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Ante1<==>Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(_::::Outcome,OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb_0(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(bt(Outcome,Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(pt(Ante1,Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(pk(Ante1a,Ante1b,Outcome),OutcomeO,(Ante1a,Ante1b,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(nt(Ante1a,Ante1b,Outcome),OutcomeO,(Ante1a,Ante1b,Ante2)):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(spft(Outcome,Ante1a,Ante1b),OutcomeO,(Ante1a,Ante1b,Ante2)):- (nonvar(Outcome)-> ! ; true),mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0(que(Outcome,_),OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
% mpred_rule_hb_0(pfc Default(Outcome),OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), mpred_rule_hb(Outcome,OutcomeO,Ante2).
mpred_rule_hb_0((Outcome:-Ante),Outcome,Ante):-(nonvar(Outcome)-> ! ; true).
mpred_rule_hb_0(Outcome,Outcome,true).


%% ain_minfo( +G) is semidet.
%
% Assert If New Metainformation.
%
:- module_transparent(ain_minfo/1).
ain_minfo(G):-ain_minfo(assertz_if_new,G).

%% ain_minfo( :PRED1How, ?H) is semidet.
%
% Assert If New Metainformation.
%
:- module_transparent(ain_minfo/2).
ain_minfo(How,(H:-True)):-is_true(True),must(is_ftNonvar(H)),!,ain_minfo(How,H).
/*
ain_minfo(How,(H<-B)):- !,ain_minfo(How,(H:-infoF(H<-B))),!,get_bc_clause(H,Post),ain_minfo(How,Post),ain_minfo_2(How,(B:-infoF(H<-B))).
ain_minfo(How,(B==>H)):- !,ain_minfo(How,(H:-infoF(B==>H))),!,ain_minfo_2(How,(B:-infoF(B==>H))).
ain_minfo(How,(B<==>H)):- !,ain_minfo(How,(H:-infoF(B<==>H))),!,ain_minfo(How,(B:-infoF(B<==>H))),!.
ain_minfo(How,((A,B):-INFOC)):-mpred_is_info(INFOC),(is_ftNonvar(A);is_ftNonvar(B)),!,ain_minfo(How,((A):-INFOC)),ain_minfo(How,((B):-INFOC)),!.
ain_minfo(How,((A;B):-INFOC)):-mpred_is_info(INFOC),(is_ftNonvar(A);is_ftNonvar(B)),!,ain_minfo(How,((A):-INFOC)),ain_minfo(How,((B):-INFOC)),!.
ain_minfo(How,(-(A):-infoF(C))):-is_ftNonvar(C),is_ftNonvar(A),!,ain_minfo(How,((A):-infoF((C)))). % attvar_op(How,(-(A):-infoF(C))).
ain_minfo(How,(~(A):-infoF(C))):-is_ftNonvar(C),is_ftNonvar(A),!,ain_minfo(How,((A):-infoF((C)))). % attvar_op(How,(-(A):-infoF(C))).
ain_minfo(How,(A:-INFOC)):- is_ftNonvar(INFOC), get_bc_clause(A,(A:-INFOC)),!,attvar_op(How,(A:-INFOC)),!.
ain_minfo(How,bt(_ABOX,H,_)):-!,get_bc_clause(H,Post),attvar_op(How,Post).
ain_minfo(How,nt(H,Test,Body)):-!,attvar_op(How,(H:-fail,nt(H,Test,Body))).
ain_minfo(How,pt(H,Body)):-!,attvar_op(How,(H:-fail,pt(H,Body))).
ain_minfo(How,(A0:-INFOC0)):- mpred_is_info(INFOC0), copy_term_and_varnames((A0:-INFOC0),(A:-INFOC)),!,must((mpred_rewrap_h(A,AA),imploded_copyvars((AA:-INFOC),ALLINFO), attvar_op(How,(ALLINFO)))),!.
%ain_minfo(How,G):-pfc_trace_msg(skipped_add_meta_facts(How,G)).
*/
ain_minfo(_,_).


:- was_export(ain_minfo_2/2).

%% ain_minfo_2( :PRED1How, ?G) is semidet.
%
% Assert If New Metainformation  Extended Helper.
%
:- module_transparent(ain_minfo_2/2).
ain_minfo_2(How,G):-ain_minfo(How,G).


%% mpred_is_info( :TermC) is semidet.
%
% PFC If Is A Info.
%
mpred_is_info(mpred_bc_only(C)):-is_ftNonvar(C),!.
mpred_is_info(infoF(C)):-is_ftNonvar(C),!.
mpred_is_info(inherit_above(_,_)).
mpred_is_info((Fail,_)):-Fail==fail.


%:- was_dynamic(not_not/1).

%% mpred_rewrap_h( +A, ?A) is semidet.
%
% PFC Rewrap Head.
%
mpred_rewrap_h(A,A):-is_ftNonvar(A),\+ is_static_predicate(A).
mpred_rewrap_h(A,F):- functor(A,F,_),\+ is_static_predicate(F),!.
%mpred_rewrap_h(A,not_not(A)):-!.


%% cwc is det.
%
% Cwc.
%
cwc:-true.

%% fwc is det.
%
% Fwc.
%
fwc:-true.

%% bwc is semidet.
%
% Bwc.
%
bwc:-true.

awc:-true.
zwc:-true.

%% wac is semidet.
%
% Wac.
%
wac:-true.

%% is_fc_body( +P) is semidet.
%
% If Is A Forward Chaining Body.
%
is_fc_body(P):- has_body_atom(fwc,P).

%% is_bc_body( +P) is semidet.
%
% If Is A Backchaining Body.
%
is_bc_body(P):- has_body_atom(bwc,P).

%% is_action_body( +P) is semidet.
%
% If Is A Action Body.
%
is_action_body(P):- has_body_atom(wac,P).



%% has_body_atom( +WAC, ?P) is semidet.
%
% Has Body Atom.
%
has_body_atom(WAC,P):- call(
   WAC==P -> true ; (is_ftCompound(P),get_unnegated_head_arg(1,P,E),has_body_atom(WAC,E))),!.

/*
has_body_atom(WAC,P,Rest):- call(WAC==P -> Rest = true ; (is_ftCompound(P),functor(P,F,A),is_atom_body_pfa(WAC,P,F,A,Rest))).
is_atom_body_pfa(WAC,P,F,2,Rest):-get_unnegated_head_arg(1,P,E),E==WAC,get_unnegated_head_arg(2,P,Rest),!.
is_atom_body_pfa(WAC,P,F,2,Rest):-get_unnegated_head_arg(2,P,E),E==WAC,get_unnegated_head_arg(1,P,Rest),!.
*/


same_functors(Head1,Head2):-must_det(get_unnegated_functor(Head1,F1,A1)),must_det(get_unnegated_functor(Head2,F2,A2)),!,F1=F2,A1=A2.



%% mpred_update_literal( +P, ?N, ?Q, ?R) is semidet.
%
% PFC Update Literal.
%
mpred_update_literal(P,N,Q,R):-
    get_unnegated_head_arg(N,P,UPDATE),call(replace_arg(P,N,Q_SLOT,Q)),
    must(umt(Q)),update_value(Q_SLOT,UPDATE,NEW), 
    replace_arg(Q,N,NEW,R).


% spft(5,5,5).

% ======================= 
% utils
% ======================= 

%% map_literals( +P, ?G) is semidet.
%
% Map Literals.
%
map_literals(P,G):-map_literals(P,G,[]).


%% map_literals( +VALUE1, :TermH, ?VALUE3) is semidet.
%
% Map Literals.
%
map_literals(_,H,_):-is_ftVar(H),!. % skip over it
map_literals(_,[],_) :- !.
map_literals(Pred,(H,T),S):-!, apply(Pred,[H|S]), map_literals(Pred,T,S).
map_literals(Pred,[H|T],S):-!, apply(Pred,[H|S]), map_literals(Pred,T,S).
map_literals(Pred,H,S):- mpred_literal(H),must(apply(Pred,[H|S])),!.
map_literals(_Pred,H,_S):- \+ is_ftCompound(H),!. % skip over it
map_literals(Pred,H,S):-H=..List,!,map_literals(Pred,List,S),!.



%% map_unless( :PRED1Test, ?Pred, ?H, ?S) is semidet.
%
% Map Unless.
%
map_unless(Test,Pred,H,S):- call(Test,H),ignore(apply(Pred,[H|S])),!.
map_unless(_Test,_,[],_) :- !.
map_unless(_Test,_Pred,H,_S):- \+ is_ftCompound(H),!. % skip over it
map_unless(Test,Pred,(H,T),S):-!, apply(Pred,[H|S]), map_unless(Test,Pred,T,S).
map_unless(Test,Pred,[H|T],S):-!, apply(Pred,[H|S]), map_unless(Test,Pred,T,S).
map_unless(Test,Pred,H,S):-H=..List,!,map_unless(Test,Pred,List,S),!.


:- meta_predicate(map_first_arg(:,+)).
%% map_first_arg( +Pred, ?List) is semidet.
%
% PFC Maptree.
%
map_first_arg(CM:Pred,List):-map_first_arg(CM,Pred,List,[]).

:- meta_predicate(map_first_arg(+,*,+,+)).
%% map_first_arg( +Pred, :TermH, ?S) is semidet.
%
% PFC Maptree.
%
map_first_arg(CM,Pred,H,S):-is_ftVar(H),!,CM:apply(Pred,[H|S]).
map_first_arg(_,_,[],_) :- !.
map_first_arg(CM,Pred,(H,T),S):-!, map_first_arg(CM,Pred,H,S), map_first_arg(CM,Pred,T,S).
map_first_arg(CM,Pred,(H;T),S):-!, map_first_arg(CM,Pred,H,S) ; map_first_arg(CM,Pred,T,S).
map_first_arg(CM,Pred,[H|T],S):-!, CM:apply(Pred,[H|S]), map_first_arg(CM,Pred,T,S).
map_first_arg(CM,Pred,H,S):- CM:apply(Pred,[H|S]). 

:- fixup_exports.

% % :- ensure_loaded(logicmoo(util/rec_lambda)).

%example pfcVerifyMissing(mpred_isa(I,D), mpred_isa(I,C), ((mpred_isa(I,C), {D==C});-mpred_isa(I,C))). 
%example pfcVerifyMissing(mudColor(I,D), mudColor(I,C), ((mudColor(I,C), {D==C});-mudColor(I,C))). 


%% pfcVerifyMissing( +GC, ?GO, ?GO) is semidet.
%
% Prolog Forward Chaining Verify Missing.
%
pfcVerifyMissing(GC, GO, ((GO, {D==C});\+ GO) ):-  GC=..[F,A|Args],append(Left,[D],Args),append(Left,[C],NewArgs),GO=..[F,A|NewArgs],!.

%example mpred_freeLastArg(mpred_isa(I,C),~(mpred_isa(I,C))):-is_ftNonvar(C),!.
%example mpred_freeLastArg(mpred_isa(I,C),(mpred_isa(I,F),C\=F)):-!.

%% mpred_freeLastArg( +G, ?GG) is semidet.
%
% PFC Free Last Argument.
%
mpred_freeLastArg(G,GG):- G=..[F,A|Args],append(Left,[_],Args),append(Left,[_],NewArgs),GG=..[F,A|NewArgs],!.
mpred_freeLastArg(_G,false).


:- fixup_exports.



