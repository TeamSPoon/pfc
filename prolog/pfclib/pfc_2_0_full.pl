/*
% ===================================================================
% File 'pfc_db_preds.pl'
% Purpose: Emulation of OpenCyc for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface.pl' 1.0.0
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

:-dynamic(unused_predicate/4).

:- include('pfc_header.pi').
:- flag_call(runtime_debug=false).

:- set_how_virtualize_file(bodies).

user_m_check(_Out).

:- meta_predicate make_shared_multifile(+,+,+), pfc_op_each(3).
:- meta_predicate make_shared_multifile(*,*,*,*).


:- meta_predicate transitive_path(2,*,*).

% add_abox_module(baseKB):-!.
add_abox_module(ABox):- must(atom(ABox)),
  must(mtCanAssert(ABox)),
  ABox:ain(baseKB:mtHybrid(ABox)).

/*
:- dynamic(baseKB:mtProlog/1).
*/

:- kb_global(baseKB:mtNoPrologCode/1).
baseKB:mtNoPrologCode(pfc_userkb).

:- kb_global(baseKB:mtProlog/1).
baseKB:mtProlog(Mt):- baseKB_mtProlog(Mt).

baseKB_mtProlog(Mt):- \+ atom(Mt),!,var(Mt),!,current_module(Mt),baseKB:mtProlog(Mt).
baseKB_mtProlog(Mt):- \+ current_module(Mt),!,fail.
baseKB_mtProlog(Mt):- clause_b(mtHybrid(Mt)),!,fail.
baseKB_mtProlog(Mt):- module_property(Mt,class(library)).
baseKB_mtProlog(Mt):- module_property(Mt,class(system)).
baseKB_mtProlog(Mt):- arg(_,v(lmcache,t_l,system),Mt).
% baseKB_mtProlog(user).

:- multifile(lmcache:has_pfc_database_preds/1).
:- dynamic(lmcache:has_pfc_database_preds/1).


%% assert_setting01( ?X) is semidet.
% :- srtrace.
assert_setting01(M:P):-safe_functor(P,_,A),dupe_term(P,DP),setarg(A,DP,_),system:retractall(M:DP),system:asserta(M:P).

% :- break.

%% which_file( ?F) is semidet.
%
% Which File.
%
which_file(F):- prolog_load_context(source,F) -> true; once(loading_source_file(F)).

:- module_transparent

         assert_setting01/1,
         make_module_name_local/2,
         make_module_name_local0/2,

         defaultAssertMt/1,
         set_defaultAssertMt/1,
         with_no_retry_undefined/1,
         which_file/1,
         fileAssertMt/1,
         set_fileAssertMt/1,

         correct_module/3,
         correct_module/5,
         ensure_imports/1,
         in_pfc_kb_module/0,
         which_file/1,
         user_m_check/1 .


%% in_pfc_kb_module is semidet.
%
% In Managed Predicate Knowledge Base Module.
%
in_pfc_kb_module:- source_context_module(MT),defaultAssertMt(MT2),!,MT==MT2.


map_inheritance(Child):-forall(import_module(Child,Parent),inherit_into_module(Child,Parent)).


%% box_type( ?F, ?A, ?VALUE3) is semidet.
%
% Datalog Type.
%
box_type(F,A,tbox):-current_predicate(baseKB:F/A).
box_type(_,_,abox).




:- thread_local(t_l:current_defaultAssertMt/1).
:- dynamic(baseKB:file_to_module/2).






% :- '$hide'(defaultAssertMt(_)).


%% get_file_type_local( ?File, ?Type) is det.
%
% Get File Type.
%
get_file_type_local(File,Type):-var(File),!,quietly_must(loading_source_file(File)),get_file_type_local(File,Type),!.
get_file_type_local(File,pfc):-file_name_extension(_,'.pfc.pl',File),!.
get_file_type_local(File,pfc):-file_name_extension(_,'.clif',File),!.
get_file_type_local(File,Type):-file_name_extension(_,Type,File),!.
get_file_type_local(File,Type):-clause_b(lmcache:pfc_directive_value(File,language,Type)).


mtCanAssert(Module):- clause_b(mtNonAssertable(Module)),!,fail.
mtCanAssert(ABox):- \+ \+ (ABox=abox),!,trace_or_throw_ex(mtCanAssert(ABox)),fail.
mtCanAssert(Module):- clause_b(mtHybrid(Module)).
mtCanAssert(user):-  is_user_pfc.
% mtCanAssert(Module):- clause_b(mtExact(Module)).
mtCanAssert(Module):-  module_property(Module,file(_)),!,fail.
mtCanAssert(Module):- (loading_source_file(File),get_file_type_local(File,pfc),prolog_load_context(module,Module)).
mtCanAssert(Module):- clause_b(mtProlog(Module)),!,fail.
mtCanAssert(Module):- \+ pfc_lib:is_code_module(Module),!.

is_user_pfc:- clause_b(mtHybrid(user)).



%% fileAssertMt(-ABox) is det.
%
% Gets ABox is an "assertion component" Prolog Module
% within a knowledge base.
%
% not just user modules

fileAssertMt(M):- nonvar(M), fileAssertMt(ABoxVar),!,M=@=ABoxVar.
fileAssertMt(M):- loading_source_file(File),clause_b(baseKB:file_to_module(File,M)),!.
fileAssertMt(M):- loading_source_file(File),clause_b(lmcache:pfc_directive_value(File,module,M)),!.
fileAssertMt(M):- fileAssertMt0(M), (source_location(_,_)->show_call(set_fileAssertMt(M));true).

fileAssertMt0(M):- prolog_load_context(module,M),mtCanAssert(M),!.
fileAssertMt0(M):- '$current_typein_module'(M),mtCanAssert(M),!.
fileAssertMt0(M):- 'strip_module'(module,M,module),mtCanAssert(M),!.
fileAssertMt0(M):- must(get_fallBackAssertMt(M)),!.


:- initialization(fix_baseKB_imports,now).


%% set_fileAssertMt( ABox) is semidet.
%
% Sets the File''s Module.
%

% set_fileAssertMt(M):- '$current_source_module'(M),!.
set_fileAssertMt(M):-
 ensure_abox(M),
  sanity(mtCanAssert(M)),
  must(which_file(File)),
  assert_setting(baseKB:file_to_module(File,M)),
  assert_setting(lmcache:pfc_directive_value(File,module,M)),
  asserta_until_eof(t_l:current_defaultAssertMt(M)),!,
  ((pfc_lib:is_mpred_file) -> must(set_current_modules_until_eof(M)) ; true).


%:- import(pfc_lib:is_mpred_file/0).
% :- '$hide'(set_fileAssertMt(_)).


set_current_modules_until_eof(M):- 
 '$current_typein_module'(CM),'$set_typein_module'(M),call_on_eof('$set_typein_module'(CM)),
 '$current_source_module'(SM),'$set_source_module'(M),call_on_eof('$set_source_module'(SM)).


%% set_defaultAssertMt( ?M) is semidet.
%
% Sets Current Module.
%
set_defaultAssertMt(M):-
  ignore(show_failure(mtCanAssert(M))),
   ensure_abox(M),!,
   % assert_setting(t_l:current_defaultAssertMt(M)),
   asserta_until_eof(t_l:current_defaultAssertMt(M)),
  (source_location(_,_)-> ((fileAssertMt(M) -> true; set_fileAssertMt(M)))  ;set_current_modules_until_eof(M)).

% :- '$hide'(set_defaultAssertMt(_)).



%% defaultAssertMt(-Ctx) is det.
%
% M is an "assertion component" Prolog Module
% within a knowledge base.
%
% not just user modules

defaultAssertMt(M):- nonvar(M), defaultAssertMt(ABoxVar),!,M=@=ABoxVar.
defaultAssertMt(M):- quietly(defaultAssertMt0(M)),!.

defaultAssertMt0(M):- t_l:current_defaultAssertMt(M).
defaultAssertMt0(M):- get_fallBackAssertMt(M),!.

get_fallBackAssertMt(M):- loading_source_file(File),clause_b(baseKB:file_to_module(File,M)).
get_fallBackAssertMt(M):- loading_source_file(File),clause_b(lmcache:pfc_directive_value(File,module,M)).
get_fallBackAssertMt(M):- guess_maybe_assertMt(M),clause_b(mtHybrid(M)),!.
get_fallBackAssertMt(M):- guess_maybe_assertMt(M),mtCanAssert(M),!.
get_fallBackAssertMt(M):- guess_maybe_assertMt(M).

guess_maybe_assertMt(M):- '$current_source_module'(M).
guess_maybe_assertMt(M):- context_module(M).
guess_maybe_assertMt(M):- loading_source_file(File),clause_b(baseKB:file_to_module(File,M)).
guess_maybe_assertMt(M):- loading_source_file(File),clause_b(lmcache:pfc_directive_value(File,module,M)).
guess_maybe_assertMt(M):-  which_file(File)->current_module(M),module_property(M,file(File)),File\==M.
guess_maybe_assertMt(M):- '$current_typein_module'(M).
guess_maybe_assertMt(M):- nb_current(defaultQueryMt,M),!.
guess_maybe_assertMt(M):- which_file(File)->make_module_name_local(File,M),current_module(M),File\==M.   
guess_maybe_assertMt(M):- (loading_source_file(File),get_file_type_local(File,pfc)),prolog_load_context(module,M).





defaultQueryMt(M):- nonvar(M), defaultQueryMt(ABoxVar),!,M=@=ABoxVar.
defaultQueryMt(M):- nb_current(defaultQueryMt,M)->true;(defaultQueryMt0(M)->nb_setval(defaultQueryMt,M)),!.


defaultQueryMt0(M):- 'strip_module'(module,M,module),clause_b(mtHybrid(M)),!.
defaultQueryMt0(M):- prolog_load_context(module,M),clause_b(mtHybrid(M)),!.
defaultQueryMt0(M):- '$current_typein_module'(M),clause_b(mtHybrid(M)),!.
defaultQueryMt0(M):- guess_maybe_assertMt(M),clause_b(mtHybrid(M)),!.
defaultQueryMt0(M):- guess_maybe_assertMt(M),mtCanAssert(M),!.
defaultQueryMt0(M):- guess_maybe_assertMt(M).







% baseKB:mtGlobal
% mtCore



makeConstant(_Mt).

is_pfc_module_file(M):- is_pfc_module_file(M,F,TF),!, (F \== (-)), TF = true.

is_pfc_module_file(M,F,TF):- (module_property(M,file(F)),pfc_lib:is_mpred_file(F)) *-> TF=true ; 
  (module_property(M,file(F))*->TF=false ; (F= (-), TF=false)).

maybe_ensure_abox(M):- is_pfc_module_file(M,F,_), (F \== (-)), !,   
  (pfc_lib:is_mpred_file(F)->show_call(pfc_lib:is_mpred_file(F),ensure_abox(M));dmsg_pretty(not_is_pfc_module_file(M,F))).
maybe_ensure_abox(M):- show_call(not_is_mpred_file,ensure_abox(M)).


:- module_transparent((ensure_abox)/1).
ensure_abox(M):- 
  ignore(((M==user;M==baseKB)->true;nop(add_import_module(M,pfc_lib,end)))),
  dynamic(M:defaultTBoxMt/1),
  must(ensure_abox_support(M,baseKB)),!.
:- module_transparent((ensure_abox_support)/2).
ensure_abox_support(M,TBox):- clause_b(M:defaultTBoxMt(TBox)),!.
ensure_abox_support(M,TBox):- 
	% asserta(M:defaultTBoxMt(TBox)),
   set_prolog_flag(M:unknown,error),  
  must(forall(pfc_database_term(F,A,_Type),
           kb_shared(M:F/A))),
  must(M:ain(TBox:mtHybrid(M))),   
  must(system:add_import_module(M,system,end)),
  (M\==user->must(ignore(system:delete_import_module(M,user)));true),!,
  must(setup_module_ops(M)),!.
  
ensure_abox_support(M,TBox):- 
       % system:add_import_module(M,user,end),
       must(ignore(system:delete_import_module(M,system))),
       must(ignore(system:delete_import_module(M,baseKB))),
       system:add_import_module(M,system,end),
       retractall(M:defaultTBoxMt(TBox)),
       throw(failed_ensure_abox_support(M,TBox)).


   

setup_module_ops(M):- pfc_op_each(pfc_op_unless(M)).

pfc_op_unless(M,A,B,C):- op_safe(A,B,M:C).

pfc_op_each(OpEach):-
            call(OpEach,1199,fx,('==>')), % assert
            call(OpEach,1199,fx,('?->')), % ask
            call(OpEach,1190,xfy,('::::')), % Name something
            call(OpEach,1180,xfx,('==>')), % Forward chaining
            call(OpEach,1170,xfx,('<==>')), % Forward and backward chaining
            call(OpEach,1160,xfx,('<==')), % backward chain PFC sytle
            call(OpEach,1160,xfx,('<-')), % backward chain PTTP sytle (currely really PFC)
            call(OpEach,1160,xfx,('<=')), % backward chain DRA sytle
            call(OpEach,1150,xfx,('=>')), % Logical implication
            call(OpEach,1130,xfx,('<=>')), % Logical bi-implication
            call(OpEach,600,yfx,('&')), 
            call(OpEach,600,yfx,('v')),
            call(OpEach,400,fx,('~')),
            % call(OpEach,300,fx,('-')),
            call(OpEach,350,xfx,('xor')),
            % replicate user:op/3s in case we remove inheritance
            forall(current_op(X,Y,user:Z),
              call(OpEach,X,Y,Z)).







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





make_module_name_local(A,B):- make_module_name_local0(A,B), \+ exists_file(B),!.

make_module_name_local0(Source,KB):- clause_b(mtProlog(Source)),t_l:current_defaultAssertMt(KB),!.
make_module_name_local0(Source,KB):- clause_b(mtGlobal(Source)),t_l:current_defaultAssertMt(KB),!.
make_module_name_local0(Source,SetName):- clause_b(baseKB:file_to_module(Source,SetName)),!.
make_module_name_local0(Source,Source):- lmcache:has_pfc_database_preds(Source).
make_module_name_local0(Source,Source):- clause_b(mtHybrid(Source)),!.
make_module_name_local0(user,KB):- t_l:current_defaultAssertMt(KB),!.
make_module_name_local0(user,baseKB):-!.
make_module_name_local0(Source,GetName):- make_module_name00(Source,GetName).


ensure_tbox(_ABox).


%% mtCore( ?VALUE1) is semidet.
%
% If Is A Datalog System Core Microtheory.
%
:- dynamic(baseKB:mtCore/1).
baseKB:mtCore(baseKB).




%% baseKB:mtGlobal(M,Box).
%
% Boot Modules.
%
%baseKB:mtGlobal(pfc_loader).

:- dynamic(baseKB:mtGlobal/1).
baseKB:mtGlobal(boot_system).
baseKB:mtGlobal(system_markers).
baseKB:mtGlobal(system_singleValued).
baseKB:mtGlobal(system_genls).
baseKB:mtGlobal(system_if_missing).
baseKB:mtGlobal(common_logic_clif).
baseKB:mtGlobal(system_mdefault).

:- dynamic(baseKB:mtCycLBroad/1).

baseKB:mtCycLBroad(baseKB).

is_undefaulted(user).

/*
:- dynamic(call_a/0).
call_a:- arity(tCol,1),arity(arity,2).
:- must(((clause(call_a,
        (ereq(arity(tCol,1)),ereq(arity(arity,2))),Ref),erase(Ref)))).
*/

%% ensure_imports( ?M) is semidet.
%
% Ensure Imports.
%
ensure_imports(baseKB):-!.
ensure_imports(M):- ain(genlMt(M,baseKB)).
% ensure_imports(M):- ain(M:genlMt(M,baseKB)).

:-multifile(lmcache:is_ensured_imports_tbox/2).
:-dynamic(lmcache:is_ensured_imports_tbox/2).


%% skip_user( ?M) is semidet.
%
% Skip over 'user' module and still see 'system'.
%
skip_user(Mt):- Mt==user,!.
skip_user(Mt):- import_module(Mt,system), \+ default_module(Mt,user), !.
skip_user(Mt):- add_import_module(Mt,system,start),ignore(delete_import_module(Mt,user)),
  forall((import_module(Mt,X),default_module(X,user)),skip_user(X)).

inherit_into_module(Child,Parent):- ==(Child,Parent),!.
%TODO inherit_into_module(Child,Parent):- ain(Child:genlMt(Child,Parent)).
inherit_into_module(Child,Parent):- ain(baseKB:genlMt(Child,Parent)).

%% ensure_imports_tbox( ?M, ?TBox) is semidet.
%
% Ensure Imports Tbox.
%
ensure_imports_tbox(M,TBox):- trace_or_throw_ex(unexpected_ensure_imports_tbox(M,TBox)), M==TBox,!.
ensure_imports_tbox(M,TBox):-
  lmcache:is_ensured_imports_tbox(M,TBox),!.
ensure_imports_tbox(M,TBox):-
  asserta(lmcache:is_ensured_imports_tbox(M,TBox)),

  must((
   skip_user(TBox),
   ignore(maybe_delete_import_module(M,TBox)),
   ignore(maybe_delete_import_module(TBox,M)),
   forall((user:current_predicate(_,TBox:P),
      \+ predicate_property(TBox:P,imported_from(_))),
      add_import_predicate(M,P,TBox)),
   inherit_into_module(M,user),
   skip_user(M),
   ignore(maybe_delete_import_module(M,user)),
   inherit_into_module(user,M),
   ignore(maybe_delete_import_module(user,system)), % gets from M now
   !)).



% :- inherit_into_module(logicmoo_user,system).

fixup_module(_,_):-!.
fixup_module(system,_).
fixup_module(M,_L):- clause_b(tGlobal(M)),skip_user(M).
fixup_module(system,_L):-skip_user(system).
fixup_module(_,[user]).
fixup_module(M,_L):- skip_user(M).


fixup_modules:-  trace_or_throw_ex(unexpected(fixup_modules)),
   doall((current_module(M),once((findall(I,import_module(M,I),L))),once(fixup_module(M,L)))).

% :- autoload([verbose(false)]).
:- flag_call(runtime_debug=true).

% :- fixup_modules.







% ============================================

%% correct_module( ?M, ?X, ?T) is semidet.
%
% Correct Module.
%
correct_module(M,G,T):-safe_functor(G,F,A),quietly_must(correct_module(M,G,F,A,T)),!.

%% correct_module( ?M, ?Goal, ?F, ?A, ?T) is semidet.
%
% Correct Module.
%
correct_module(abox,G,F,A,T):- !, defaultAssertMt(M),correct_module(M,G,F,A,T).
correct_module(tbox,G,F,A,T):- !, get_current_default_tbox(M),correct_module(M,G,F,A,T).
correct_module(user,G,F,A,T):- fail,!,defaultAssertMt(M),correct_module(M,G,F,A,T).

correct_module(HintMt,Goal,F,A,OtherMt):-var(Goal),safe_functor(Goal,F,A),!,correct_module(HintMt,Goal,F,A,OtherMt).
correct_module(HintMt,Goal,_,_,OtherMt):- predicate_property(HintMt:Goal,imported_from(OtherMt)).
correct_module(_,Goal,_,_,OtherMt):- predicate_property(Goal,imported_from(OtherMt)).
correct_module(HintMt,_,_,_,HintMt):- call_u(mtExact(HintMt)).
correct_module(HintMt,Goal,_,_,HintMt):- predicate_property(HintMt:Goal,exported).
correct_module(_,Goal,_,_,OtherMt):- var(OtherMt),!, predicate_property(OtherMt:Goal,file(_)).
correct_module(_,Goal,_,_,OtherMt):- clause_b(mtGlobal(OtherMt)), predicate_property(OtherMt:Goal,file(_)).
correct_module(MT,_,_,_,MT):-!.



:- dynamic(lmcache:how_registered_pred/4).
:- module_transparent(lmcache:how_registered_pred/4).

add_import_predicate(Mt,Goal,OtherMt):- fail,
   clause_b(mtGlobal(Mt)),
   clause_b(mtGlobal(OtherMt)),
   \+ import_module(OtherMt,Mt),
   catch(add_import_module(Mt,OtherMt,end),
       error(permission_error(add_import,module,baseKB),
       context(system:add_import_module/3,'would create a cycle')),fail),
   must(predicate_property(Mt:Goal,imported_from(OtherMt))),!.


add_import_predicate(Mt,Goal,OtherMt):- trace_or_throw_ex(add_import_predicate(Mt,Goal,OtherMt)),
   catch(Mt:import(OtherMt:Goal),_,fail),!.
add_import_predicate(Mt,Goal,OtherMt):-
   safe_functor(Goal,F,A),
   make_as_dynamic(imported_from(OtherMt),Mt,F,A),
   assert_if_new(( Mt:Goal :- OtherMt:Goal)).


transitive_path(F,[Arg1,Arg2],Arg2):-
  dif(Arg1,Arg2),call(F,Arg1,Arg2),!.
transitive_path(F,[Arg1,SecondNodeMt|REST],Arg2):-
  dif(Arg1,Arg2),dif(Arg1,SecondNodeMt),
  call(F,Arg1,SecondNodeMt),sanity(stack_check),
  transitive_path(F,[SecondNodeMt|REST],Arg2).



autoload_library_index(F,A,PredMt,File):- safe_functor(P,F,A),'$autoload':library_index(P,PredMt,File).


:- multifile(baseKB:hybrid_support/2).
:- dynamic(baseKB:hybrid_support/2).
baseKB_hybrid_support(F,A):-suggest_m(M),clause_b(baseKB:safe_wrap(M,F,A,_)).
baseKB_hybrid_support(F,A):-clause_b(hybrid_support(F,A)).

baseKB:hybrid_support(predicateConventionMt,2).

baseKB:hybrid_support(functorDeclares,1).
baseKB:hybrid_support(arity,2).

%baseKB:hybrid_support(spft,3).

baseKB:hybrid_support(mtHybrid,1).
baseKB:hybrid_support(mtCycLBroad,1).
baseKB:hybrid_support(genlMt,2).


:- if(\+ exists_source(library(retry_undefined))).


:- endif.


%=

%% kb_global( +PI) is semidet.
%
% Shared Multifile.
%
make_shared_multifile(PredMt:MPI):-
   context_module_of_file(CallerMt),!,
   with_pfa_group(make_shared_multifile,CallerMt,PredMt, MPI),!.


%% make_shared_multifile( ?CallerMt, ?PredMt, :TermPI) is semidet.
%
% Make Shared Multifile.
%
make_shared_multifile(CallerMt, PredMt,FA):- get_fa(FA,F,A), make_shared_multifile(CallerMt, PredMt,F,A),!.

make_shared_multifile(CallerMt,    t_l,F,A):-!,CallerMt:thread_local(t_l:F/A),CallerMt:multifile(t_l:F/A).
% make_shared_multifile(CallerMt,baseKB ,F,A):-!,CallerMt:multifile(baseKB:F/A),CallerMt:dynamic(baseKB:F/A),!.
make_shared_multifile(CallerMt,lmcache,F,A):-!,CallerMt:multifile(lmcache:F/A),CallerMt:volatile(lmcache:F/A),CallerMt:dynamic(lmcache:F/A),!.

make_shared_multifile(CallerMt,PredMt,F,A):-
  safe_functor(Goal,F,A),
  correct_module(PredMt,Goal,F,A,HomeM),
  HomeM\==PredMt,!,
  make_shared_multifile(CallerMt,HomeM,F,A).

make_shared_multifile(CallerMt,Home,F,A):- clause_b(mtProlog(Home)),!,
     wdmsg_pretty(mtSharedPrologCodeOnly_make_shared_multifile(CallerMt,Home:F/A)),!.

make_shared_multifile(_CallerMt, baseKB,F,A):-  kb_global(baseKB:F/A),!.

make_shared_multifile(_CallerMt,PredMt,F,A):-!,
 dmsg_pretty(make_shared_multifile(PredMt:F/A)),
 locally(set_prolog_flag(access_level,system),
  PredMt:(
   sanity( \+ ((PredMt:F/A) = (qrTBox:p/1))),
   PredMt:check_never_assert(declared(PredMt:F/A)),
   decl_mpred(PredMt:F/A))).




%% make_reachable( ?UPARAM1, ?Test) is semidet.
%
% Make Reachable.
%
make_reachable(_,Test):- \+ \+ ((Test= (_:F/_), is_ftVar(F))),!.
make_reachable(CM,M:F/A):-  atom(CM),ignore(CM=M),quietly_must(atom(CM)),quietly_must(atom(M)),
   safe_functor(G,F,A),
   correct_module(M,G,F,A,TT), !,import_predicate(CM,TT:F/A).



%% import_predicate( ?CM, :TermM) is semidet.
%
% Import Predicate.
%
import_predicate(CM,M:_):- CM==M,!.
import_predicate(CM,M:_):- default_module(CM,M),!.
import_predicate(CM,M:F/A):- show_call(nop(CM:z333import(M:F/A))),CM:multifile(M:F/A),
  on_xf_cont(CM:discontiguous(M:F/A)).



/*
system:call_expansion(T,(pfc_at_box:defaultAssertMt(NewVar),NewT)):- current_predicate(_,get_lang(pfc)), compound(T),
   subst(T,abox,NewVar,NewT),NewT\=@=T.

system:body_expansion(T,(pfc_at_box:defaultAssertMt(NewVar),NewT)):- current_predicate(_,get_lang(pfc)), compound(T),
   subst(T,abox,NewVar,NewT),NewT\=@=T.
*/


:- fixup_exports.
:- meta_predicate pfc_retract_i_or_warn(*).
:- meta_predicate pfc_retract_i_or_warn_1(*).
:- meta_predicate not_not_ignore_quietly_ex(*).
:- meta_predicate must_notrace_pfc(*).
:- multifile(baseKB:safe_wrap/4).
:- dynamic(baseKB:safe_wrap/4).


:- op(700,xfx,('univ_safe')).


:- system:use_module(library(lists)).

:- module_transparent lookup_u/1,lookup_u/2,pfc_unfwc_check_triggers0/1,pfc_unfwc1/1,pfcWhy1/1,pfc_blast/1.

must_ex(G):- (G*->true;(wdmsg_pretty(must_ex(G)),if_interactive((ignore(rtrace(G)),wdmsg_pretty(must_ex(G)), break)))).

must_notrace_pfc(G):- must_ex((G)).

:- thread_local(t_l:assert_to/1).

/*

  ?- dynamic(f2/2),gensym(nnn,N),sanity_attvar_08:attr_bind([name_variable(A, 'ExIn'), form_sk(A, 'SKF-66')], true),
   IN=f2(N,A),OUT=f2(N,B),copy_term_vn(IN,OUT),
  asserta_u(IN),clause_asserted_u(OUT),!. % ,nl,writeq(A=@=B).
*/
:- meta_predicate with_each_item(:,+,+).
%% with_each_item(:P2,+EleList,+ArgList) is nondet.
%
% Call apply(P,[Ele|ArgList]) on each Ele(ment) in the EleList.
%
% EleList is a  List, a Conjuction Terms or a single element.
%
with_each_item(P,HV,S):- var(HV),!, apply(P,[HV|S]).
with_each_item(P,M:HT,S) :- !, must_be(atom,M), M:with_each_item(P,HT,S).
with_each_item(P,[H|T],S) :- !, apply(P,[H|S]), with_each_item(P,T,S).
with_each_item(P,(H,T),S) :- !, with_each_item(P,H,S), with_each_item(P,T,S).
with_each_item(P,H,S) :- apply(P,[H|S]).




%% pfc_database_term(:PI, -TYPE) is nondet.
%
% is true iff F/A is something that Pfc adds to
% the database and should not be present in an empty Pfc database
%

:- nodebug(logicmoo(pfc)).

% mined from program database

:- dynamic(baseKB:pt/2).                   
:- system:import(baseKB:pt/2).

:- dynamic(baseKB:pm/1).                   
:- system:import(baseKB:pm/1).

:- dynamic(baseKB:nt/3).                   
:- system:import(baseKB:nt/3).

:- dynamic(baseKB:spft/3).                   
:- system:import(baseKB:spft/3).

:- dynamic(baseKB:bt/2).                   
:- system:import(baseKB:bt/2).

:- dynamic(baseKB:do_and_undo/2).
:- system:import(baseKB:do_and_undo/2).

:- dynamic(baseKB:tms/1).                   
:- system:import(baseKB:tms/1).



/*
*/
:- dynamic(baseKB:pfc_is_tracing_exec/0).
:- export(baseKB:pfc_is_tracing_exec/0).

pfc_database_term_syntax(do_and_undo,2,rule(_)).

pfc_database_term_syntax(('::::'),2,rule(_)).
pfc_database_term_syntax((<-),2,rule(_)).
pfc_database_term_syntax((<==>),2,rule(_)).
pfc_database_term_syntax((==>),2,rule(_)).

pfc_database_term_syntax(mdefault,1,fact(_)).
pfc_database_term_syntax((==>),1,fact(_)).
pfc_database_term_syntax((~),1,fact(_)).


baseKB:pfc_database_term(F,A,syntaxic(T)):- pfc_lib:pfc_database_term_syntax(F,A,T).
baseKB:pfc_database_term(F,A,T):- pfc_lib:pfc_core_database_term(F,A,T).

pfc_core_database_term(genlPreds,2,fact(_)).
% pfc_core_database_term(rtArgsVerbatum,1,fact(_)).

% forward,backward chaining database
pfc_core_database_term(spft,3,support).

pfc_core_database_term(nt,3,trigger(pt)).
pfc_core_database_term(pt,2,trigger(nt)).
pfc_core_database_term(bt,2,trigger(bt)).

% transient state
pfc_core_database_term(pfcAction,1,state).
pfc_core_database_term(que,2,state).
pfc_core_database_term(hs,1,state).

% forward,backward settings
pfc_core_database_term(pfc_current_db,1,setting).
pfc_core_database_term(pfcSelect,1,setting).
pfc_core_database_term(tms,1,setting).
pfc_core_database_term(pm,1,setting).

% debug settings
pfc_core_database_term(pfc_is_tracing_exec,0,debug).
%pfc_core_database_term(lmcache:pfc_is_spying_pred,2,debug).
pfc_core_database_term(pfcWarnings,1,debug).
% pfc_core_database_term(t_l:whybuffer,2,debug).

pfc_core_database_term(pfc_prop,4,fact(_)).

pfc_core_database_term(predicateConventionMt,2,fact(_)).
% pfc_core_database_term(genlMt,2,fact(_)).
%pfc_core_database_term(arity,2,fact(_)).
%pfc_core_database_term(rtArgsVerbatum,1,fact(_)).

                         
import_everywhere:- 
  forall(baseKB:pfc_database_term(F,A,_),
    (dynamic(baseKB:F/A),baseKB:export(baseKB:F/A),
     system:import(baseKB:F/A))).
:- import_everywhere.

:- thread_local(t_l:whybuffer/2).
% :- dynamic(baseKB:que/2).

:- meta_predicate show_pfc_success(*,*).
show_pfc_success(Type,G):- G*->pfc_trace_msg(success(Type,G)) ; fail.

% :- ensure_loaded(library(logicmoo_utils)).

:- module_transparent((assert_u_confirmed_was_missing/1,pfc_trace_exec/0, % pfcl_do/1,
  call_u_mp_fa/4,call_u_mp_lc/4,
  pfc_post1/2,get_pfc_assertion_status/3,pfc_post_update4/4,get_pfc_support_status/5,same_file_facts/2,
 
                       asserta_u/1,assert_u/1,assertz_u/1,retract_u/1,retractall_u/1,

                       retract_u0/1,retractall_u0/1,
  pfc_trace_op/3)).

:- thread_local(t_l:no_breaks/0).

decl_rt(RT) :- 
 '@'(((
   sanity(atom(RT)),
   univ_safe(Head , [RT,FP]),
   AIN = ((Head :- cwc, /* dmsg_pretty(warn(call(Head))), */ pfc_prop(M,FP,_,RT))),
   (clause_asserted(AIN) -> 
    (nop(listing(RT)),
     sanity((predicate_property(RHead,number_of_clauses(CL)),predicate_property(RHead,number_of_rules(RL)),CL=RL)));
     
  ((
   (current_predicate(RT/1)->
   ( nop(listing(RT)),
     RHead univ_safe [RT,F/A],
     forall(retract(RHead),ain(pfc_prop(M,F,A,RT))),
     forall(retract(Head),(get_arity(FP,F,A),sanity(atom(F)),sanity(integer(A)),ain(pfc_prop(M,F,A,RT)))),
     sanity((predicate_property(RHead,number_of_clauses(CL)),CL==0)),
     sanity((predicate_property(RHead,number_of_rules(RL)),RL==0)),
     abolish(RT,1));true),

   asserta(AIN),
  % compile_predicates([Head]),
   nop(decl_rt(RT))))))),baseKB).

quietly_ex(G):- !,G,!.
quietly_ex(G):- quietly(G).

trace_or_throw_ex(G):- trace_or_throw(G).

% =================================================
% ==============  UTILS BEGIN        ==============
% =================================================
% copy_term_vn(A,A):- current_prolog_flag(unsafe_speedups , true) ,!.
copy_term_vn(B,A):- ground(B),!,A=B.
copy_term_vn(B,A):- !,copy_term(B,A).
copy_term_vn(B,A):- need_speed,!,copy_term(B,A).
copy_term_vn(B,A):- get_varname_list(Vs),length(Vs,L),L<30, shared_vars(B,Vs,Shared),Shared\==[],!,copy_term(B+Vs,A+Vs2),append(Vs,Vs2,Vs3),set_varname_list(Vs3),!.
copy_term_vn(B,A):- nb_current('$old_variable_names',Vs),length(Vs,L),L<30, shared_vars(B,Vs,Shared),Shared\==[],!,copy_term(B+Vs,A+Vs2),append(Vs,Vs2,Vs3),b_setval('$old_variable_names',Vs3),!.
copy_term_vn(B,A):- copy_term(B,A).


setup_pfc_ops:-
          op(500,fx,'-'),
          op(300,fx,'~'),
          op(1050,xfx,('==>')),
          op(1050,xfx,'<==>'),
          op(1050,xfx,('<-')),
          op(1100,fx,('==>')),
          op(1150,xfx,('::::')),
          op(500,fx,user:'-'),
          op(300,fx,user:'~'),
          op(1050,xfx,(user:'==>')),
          op(1050,xfx,user:'<==>'),
          op(1050,xfx,(user:'<-')),
          op(1100,fx,(user:'==>')),
          op(1150,xfx,(user:'::::')).
:- setup_pfc_ops.


% :- pfc_ain_in_thread.
% :- current_thread_pool(ain_pool)->true;thread_pool_create(ain_pool,20,[]).
:- multifile thread_pool:create_pool/1.
:- dynamic thread_pool:create_pool/1.
thread_pool:create_pool(ain_pool) :-
    thread_pool_create(ain_pool, 50, [detached(true)] ).

:- use_module(library(http/thread_httpd)).
:- use_module(library(thread_pool)).

is_ain_pool_empty:- thread_pool_property(ain_pool,running(N)),!,N==0.
is_ain_pool_empty.

show_ain_pool:- forall(thread_pool_property(ain_pool,PP),fmt(show_ain_pool(PP))).

await_ain_pool:- is_ain_pool_empty->true;(repeat, sleep(0.005), is_ain_pool_empty).

ain_in_thread(MAIN):- strip_module(MAIN,M,AIN), call_in_thread(M:ain(AIN)).

call_in_thread(MG):- strip_module(MG,M,G), copy_term(M:G,GG,_),numbervars(GG,0,_),term_to_atom(GG,TN), call_in_thread(TN,M,G).

call_in_thread(TN,M,G):- thread_property(_,alias(TN)),!,dmsg_pretty(already_queued(M,G)).
call_in_thread(TN,M,G):- current_why(Why), thread_create_in_pool(ain_pool,call_in_thread_code(M,G,Why,TN),_Id,[alias(TN)]).

call_in_thread_code(M,G,Why,TN):- 
 with_only_current_why(Why,
   catch(( M:G-> nop(dmsg_pretty(suceeded(exit,TN)));dmsg_pretty(failed(exit,TN))),E,dmsg_pretty(error(E-->TN)))).
       
% why_dmsg(Why,Msg):- with_current_why(Why,dmsg_pretty(Msg)).

u_to_uu(U,(U,ax)):- var(U),!.
u_to_uu(U,U):- nonvar(U),U=(_,_),!.
u_to_uu([U|More],UU):-list_to_conj([U|More],C),!,u_to_uu(C,UU).
u_to_uu(U,(U,ax)):-!.

%% get_source_uu( :TermU) is det.
%
% Get Source Ref (Current file or User)
%
:- module_transparent((get_source_uu)/1).
get_source_uu(UU):- must(((get_source_ref1(U),u_to_uu(U,UU)))),!.

get_source_ref1(U):- quietly_ex(((current_why(U),nonvar(U)));ground(U)),!.
get_source_ref1(U):- quietly_ex(((get_source_mfl(U)))),!.


:- module_transparent((get_why_uu)/1).
get_why_uu(UU):- findall(U,current_why(U),Whys),Whys\==[],!,u_to_uu(Whys,UU).
get_why_uu(UU):- get_source_uu(UU),!.


get_startup_uu(UU):-u_to_uu((isRuntime,mfl4(VarNameZ,baseKB, user_input, _)),UU),varnames_load_context(VarNameZ).

is_user_reason((_,U)):-atomic(U).
only_is_user_reason((U1,U2)):- freeze(U2,is_user_reason((U1,U2))).

is_user_fact(P):-get_first_user_reason(P,UU),is_user_reason(UU).


get_first_real_user_reason(P,UU):- nonvar(P), UU=(F,T),
  quietly_ex((  ((((lookup_spft(P,F,T))),is_user_reason(UU))*-> true;
    ((((lookup_spft(P,F,T))), \+ is_user_reason(UU))*-> (!,fail) ; fail)))).

get_first_user_reason(P,(F,T)):-
  UU=(F,T),
  ((((lookup_spft(P,F,T))),is_user_reason(UU))*-> true;
    ((((lookup_spft(P,F,T))), \+ is_user_reason(UU))*-> (!,fail) ;
       (clause_asserted_u(P),get_source_uu(UU),is_user_reason(UU)))),!.
get_first_user_reason(_,UU):- get_why_uu(UU),is_user_reason(UU),!.
get_first_user_reason(_,UU):- get_why_uu(UU),!.
get_first_user_reason(P,UU):- must_ex(ignore(((get_first_user_reason0(P,UU))))),!.
get_first_user_reason0(_,(M,ax)):-get_source_mfl(M).

%get_first_user_reason(_,UU):- get_source_uu(UU),\+is_user_reason(UU). % ignore(get_source_uu(UU)).

%:- export(pfc_at_box:defaultAssertMt/1).
%:- system:import(defaultAssertMt/1).
%:- pfc_lib:import(pfc_at_box:defaultAssertMt/1).

:- module_transparent((get_source_mfl)/1).
get_source_mfl(M):- current_why(M), nonvar(M) , M =mfl4(_VarNameZ,_,_,_).
get_source_mfl(mfl4(VarNameZ,M,F,L)):- defaultAssertMt(M), current_source_location(F,L),varnames_load_context(VarNameZ).

get_source_mfl(mfl4(VarNameZ,M,F,L)):- defaultAssertMt(M), current_source_file(F:L),varnames_load_context(VarNameZ).
get_source_mfl(mfl4(VarNameZ,M,F,_L)):- defaultAssertMt(M), current_source_file(F),varnames_load_context(VarNameZ).
get_source_mfl(mfl4(VarNameZ,M,_F,_L)):- defaultAssertMt(M), varnames_load_context(VarNameZ).
%get_source_mfl(M):- (defaultAssertMt(M)->true;(atom(M)->(module_property(M,class(_)),!);(var(M),module_property(M,class(_))))).
get_source_mfl(M):- fail,dtrace,
 ((defaultAssertMt(M) -> !;
 (atom(M)->(module_property(M,class(_)),!);
    pfcError(no_source_ref(M))))).

is_source_ref1(_).

unassertable(Var):-var(Var),!.
unassertable((M:V)):-nonvar(M),!,unassertable(V).
unassertable((_;_)).
unassertable((_,_)).

:- style_check(+discontiguous).

to_real_mt(_Why,abox,ABOX):- defaultAssertMt(ABOX),!.
to_real_mt(_Why,tbox,TBOX):- get_current_default_tbox(TBOX),!.
to_real_mt(_Why,BOX,BOX).

%% fix_mp(+Why,+I,-O) is det.
%
% Ensure modules are correct when asserting/calling information into the correct MTs
%
%fix_mp(Why,I,UO):- compound(UO),dtrace,UO=(U:O),!,quietly_must(fix_mp(Why,I,U,O)).
% fix_mp(Why,I,MT:UO):- current_prolog_flag(unsafe_speedups , true) , !, strip_module(I,_,UO),defaultAssertMt(MT).
fix_mp(Why,I,UO):- quietly_must(fix_mp(Why,I,U,O)),maybe_prepend_mt(U,O,UO).


fix_mp(Why,G,M,GOO):-
  must_ex((quietly_ex((fix_mp0(Why,G,M,GO),strip_module(GO,_,GOO))))).

meta_split(PQ,P,OP,Q):-PQ  univ_safe [OP,P,Q],arg(_,v('<-','==>','<==>','==>',(','),(';')),OP).

fix_mp0(Nonvar,Var,ABox,VarO):- sanity(nonvar(Nonvar)), is_ftVar(Var),!,Var=VarO,defaultAssertMt(ABox),!.
fix_mp0(Why, '~'(G), M, '~'(GO)):-nonvar(G),!,fix_mp0(Why,G,M,GO).
fix_mp0(Why,'?-'(G),M, '?-'(GO)):-nonvar(G),!,fix_mp0(Why,G,M,GO).
fix_mp0(Why,':-'(G),M, ':-'(GO)):-nonvar(G),!,fix_mp0(Why,G,M,GO).
fix_mp0(Why,(:- G),M,(:- GO)):- !, fix_mp0(Why,G,M,GO).
fix_mp0(Why,(G :- B),M,( GO :- B)):- !, fix_mp0(Why,G,M,GO).
% fix_mp0(Why,(G <- B),M,( GO <- B)):- !, fix_mp0(Why,G,M,GO).
fix_mp0(Why,CM:(G :- B),M,( GO :- B)):- !, CM:fix_mp0(Why,G,M,GO).

fix_mp0(_Why,spft(P,(mfl4(VarNameZ,FromMt,File,Lineno),UserWhy)),FromMt,spft(P,(mfl4(VarNameZ,FromMt,File,Lineno),UserWhy))):-!.

fix_mp0(Why,M:P,MT,P):- to_real_mt(Why,M,MT)->M\==MT,!,fix_mp0(Why,MT:P,MT,P).

% fix_mp0(Why,PQ,M,PPQQ):- meta_split(PQ,P,OP,Q),!,fix_mp(Why,P,M1,PP),fix_mp(Why,Q,M2,QQ),(M1\==M2 -> (QQ\==Q->M=M2;M=M1) ; M=M1),!,meta_split(PPQQ,PP,OP,QQ).

fix_mp0(_Why,Mt:P,Mt,P):- clause_b(mtExact(Mt)),!.


fix_mp0(Why,G,M,GO):- /*Why = change(_,_),*/ strip_module(G,WAZ,GO),
  %  ((G==GO; (context_module(CM),CM==WAZ) ; (defaultAssertMt(ABox),ABox==WAZ) ; \+ clause_b(mtHybrid(WAZ)) ; (header_sane==WAZ); (abox==WAZ))),
   must_ex(get_unnegated_functor(GO,F,A)) 
     -> % loop_check
     (WAZ:convention_to_mt(WAZ,Why,F,A,M)),!.


fix_mp0(_Why,Mt:P,Mt,P):- clause_b(mtHybrid(Mt)),!.

fix_mp0(_Why,I,ABox,I):- defaultAssertMt(ABox),!.

/*
fix_mp(Why,Junct,ABox,Result):- fail, (pfc_db_type(Junct,rule(_));(safe_functor(Junct,F,_),bad_head_pred(F))),!,
   must_ex((pfc_rule_hb(Junct,HC,BC),nonvar(HC))),
   Junct univ_safe [F|List],
   must_maplist(fix_mp(call(hb(HC,BC,Op))),List,ListO),
   Result univ_safe [F|ListO],
   defaultAssertMt(ABox),!.

%fix_mp(call(hb(HC,_BC,Op)),H,M,HH):- contains_var(H,HC),!,
%   fix_mp(change(assert,Op),H,M,HH).

fix_mp(call(hb(_HC,BC,Op)),B,M,BB):- contains_var(B,BC),B\=@=BC,!,
   fix_mp(call(Op),B,M,BB).



% fix_mp(Why,Unassertable,_,_):- Why = clause(_,_), unassertable(Unassertable),!,trace_or_throw_ex(unassertable_fix_mp(Why,Unassertable)).

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
   dumpST,dmsg_pretty(bad_head_pred(F)),break,trace_or_throw_ex(error_convention_to_symbolic_mt(From,Why,F,A,Error)))).


% convention_to_symbolic_mt(_From,_Why,_,_,M):- atom(M),!.

full_transform_warn_if_changed(_,MH,MHH):-!,MH=MHH.
full_transform_warn_if_changed(Why,MH,MHH):- full_transform(Why,MH,MHH),!,sanity(MH=@=MHH).
full_transform_warn_if_same(Why,MH,MHH):- full_transform(Why,MH,MHH),!,sanity(MH \=@= MHH).

/*
full_transform_and_orignal(Why,MH,MHO):- full_transform(Why,MH,MHH),
      (MH=@=MHH -> MHO=MH ; (MHO = MHH ; MHO = MH )).



full_transform(Op,ISA,SentO):- nonvar(ISA),isa(I,C)=ISA,!, must_ex(fully_expand_real(Op,isa(I,C),SentO)),!.
full_transform(Op,Sent,SentO):- safe_functor(Sent,F,A),may_fully_expand(F,A),!,
   must_ex(fully_expand_real(Op,Sent,SentO)),!.

*/
%:- use_module(pfc_expansion).

/*
full_transform(Why,MH,MHH):- has_skolem_attrvars(MH),!,
 rtrace(fully_expand_real(change(assert,skolems(Why)),MH,MHH)),!,
   nop(sanity(on_f_debug(same_modules(MH,MHH)))),!.
*/
%full_transform(Why,MH,MHH):- \+ compound(MH),!,
%   must_det(fully_expand_real(change(assert,Why),MH,MHH)),!.
     % nop(sanity(on_f_debug(same_modules(MH,MHH)))).
%full_transform(Op,==> CI,SentO):- nonvar(CI),!, full_transform(Op,CI,SentO).
%full_transform(Op,isa(I,C),SentO):- nonvar(C),!,must_ex(fully_expand_real(Op,isa(I,C),SentO)),!.
%full_transform(_,CI,SentO):- CI univ_safe [_C,I], atom(I),!,if_defined(do_renames(CI,SentO),CI=SentO),!.
full_transform(Why,MH,MHH):-
 must_det(fully_expand_real(change(assert,Why),MH,MHH)),!,
 nop(sanity(on_f_debug(same_modules(MH,MHH)))).

same_modules(MH,MHH):- strip_module(MH,HM,_),strip_module(MHH,HHM,_),!,
   HM==HHM.

%full_transform_compound(Op,ISA,SentO):- compound(ISA),isa(I,C)=ISA,!, must_ex(fully_expand_real(Op,isa(I,C),SentO)),!.
%full_transform_compound(Why,MH,MHH):-
% must_det(fully_expand_real(change(assert,Why),MH,MHH)),!.
   % nop(sanity(on_f_debug(same_modules(MH,MHH)))).


%:- if(\+ current_prolog_flag(umt_local,false)).

listing_i(MP):- % strip_module(MP,M,P),!,
 forall(to_mpi_matcher(MP,MM:PI),
   listing_mpi(MP,MM:PI)). 

:- reconsult(library(listing)).
%:- system:reexport(library(xlisting)).

%listing_mpi(_MP,MMPI):-  (predicate_property(MMPI,number_of_clauses(NC))->NC==0;true),!,
%  unify_listing_header(MMPI),prolog_listing_list_clauses(MMPI, none),!.
%listing_mpi(_MP,MMPI):- !,unify_listing_header(MMPI), 
%   prolog_listing:list_clauses(MMPI, none).
listing_mpi(_MP,MM:PI):- forall(clause_u(MM:PI,B,R),foo:once(portray_hbr(MM:PI,B,R))).

listing_u(P):-call_u_no_bc(xlisting((P,-lmcache,/*-spft,*/-xlisting))),!.

attvar_op_fully(What,MH):- !, attvar_op(What,MH).
%attvar_op_fully(What,M:H):- must_notrace_pfc(full_transform_warn_if_changed(change(What,attvar_op_fully),H,true,HH,true)),!,each_E(attvar_op(What),M:HH,[]).
%attvar_op_fully(What,MH):- full_transform_warn_if_changed(What, MH,MHH),each_E(attvar_op(What),MHH,[]).

throw_depricated:- trace_or_throw_ex(throw_depricated).

do_db_checks:- fail.

assert_u(MH):- assert_u_no_dep(MH).

assert_u_no_dep(X):- do_db_checks, check_never_assert(X),fail.
assert_u_no_dep(MH):- fix_mp(change(assert,assert_u),MH,MHA),
    attvar_op_fully(db_op_call(assert,assert_i), MHA),expire_tabled_list(MHA).

asserta_u(X):-  do_db_checks, check_never_assert(X),fail.
asserta_u(MH):- fix_mp(change(assert,asserta_u),MH,MHA),attvar_op_fully(db_op_call(asserta,asserta_i),MHA).

assertz_u(X):- do_db_checks, check_never_assert(X),fail.
assertz_u(MH):- fix_mp(change(assert,assertz_u),MH,MHA),attvar_op_fully(db_op_call(asserta,assertz_i),MHA).

% retract_u((H:-B)):- !, show_failure(retract((H:-B))).
retract_u(H):- retract_u0(H) *-> true; ((fail,attvar_op_fully(db_op_call(retract,retract_u0),H))).

retract_u0(X):- do_db_checks, check_never_retract(X),fail.
retract_u0(H0):- strip_module(H0,_,H),(H = ( \+ _ )),!,trace_or_throw_ex(pfcWarn(retract_u(H0))),expire_tabled_list(H).
retract_u0(M:(H:-B)):- atom(M),!, M:clause_u(H,B,R),erase(R),expire_tabled_list(H).
retract_u0(M:(H)):- atom(M),!, M:clause_u(H,true,R),erase(R),expire_tabled_list(H).
retract_u0((H:-B)):-!,clause_u(H,B,R),erase(R),expire_tabled_list(H).
retract_u0(H):- clause_u(H,true,R),erase(R),expire_tabled_list(H).

:- lmcache:import(retract_u0/1).

retractall_u(X):- do_db_checks, check_never_retract(X),fail.
retractall_u(H):- attvar_op_fully(db_op_call(retractall,retractall_u0),H).

retractall_u0(X):- do_db_checks, check_never_retract(X),fail.
retractall_u0(H):- forall(clause_u(H,_,R),erase(R)),expire_tabled_list(H).



clause_u(C):- expand_to_hb(C,H,B),!,clause_u(H,B).


%% clause_u( ?H, ?B) is semidet.
%

% clause_u(H,B):-  current_prolog_flag(unsafe_speedups , true) , ground(H:B),!,clause(H,B).
clause_u(H,B):- clause_u(H,B,_).
%clause_u(H,B):- clause_true( ==>( B , H) ).
%clause_u(H,B):- clause_true( <-( H , B) ).

match_attvar_clauses(HH,BB,H,B):- 
    matrialize_clause((H:-B),C),
 matrialize_clause((HH:-BB),CC),!,
 C=CC.

matrialize_clause((H:-B),(H:-B)):- \+ compound(B),!.
matrialize_clause((H:-attr_bind(Attribs,B)),(H:-B)):-!, attr_bind(Attribs).
matrialize_clause((H:-attr_bind(Attribs)),(H:-true)):-!, attr_bind(Attribs).

:- set_prolog_flag(clause_u_h_exact,false).
:- set_prolog_flag(clause_u_mh_inherit,false).

should_inherit(_, M,_,TF):- mtInherits(M),!,TF=true.
should_inherit(_, M,_,TF):- mtNotInherits(M),!,TF=false.
should_inherit(h, _,_,TF):- current_prolog_flag(clause_u_h_exact,false) -> TF = true ; TF = false.
should_inherit(mh,_,_,TF):- current_prolog_flag(clause_u_mh_inherit,TF).

%% clause_u( +H, ?B, ?Why) is semidet.
%
% PFC Clause.
%
clause_u(MH,B,R):- nonvar(R),!,must_ex(clause_i(M:H,B,R)),must_ex((MH=(M:H);MH=(H))),!.
clause_u(H,B,Ref):-var(H),!,trace_or_throw_ex(var_clause_u(H,B,Ref)).
clause_u((H:-BB),B,Ref):- is_true(B),!, trace_or_throw_ex(malformed(clause_u((H:-BB),B,Ref))),clause_u(H,BB,Ref).
clause_u((H:-B),BB,Ref):- is_true(B),!, trace_or_throw_ex(malformed(clause_u((H:-B),BB,Ref))),clause_u(H,BB,Ref).

clause_u(H,B,R):-clause_u_visible(H,B,R),B \= inherit_above(_,_).

module_clause(MHB):- strip_module(MHB,M,HB), expand_to_hb(HB,H,B),clause(M:H,B,R),clause_property(R,module(CM)),CM==M.

clause_u_visible(M:H,B,R):- !, clause_i(M:H,B,R),clause_ref_module(R). % need? \+ reserved_body_helper(B) 
clause_u_visible(MH,B,R):- Why = clause(clause,clause_u),
 quietly_ex(fix_mp(Why,MH,M,H)),
   (clause(M:H,B,R)*->true;clause_i(M:H,B,R)).
   
% clause_u(H,B,Why):- has_cl(H),clause_u(H,CL,R),pfc_pbody(H,CL,R,B,Why).
%clause_u(H,B,backward(R)):- R=(<-(H,B)),clause_u(R,true).
%clause_u(H,B,equiv(R)):- R=(<==>(LS,RS)),clause_u(R,true),(((LS=H,RS=B));((LS=B,RS=H))).
%clause_u(H,true, pfcTypeFull(R,Type)):-is_ftNonvar(H),!,pfcDatabaseTerm(F/A),make_functor(R,F,A),pfcRuleOutcomeHead(R,H),clause(R,true),pfcTypeFull(R,Type),Type\=rule.
%clause_u(H,true, pfcTypeFull(R)):-pfcDatabaseTerm(F/A),make_functor(R,F,A),pfcTypeFull(R,Type),Type\=rule,clause(R,true),once(pfcRuleOutcomeHead(R,H)).
%clause_u('nesc'(H),B,forward(Proof)):- is_ftNonvar(H),!, clause_u(H,B,Proof).
%clause_u(H,B,forward(R)):- R=(==>(B,H)),clause_u(R,true).

clause_uu(H,B,Ref):- var(H),var(Ref),!,trace_or_throw_ex(var_clause_u(H,B,Ref)).
clause_uu(M:H,B,R):- safe_functor(H,F,A),safe_functor(HH,F,A),!,should_inherit(mh,M,H,TF),clause_u_attv_m(mh,TF,M,HH,BB,R),match_attvar_clauses(HH,BB,H,B).
clause_uu(  H,B,R):- safe_functor(H,F,A),safe_functor(HH,F,A),!,defaultAssertMt(M),should_inherit(h,M,H,TF),clause_u_attv_m(mh,TF,M,HH,BB,R),match_attvar_clauses(HH,BB,H,B).


clause_u_attv_m(MP,Herit,M,H,B,Ref):-var(H),var(Ref),!,trace_or_throw_ex(var_clause_u_attv_m(MP,Herit,M,H,B,Ref)).
clause_u_attv_m(_,_,M,H,B,R):- nonvar(R),!,must_ex(clause_i(M:H,B,R)),!. % must_ex((MH=(M:H);MH=(H))),!.
clause_u_attv_m(MP,Herit,M,(H:-BB),B,Ref):- is_true(B),!, trace_or_throw_ex(malformed(clause_u(MP,Herit,M,(H:-BB),B,Ref))),clause_u(H,BB,Ref).
clause_u_attv_m(MP,Herit,M,(H:-B),BB,Ref):- is_true(B),!, trace_or_throw_ex(malformed(clause_u(MP,Herit,M,(H:-B),BB,Ref))),clause_u(H,BB,Ref).
clause_u_attv_m(MP,Herit,M,H,B,Ref):- clause_u_attv_b(MP,Herit,M,H,B,Ref),
   B \= inherit_above(M,_), (Herit->clause_ref_module(Ref);clause_ref_module(M,Ref)).

clause_u_attv_b(mh,false,M,H,B,R):- !, clause_i(M:H,B,R), B \= inherit_above(M,_).
clause_u_attv_b(mh,true,IM,H,B,R):- genlMt_each(IM,M),clause_i(M:H,B,R), B \= inherit_above(M,_).
clause_u_attv_b(mh,_,M,H,B,R):- !, clause_u_attv_mhbr(M:H,B,R).
clause_u_attv_b(h,false,M,H,B,R):- clause_i(M:H,B,R).
clause_u_attv_b(h,_,M,H,B,R):- clause_u_attv_mhbr(M:H,B,R).
clause_u_attv_b(h,true,M,H,B,R):- clause_i(M:H,B,R).

genlMt_each(M,M).
genlMt_each(M,O):- genlMt(M,P),(O=P;genlMt(P,O)).

clause_u_attv_mhbr(MH,B,R):-
  Why = clause(clause,clause_u),
 ((quietly_ex(fix_mp(Why,MH,M,H)),
  clause(M:H,B,R))*->true;
           (fix_mp(Why,MH,M,CALL)->clause_i(M:CALL,B,R))).

%% clause_u( +VALUE1, ?H, ?B, ?Proof) is semidet.
%
% Hook To [baseKB:clause_u/4] For Module Mpred_pfc.
% PFC Provide Storage Clauses.
%
%clause_u(pfc,H,B,Proof):-clause_u(H,B,Proof).


clause_ref_module(M,Ref):- (clause_property(Ref,module(CM))-> M=CM; false).  % clause_ref_module(Ref) ?
clause_ref_module(Ref):- clause_property(Ref,module(CM)),module_direct(CM).

module_direct(CM):- t_l:exact_kb(M)*->CM=M; true.

with_exact_kb(MM,Call):- locally_tl(exact_kb(MM),Call).


lookup_kb(MM,MHB):- strip_module(MHB,M,HB),
     expand_to_hb(HB,H,B),
      (MM:clause(M:H,B,Ref)*->true; M:clause(MM:H,B,Ref)),
      %clause_ref_module(Ref),
      clause_property(Ref,module(MM)).

% lookup_u/cheaply_u/call_u/clause_b
lookup_m(SPFT):- callable(SPFT),!,clause_b(SPFT).
lookup_m(SPFT):- callable(SPFT),!,baseKB:on_x_rtrace(SPFT).


lookup_u(SPFT):- callable(SPFT),on_x_rtrace(SPFT).
% baseKB:SPFT:- current_prolog_flag(unsafe_speedups , true) , !,baseKB:mtHybrid(MT),call(MT:SPFT).
% lookup_u(H):-lookup_u(H,_).

lookup_u(MH,Ref):- nonvar(Ref),!,
                   must_ex(clause(H,B,Ref)),
                   clause_ref_module(Ref),
                   must_ex(hb_to_clause(H,B,MHI)),!,
                   MH=MHI.

lookup_u((MH,H),Ref):- nonvar(MH),!,lookup_u(MH),lookup_u(H,Ref).
lookup_u(MH,Ref):- clause_u(MH,true,Ref),clause_ref_module(Ref).


:- thread_local(t_l:current_defaultAssertMt/1).
:- was_module_transparent(with_umt/2).
:- was_export(with_umt/2).
%% with_umt( +ABOX, ?G) is semidet.
%
% Using User Microtheory.
%

with_umt(mud_telnet,P):- !,with_umt(baseKB,P).
with_umt(U,G):- sanity(stack_check(5000)),
  (t_l:current_defaultAssertMt(W)->W=U,!,call_from_module(U,G)).
%with_umt(user,P):- !,with_umt(baseKB,P).
with_umt(M,P):-
  (clause_b(mtHybrid(M))-> W=M;defaultAssertMt(W)),!,
   locally_tl(current_defaultAssertMt(W),
     call_from_module(W,P)).


/*
listing_u(P):- (listing(P)).
assert_u(A):- assert(A).
asserta_u(A):- asserta(A).
assertz_u(A):- assertz(A).
retract_u((H:-B)):-!, clause_u(H,B,R),erase(R).
retract_u(H):-!, clause_u(H,true,R),erase(R).
retractall_u(H):- forall(clause_u(H,_,R),erase(R)).
clause_u(H,B):- clause_u(H,B,_).
clause_u(H,B,R):- clause_i(H,B,R).
call_u_no_bc(G):- G.
*/

%% each_E(+P2,+HT,+S) semidet.
%
% Call P(E,S). each Element in the list.
%
each_E(P,HV,S):- check_context_module, var(HV),!,apply(P,[HV|S]).
each_E(P,M:(H,T),S) :- must_be(atom,M),!,each_E(P,M:H,S), each_E(P,M:T,S).
each_E(P,M:[H],S) :- must_be(atom,M),!,each_E(P,M:H,S).
each_E(P,M:[H|T],S) :- must_be(atom,M),!,each_E(P,M:H,S), each_E(P,M:T,S).
each_E(P,M:HT,S) :- M=='$si$',!,apply(P,[M:HT|S]).
each_E(P,M:HT,S) :- !, must_be(atom,M),M:each_E(P,HT,S).
each_E(P,[H],S) :- !, each_E(P,H,S).
each_E(P,[H|T],S) :- !, each_E(P,H,S), each_E(P,T,S).
each_E(P,(H,T),S) :- !, each_E(P,H,S), each_E(P,T,S).
each_E(P,H,S) :- apply(P,[H|S]).


% =================================================
% ==============  UTILS END          ==============
% =================================================

:- style_check(+singleton).
%   File   : pfc_syntax.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Purpose: syntactic sugar for Pfc - operator definitions and term expansions.

:- op(500,fx,'-').
:- op(300,fx,'~').
:- op(1050,xfx,('==>')).
:- op(1050,xfx,'<==>').
:- op(1050,xfx,('<-')).
:- op(1100,fx,('==>')).
:- op(1150,xfx,('::::')).

:- export('__aux_maplist/2_call+0'/1).
:- meta_predicate('__aux_maplist/2_call+0'(0)).
'__aux_maplist/2_call+0'([]).
'__aux_maplist/2_call+0'([A|B]) :-!,
        call(A),
        '__aux_maplist/2_call+0'(B).
'__aux_maplist/2_call+0'(_:[]).
'__aux_maplist/2_call+0'(M:[A|B]) :-
        M:call(A),
        '__aux_maplist/2_call+0'(M:B).


:- use_module(library(lists)).



%  predicates to examine the state of pfc_


pp_qu:- call_u_no_bc(listing(que/1)).

%   File   : pfc_lib.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Updated: 10/11/87, ...
%            4/2/91 by R. McEntire: added calls to valid_dbref as a
%                                   workaround for the Quintus 3.1
%                                   bug in the recorded database.
%   Purpose: core Pfc predicates.


% ============================================
% % initialization of global assertons
% ============================================

%%   pfc_set_default(P,Q) is det.
%
%  if there is any fact unifying with P,
% via lookup_u/1 then do
%  nothing, else assert_u Q.
%
pfc_set_default(GeneralTerm,Default):-
  clause_u(GeneralTerm,true) -> true ; assert_u_no_dep(Default).

%  tms is one of {none,local,cycles} and controles the tms alg.
% :- pfc_set_default(tms(_),tms(cycles)).

% Pfc Propagation strategy. pm(X) where P is one of {direct,depth,breadth}
% :- must_ex(pfc_set_default(pm(_), pm(direct))).


ain_expanded(IIIOOO):- pfc_ain((IIIOOO)).

ain_expanded(IIIOOO,S):- pfc_ain((IIIOOO),S).


%% pfc_ainz(+G, ?S) is semidet.
%
% PFC Ainz.
%
pfc_ainz(G):- locally_tl(assert_to(z),pfc_ain(G)).
pfc_ainz(G,S):- locally_tl(assert_to(z),pfc_ain(G,S)).

%% pfc_aina(+G, ?S) is semidet.
%
% PFC Aina.
%
pfc_aina(G):- locally_tl(assert_to(a),pfc_ain(G)).
pfc_aina(G,S):- locally_tl(assert_to(a),pfc_ain(G,S)).

%%  pfc_ain(P,S)
%
%  asserts P into the dataBase with support from S.
%
%  pfc_ain/2 and pfc_post/2 are the proper ways to add new clauses into the
%  database and have forward reasoning done.
%
pfc_ain(_:P):- retractall(t_l:busy(_)), P==end_of_file,!.
pfc_ain(_:props(_,EL)):- EL==[],!.
pfc_ain(M:P):- M:get_source_uu(UU),M:pfc_ain(M:P,UU).

pfc_add(P):- pfc_ain(P).

%%  pfc_ain(P,S)
%
%  asserts P into the dataBase with support from S.
%

decl_assertable_module(AM):- nop((must_ex(dynamic(AM:spft/3)))).

% pfc_ain_cm(SM:(==>(AM:P)),P,AM,SM):- SM\==AM, current_predicate(SM:spft/3),!,decl_assertable_module(SM).
pfc_ain_cm(SM:(==>(AM:P)),==>P,AM,SM):- AM==SM,!,decl_assertable_module(AM).
pfc_ain_cm(SM:(==>(_:(AM:P :- B))),==>(AM:P :- SM:B),AM,SM):- nonvar(P), decl_assertable_module(AM).
pfc_ain_cm(SM:(==>(AM:P)),==>P,AM,AM):- decl_assertable_module(AM),!,decl_assertable_module(SM).
pfc_ain_cm((==>(AM:P)),==>P,AM,AM):- decl_assertable_module(AM),!.
pfc_ain_cm((==>(P)),==>P,AM,SM):- get_assert_to(AM), guess_pos_source_to(SM),!.
pfc_ain_cm(M:(==>(P)),==>P,AM,AM):- context_module(M),get_assert_to(AM),!. %  guess_pos_source_to(SM).
pfc_ain_cm(AM:(==>(P)),==>P,AM,AM):- !.

pfc_ain_cm(AM:P,P,SM,AM):- !, context_module(SM).
pfc_ain_cm(   P,P,SM,AM):- get_assert_to(AM), context_module(SM).


guess_pos_assert_to(ToMt):- 
    ((guess_pos_source_to(ToMt), \+ is_code_module(ToMt), mtCanAssert(ToMt))*-> true; 
    ((guess_pos_source_to(ToMt), \+ is_code_module(ToMt))*-> true ;
    ((guess_pos_source_to(ToMt), mtCanAssert(ToMt))*-> true;    
    guess_pos_source_to(ToMt)))).

:- dynamic(baseKB:mtExact/1).


% guess_pos_source_to(ToMt):- t_l:current_defaultAssertMt(ToMt).

guess_pos_source_to(ToMt):- no_repeats(ToMt,guess_pos_source_to0(ToMt)).

guess_pos_source_to0(ToMt):- t_l:current_defaultAssertMt(ToMt).
guess_pos_source_to0(ToMt):- '$current_source_module'(ToMt).
guess_pos_source_to0(ToMt):- context_module(ToMt).
guess_pos_source_to0(ToMt):- '$current_typein_module'(ToMt).
guess_pos_source_to0(ToMt):- guess_mpred_file(File),module_property(ToMt,file(File)),File\==ToMt.
guess_pos_source_to0(ToMt):- prolog_load_context(module,ToMt).
guess_pos_source_to0(ToMt):- defaultAssertMt(ToMt).
guess_pos_source_to0(baseKB).

guess_mpred_file(File):- which_file(File).
guess_mpred_file(File):- loading_source_file(File),get_file_type_local(File,pfc).

get_assert_to(ABox):- (var(ABox)->guess_pos_assert_to(ABox);(guess_pos_assert_to(ABoxVar),ABox=ABoxVar)),!.

% get_query_from(SM):- '$current_source_module'(SM).
get_query_from(SM):- guess_pos_assert_to(SM), \+ is_code_module(SM),!.
get_query_from(baseKB).

:- baseKB:import(is_code_module/1).
is_code_module(system).
is_code_module(user).
is_code_module(baseKB):-!,fail.
is_code_module(pfc_lib).
is_code_module(M):- clause_b(mtProlog(M)),!,fail.
is_code_module(M):- module_property(M,class(system)).
is_code_module(M):- module_property(M,class(library)).
is_code_module(baseKB):-!,fail.
is_code_module(Mt):- clause_b(mtHybrid(Mt)),!,fail.
is_code_module(M):- module_property(M,file(_)).
%call_u_mp(user, P1 ):- !,  call_u_mp(baseKB,P1).


pfc_ain(MTP,S):- quietly_ex(is_ftVar(MTP)),!,trace_or_throw_ex(var_pfc_ain(MTP,S)).
pfc_ain(MTP,S):- pfc_ain_cm(MTP,P,AM,SM),pfc_ain_now4(SM,AM,P,S).


pfc_ain_now4(SM,ToMt,P,(mfl4(VarNameZ,FromMt,File,Lineno),UserWhy)):- sanity(stack_check),ToMt \== FromMt,!,
  pfc_ain_now4(SM,ToMt,P,(mfl4(VarNameZ,ToMt,File,Lineno),UserWhy)).

pfc_ain_now4(SM0,AM0,PIn,S):- SM0==AM0, is_code_module(AM0),!,
  get_assert_to(AM),get_query_from(SM),!,pfc_ain_now4(SM,AM,PIn,S).
  
pfc_ain_now4(SM,AM,PIn,S):- % module_sanity_check(SM),
  nop(module_sanity_check(AM)),
  call_from_module(AM, 
    with_source_module(SM,
      locally_tl(current_defaultAssertMt(AM), SM:pfc_ain_now(PIn,S)))).

pfc_ain_now(PIn,S):-
  PIn=P, % must_ex(add_eachRulePreconditional(PIn,P)),  
  must_ex(full_transform(ain,P,P0)),!, % P=P0,  
  must_ex(ain_fast(P0,S)),!,
  nop(ignore((P\=@=P0, pfc_db_type(P,fact(_)),show_failure(mpred_fwc(P))))).

pfc_ain_now(P,S):- pfcWarn("pfc_ain(~p,~p) failed",[P,S]),!,fail.


ain_fast(P):-  \+ t_l:is_repropagating(_),clause_asserted(P),!.
ain_fast(P):- call_u((( get_source_uu(UU), ain_fast(P,UU)))).

ain_fast(P,S):- quietly_ex((maybe_updated_value(P,RP,OLD),subst(S,P,RP,RS))),!,ain_fast(RP,RS),ignore(pfc_retract_i(OLD)).

% ain_fast(P,S):- loop_check_term(ain_fast0(P,S),ain_fast123(P),(trace,ain_fast0(P,S))).

ain_fast(P,S):-
  %retractall(t_l:busy(_)),
  fwc1s_post1s(One,Two),
  filter_buffer_trim('$last_mpred_fwc1s',One),
  filter_buffer_trim('$last_pfc_post1s',Two),
  each_E(pfc_post1,P,[S]),!,
  pfc_run.

:- abolish(lmconf:eachRule_Preconditional/1).
:- abolish(lmconf:eachFact_Preconditional/1).
:- dynamic(lmconf:eachRule_Preconditional/1).
:- dynamic(lmconf:eachFact_Preconditional/1).
lmconf:eachRule_Preconditional(true).
lmconf:eachFact_Preconditional(true).

add_eachRulePreconditional(A,A):-var(A),!.
add_eachRulePreconditional(B::::A,B::::AA):-add_eachRulePreconditional(A,AA).
add_eachRulePreconditional(A==>B,AA==>B):-!,add_eachRulePreconditional_now(A,AA).
add_eachRulePreconditional(A<==>B, ('==>'(AA , B) , (BB ==> A)) ):-!,add_eachRulePreconditional_now(A,AA),add_eachRulePreconditional_now(B,BB).
add_eachRulePreconditional((B <- A), (B <- AA)) :-!,add_eachRulePreconditional_now(A,AA).
add_eachRulePreconditional(A,AA):-add_eachFactPreconditional_now(A,AA).

add_eachFactPreconditional_now(A,A):- lmconf:eachFact_Preconditional(true),!.
add_eachFactPreconditional_now(A,(Was==>A)):- lmconf:eachFact_Preconditional(Was),!.

add_eachRulePreconditional_now(A,A):- lmconf:eachRule_Preconditional(true),!.
add_eachRulePreconditional_now(A,(Was,A)):- lmconf:eachRule_Preconditional(Was),!.




remove_negative_version(_P):- current_prolog_flag(unsafe_speedups , true) ,!.
remove_negative_version((H:-B)):- !,
  % TODO extract_predciates((H:-B),Preds),trust(Preds),
  with_no_pfc_trace_exec((
  once((get_why_uu(S),!,
  must_ex(pfc_ain(\+ (~(H) :- B), S)))))),!.
remove_negative_version(P) :- \+ pfc_non_neg_literal(P),!.

remove_negative_version(P):-
  % TODO extract_predciates(P,Preds),trust(Preds),
  with_no_pfc_trace_exec((
  once((get_why_uu(S),!,
  must_ex(pfc_ain(\+ (~(P)), S)))))),!.

%fwc1s_post1s(0,0):-!.
fwc1s_post1s(1,1):-!.
%fwc1s_post1s(1,2):-!.
/*
fwc1s_post1s(3,0):-!.
fwc1s_post1s(3,0):-!.
%fwc1s_post1s(1,2):- flag_call(unsafe_speedups == false) ,!.

fwc1s_post1s(1,3):- fresh_mode,!.
fwc1s_post1s(1,2):- current_prolog_flag(pfc_booted,true),!.
% fwc1s_post1s(10,20):- defaultAssertMt(Mt)->Mt==baseKB,!.
fwc1s_post1s(1,2).
*/

fresh_mode :- \+ current_prolog_flag(pfc_booted,true), \+ flag_call(unsafe_speedups == false) .
plus_fwc :- \+ fresh_mode.

plus_fwc(P):- is_ftVar(P),!,trace_or_throw_ex(var_plus_fwc(P)).
plus_fwc(support_hilog(_,_)):-!.
plus_fwc('==>'(_,_)):-!.
plus_fwc(P):- gripe_time(0.6,
  (plus_fwc
    ->
      loop_check_term(must_ex(mpred_fwc(P)),plus_fwc(P),true);true)),!.


maybe_updated_value(UP,R,OLD):- % \+ current_prolog_flag(unsafe_speedups , true) ,
    compound(UP),
    get_assertion_head_unnegated(UP,P),!,
    compound(P),
    once((arg(N,P,UPDATE),is_relative(UPDATE))),
    must_ex(flag_call(unsafe_speedups == false) ),
    replace_arg(P,N,Q_SLOT,Q),
    must_ex(call_u(Q)), update_value(Q_SLOT,UPDATE,NEW), must_ex( \+ is_relative(NEW)),
    replace_arg(Q,N,NEW,R),!,R\=@=UP,subst(UP,P,Q,OLD).



implicitly_true(Var):- is_ftVar(Var),!,fail.
implicitly_true(true).
implicitly_true(end_of_file).
implicitly_true(props(_,L)):- L ==[].

abby_normal_ERR(Var):- is_ftVar(Var),!.
abby_normal_ERR( isa(_,_,_),   _).
abby_normal_ERR( tCol(COMMA),   _):- COMMA==','.
abby_normal_ERR( tCol(VAR),   _):- var(VAR).
abby_normal_ERR( P, _):- \+ \+ P = props(_,[]).   

%% pfc_post(+Ps,+S)
%
% tries to assert a fact or set of fact to the database.  For
% each fact (or the singleton) pfc_post1 is called. It always succeeds.
%
pfc_post(P, S):- full_transform(post,P,P0),each_E(pfc_post1,P0,[S]).

pfc_post( P):- get_why_uu(UU), pfc_post( P,   UU).
pfc_post1( P):- get_why_uu(UU), pfc_post1( P,   UU).

%% pfc_post1(+P,+S) is det.
%
% tries to add a fact to the database, and, if it succeeded,
% adds an entry to the Pfc queue for subsequent forward chaining.
% It always succeeds.
%

pfc_post1(P, S) :- show_success(abby_normal_ERR(P,S)),break_ex,!,fail.
pfc_post1(P, S):- each_E(pfc_post2,P,[S]).


pfc_post2( P,   S):- quietly_ex(( sanity(nonvar(P)),fixed_negations(P,P0),P\=@=P0)),!, pfc_post2( P0,   S).

pfc_post2(Fact, _):- quietly_ex(((true;current_prolog_flag(unsafe_speedups , true)) , ground(Fact),
   \+ t_l:is_repropagating(_),
   fwc1s_post1s(One,_Two),Three is One * 1,
   filter_buffer_n_test('$last_pfc_post1s',Three,Fact))),!.

%pfc_post2(P,S):- gripe_time(0.6,loop_check_early(pfc_post12(P,S),true)).
pfc_post2(P,S):- gripe_time(16,(pfc_post12(P,S),true)).


pfc_post_exactly(P):- current_why(S),pfc_enqueue(P,S).
pfc_remove_exactly(P):- remove_if_unsupported(P).

:- module_transparent(pfc_post_exactly/1).
:- module_transparent(pfc_post1/2).
:- module_transparent(pfc_post12/2).
:- export(pfc_post12/2).

leave_some_vars_at_el(action_rules).
leave_some_vars_at_el(agent_text_command).
leave_some_vars_at_el(rtArgsVerbatum).
leave_some_vars_at_el(==>).

is_ftOpen(A):- member(A,['$VAR'('????????????'),'$VAR'(_)]).

is_ftOpenSentence(P):- compound(P), safe_functor(P,F,N), \+ leave_some_vars_at_el(F),
   (arg(N,P,A);(N\==1,arg(1,P,A))),is_ftOpen(A).
is_ftOpenSentence(P):- is_ftOpen(P).


pfc_post12_withdraw( P,   S):- show_call(pfcWithdraw(P,S)), \+ pfc_supported(P),!.
%pfc_post12_withdraw( P,   S):- is_user_reason(S), show_call(pfcWithdraw(P)), \+ pfc_supported(P),!.
%pfc_post12_withdraw( P,   S):- is_user_reason(S),!, (pfcWithdraw_fail_if_supported(P,S) -> true ;  show_call(pfc_remove2(P,S))).
pfc_post12_withdraw( P,   S):- ignore(show_call(pfcWithdraw_fail_if_supported(P,S))),!.

pfc_post12_negated( P,   S):- pfcWithdraw_fail_if_supported(P,S), pfc_post13(~P,S),!.
pfc_post12_negated( P,   S):- pfc_remove2(P,S), show_call( \+ pfc_supported(P)),!, show_call((nop(2), pfc_post13(~P,S))),!.
pfc_post12_negated( P,   S) :- pfc_get_support(P,S2), 
    color_line(magenta,2),
    dmsg_pretty((pfc_post12( ~ P,   S) :- pfc_get_support(P,S2))),
    color_line(magenta,1),color_line(green,1),color_line(yellow,1),
    color_line(magenta,1),color_line(green,1),color_line(yellow,1),
    color_line(magenta,1),color_line(green,1),color_line(yellow,1),
    pfc_trace_op(blast,P),
    pfcWhy_1(P),
    must(pfc_unfwc(P)),
    must(pfc_post13(~P,S)),!.




pfc_post12(P, _):- must_be(nonvar,P),P==true,!.
% pfc_post12(P, S):- quietly_ex((is_ftOpenSentence(P)->wdmsg_pretty((warn((var_pfc_post1(P, S))))))),fail.
pfc_post12( \+  P,   S):- pfc_post12_withdraw( P,   S),!.
pfc_post12(  ~  P,   S):- pfc_post12_negated( P,   S),!.

/*
pfc_post12( \+ P,   S):- (must_be(nonvar,P)), !,doall( must_ex(pfc_post1_rem(P,S))).

% TODO - FIGURE OUT WHY THIS IS NEEDED - WELL THINKING AOBUT IT AND UIT SEEMS WRONG
pfc_post12( ~ P,   S):- fail, (must_be(nonvar,P)), sanity((ignore(show_failure(\+ is_ftOpenSentence(P))))),
   quietly_ex((  \+ pfc_unique_u(P))),
   with_current_why(S,with_no_breaks((nonvar(P),doall(pfc_remove(P,S)),must_ex(fcUndo(P))))),fail.
*/

pfc_post12(P,S):- quietly_ex((maybe_updated_value(P,RP,OLD))),!,subst(S,P,RP,RS),pfc_post13(RP,RS),ignore(pfc_retract_i(OLD)).

%  TODO MAYBE 
pfc_post12(pfcAction(P),S):- !, 
  with_current_why(S,call(P)), pfc_post13(pfcAction(P),S).

pfc_post12(P,S):- pfc_post13(P,S).

% Two versions exists of this function one expects for a clean database (fresh_mode) and adds new information.
% tries to assert a fact or set of fact to the database.
% The other version is if the program is been running before loading this module.
%
pfc_post13_unused(P,S):- fail,
  fresh_mode,!,
  % db pfc_ain_db_to_head(P,P2),
  % pfcRemoveOldVersion(P),
 \+ \+ pfc_add_support(P,S),
  ( (\+ pfc_unique_u(P)) -> true ;
  ( assert_u_confirm_if_missing(P),
     !,
     pfc_trace_op(add,P,S),
     !,
     pfc_enqueue(P,S),
     !)),
  plus_fwc(P),!.


% this would be the very inital by Tim Finnin...
pfc_post13_unused(P,S):- fail, fresh_mode,
 ignore(( %  db pfc_ain_db_to_head(P,P2),
  % pfcRemoveOldVersion(P),
  pfc_add_support(P,S),
  pfc_unique_u(P),
  assert_u_confirm_if_missing(P),
  pfc_trace_op(add,P,S),
  !,
  pfc_enqueue(P,S))),
  !.


/*
% Expects a clean database and adds new information.
pfc_post13_unused(P,S):-  fail,!,
  % db pfc_ain_db_to_head(P,P2),
  % pfcRemoveOldVersion(P),
  must_ex( \+ \+ pfc_add_support(P,S)),
  ( \+ pfc_unique_u(P)
    -> clause_asserted_u(P)
    ; ( assert_u_confirmed_was_missing(P),
        !,
        pfc_trace_op(add,P,S),
        !,
        pfc_enqueue(P,S),
        !)).
*/

/*
pfc_post13((H:-B),S):- 
  with_current_why(S,
    show_call(pfc_do_hb_catchup_now_maybe(H,B))),
  fail.
*/

% this for complete repropagation
pfc_post13(P,S):- t_l:is_repropagating(_),!,
 ignore(( %  db pfc_ain_db_to_head(P,P2),
  % pfcRemoveOldVersion(P),
  pfc_add_support(P,S),
  (pfc_unique_u(P)->
     assert_u_confirmed_was_missing(P);
     assert_u_confirm_if_missing(P)),
  pfc_trace_op(add,P,S),
  !,
  pfc_enqueue(P,S))),
  !.

/*
pfc_post13(P,S):- true, !,
 ignore(( %  db pfc_ain_db_to_head(P,P2),
  % pfcRemoveOldVersion(P),
  pfc_add_support(P,S),
  (pfc_unique_u(P)->
     assert_u_confirmed_was_missing(P);
     assert_u_confirm_if_missing(P)),
  pfc_trace_op(add,P,S),
  !,
  pfc_enqueue(P,S))),
  !.
*/


% Expects a *UN*clean database and adds new information.
% (running the program is been running before loading this module)
%
%  (gets the status in Support and in Database)
pfc_post13(P,S):- !,
 %  set_varname_list([]),!,
   copy_term_vn((P,S),(PP,SS)),
 %  checks to see if we have forward chain the knowledge yet or
  gripe_time(0.1, must_ex(get_pfc_support_status(P,S,PP,SS,Was))),!,
  pfc_post123(P,S,PP,Was).


:- thread_local(t_l:exact_assertions/0).

with_exact_assertions(Goal):-
  locally_tl(exact_assertions,Goal).
 

% The cyclic_break is when we have regressions arouind ~ ~ ~ ~ ~

get_pfc_support_status(_P,_S, PP,(F,T),Was):- 
  t_l:exact_assertions,!,
  (clause_asserted_u(spft(PP,F,T)) -> Was = exact ; Was = none).

get_pfc_support_status(_P,_S, PP,(F,T),Was):- 
  % t_l:exact_assertions,
  !,
  (clause_asserted_u(spft(PP,F,T)) -> Was = exact ; Was = none).

get_pfc_support_status(P,_S, PP,(FF,TT),Was):-
  Simular=simular(none),
  copy_term(PP,PPP),
  ((((lookup_spft(PPP,F,T),variant_u(P,PP))) *->
     ((variant_u(TT,T),same_file_facts0(F,FF)) -> (Was = exact , ! ) ; 
      (nb_setarg(1,Simular,(F,T)),!,fail))
    ; Was = none) -> true ; ignore(Was=Simular)),!.

% pfc_post123(_P,_S,_PP,exact):- current_prolog_flag(pfc_cheats,true), !.

pfc_post123(P,S,PP,Was):-
 % cyclic_break((P,S,PP,Was)),
 %  if we''ve asserted what we''ve compiled  
  gripe_time(0.22, must_ex(get_pfc_assertion_status(P,PP,AStatus))),!,
  gripe_time(0.44, must_ex(pfc_post_update4(AStatus,P,S,Was))),!.

get_pfc_assertion_status(P,_PP,Was):-
 (t_l:exact_assertions ; pfc_db_type(P,rule(_))),!,
  quietly(((clause_asserted_u(P)-> Was=identical; Was= unique))).
 
get_pfc_assertion_status(P,PP,Was):-
  quietly(((clause_asserted_u(P)-> Was=identical;
    (
      (((locally(set_prolog_flag(occurs_check,true),clause_u(PP)),cyclic_break((PPP)))-> (Was= partial(PPP));Was= unique)))))).


same_file_facts(S1,S2):-reduce_to_mfl(S1,MFL1),reduce_to_mfl(S2,MFL2),!,same_file_facts0(MFL1,MFL2).
same_file_facts0(mfl4(VarNameZ,M,F,_),mfl4(VarNameZ,M,FF,_)):-nonvar(M),!, FF=@=F.
same_file_facts0(F,FF):- FF=@=F,!.

reduce_to_mfl(MFL,MFL):- MFL=mfl4(_VarNameZ,_,_,_),!.
reduce_to_mfl((MFL,_),MFLO):- !,reduce_to_mfl(MFL,MFLO).

%% pfc_post_update4(++AssertionStatus, +Ps, +S, ++SupportStatus) is det.
%
% Physically assert the Knowledge+Support Data based on statuses
%
pfc_post_update4(Was,P,S,What):-
  not_not_ignore_quietly_ex(( (get_pfc_is_tracing(P);get_pfc_is_tracing(S)),
  fix_mp(change(assert,post),P,M,PP),
  must_ex(S=(F,T)),wdmsg_pretty(call_pfc_post4:- (Was,post1=M:PP,fact=F,trig=T,What)))),
  fail.

pfc_post_update4(identical,_P,_S,exact):-!.
pfc_post_update4(unique,P,S,none):- !,
   must_det(pfc_add_support_fast(P,S)),
   must_det(assert_u_confirmed_was_missing(P)),
   must_det(pfc_trace_op(add,P,S)),
   must_ex(pfc_enqueue(P,S)),!.

pfc_post_update4(Identical,P,S,Exact):- !,
  ((Exact\==exact ->pfc_add_support_fast(P,S);true),
  (Identical==identical-> true ; 
           (assert_u_confirmed_was_missing(P),pfc_trace_op(add,P,S),pfc_enqueue(P,S)))),!.

pfc_post_update4(identical,P,S,none):-!,pfc_add_support_fast(P,S),
    pfc_enqueue(P,S).

pfc_post_update4(identical,P,S,simular(_)):- !,pfc_add_support_fast(P,S).

/*
pfc_post_update4(Was,P,S,What):-
  not_not_ignore_quietly_ex(( \+ (get_pfc_is_tracing(P);get_pfc_is_tracing(S)),
  fix_mp(change(assert,post),P,M,PP),
  must_ex(S=(F,T)),wdmsg_pretty(pfc_post_update4:- (Was,post1=M:PP,fact=F,trig=T,What)))),
  fail.
*/

pfc_post_update4(partial(_Other),P,S,none):-!,
  pfc_add_support_fast(P,S),
  assert_u_confirmed_was_missing(P),
  pfc_trace_op(add,P,S),
  pfc_enqueue(P,S).

pfc_post_update4(partial(_Other),P,S,exact):-!,
  assert_u_confirmed_was_missing(P),
  pfc_trace_op(add,P,S),
  pfc_enqueue(P,S).

pfc_post_update4(unique,P,S,exact):-!,
  assert_u_confirmed_was_missing(P),
  pfc_trace_op(add,P,S).


pfc_post_update4(partial(_),P,S,exact):- !,
  assert_u_confirmed_was_missing(P),
  pfc_trace_op(add,P,S).


pfc_post_update4(partial(_),P,S,simular(_)):- !,
  pfc_add_support_fast(P,S),
  ignore((pfc_unique_u(P),assert_u_confirmed_was_missing(P),pfc_trace_op(add,P,S))),
  pfc_enqueue(P,S).

pfc_post_update4(unique,P,S,simular(_)):-!,
  pfc_add_support_fast(P,S),
  assert_u_confirmed_was_missing(P),
  pfc_trace_op(add,P,S),
  pfc_enqueue(P,S).


pfc_post_update4(Was,P,S,What):-dmsg_pretty(pfc_post_update4(Was,P,S,What)),dtrace,fail.

pfc_post_update4(Was,P,S,What):-!,trace_or_throw_ex(pfc_post_update4(Was,P,S,What)).

/*
assert_u_confirmed_was_missing(P):- once((get_unnegated_functor(P,F,_),get_functor(P,FF,_))),
 F==FF,
 call_u(prologSingleValued(F)),!,
 \+ \+ must_ex((db_assert_sv(P))),
 \+ \+ sanity((clause_asserted_u(P))),!.
*/

% assert_u_confirmed_was_missing(P):- pfc_enqueue(onChange(P),'was_missing'), fail.

% assert_u_confirmed_was_missing(P):- term_attvars(P,L),L\==[],!,  \+ \+ must_ex(assert_to_mu(P)),!.

assert_u_confirmed_was_missing(P):-
 \+ \+ must_ex(assert_to_mu(P)),!,
  nop((sanity((( (\+ clause_asserted_u(P)) -> (rtrace(assert_to_mu(P)),break) ; true))))),!.

assert_u_confirmed_was_missing(P):-
 copy_term_vn(P,PP),
 must_ex(assert_u_no_dep(P)),!,dtrace,
(nonvar(PP) -> true ; must_ex((P=@=PP,clause_asserted_u(PP),P=@=PP))),!.

assert_to_mu(P):-
  (t_l:assert_to(Where) ->
   (Where = a -> asserta_mu(P); assertz_mu(P));
  assert_mu(P)).

assert_u_confirm_if_missing(P):-
 must_ex(clause_asserted_u(P)-> true ; assert_u_confirmed_was_missing(P)).

%% get_pfc_current_db(-Db) is semidet.
%
% PFC Current Database.
%
% (was nothing)
%
get_pfc_current_db(Db):-lookup_u(pfc_current_db(Db)),!.
get_pfc_current_db(true).

%%  pfc_ain_db_to_head(+P,-NewP) is semidet.
%
% takes a fact P or a conditioned fact
%  (P:-C) and adds the Db context.
%
pfc_ain_db_to_head(P,NewP):-
  lookup_u(pfc_current_db(Db)),
  (Db=true        -> NewP = P;
   P=(Head:-Body) -> NewP = (Head:- (Db,Body));
   otherwise      -> NewP = (P:- Db)).


%% pfc_unique_u(+P) is semidet.
%
% is true if there is no assertion P in the prolog db.
%
pfc_unique_u(P):- t_l:exact_assertions,!, \+ clause_asserted_u(P).
%pfc_unique_u((Head:-Tail)):- !, \+ clause_u(Head,Tail).
%pfc_unique_u(P):- !, \+ clause_u(P,true).
pfc_unique_u(P):- \+ clause_asserted_u(P).


%% get_fc_mode(+P,+S,-Mode) is semidet.
%
% return Mode to forward assertion P in the prolog db.
%

%get_fc_mode(_P,_S,direct):-!.
get_fc_mode(P,_S,Mode):- get_unnegated_mfa(P,M,F,A),pfc_prop(M,F,A,Mode),is_fwc_mode(Mode),!.
get_fc_mode(pfc_prop(_,_,_,_),_S,direct).
get_fc_mode(P,_S,direct):- compound(P),functor(P,_,1).
get_fc_mode(_P,_S,Mode):- get_fc_mode(Mode).

get_fc_mode(Mode):- t_l:mpred_fc_mode(Mode),!.
get_fc_mode(Mode):- lookup_m(pm(Mode)),!.
get_fc_mode(Mode):- !, Mode=direct.


:- thread_local(t_l:mpred_fc_mode/1).

%% with_fc_mode(+Mode,:Goal) is semidet.
%
% Temporariliy changes to forward chaining propagation mode while running the Goal
%
with_fc_mode(Mode,Goal):- locally_tl(mpred_fc_mode(Mode),((Goal))).

set_fc_mode(Mode):- asserta(t_l:mpred_fc_mode(Mode)).

%% pfc_enqueue(+P,+S) is det.
%
% PFC Enqueue P for forward chaining
%

pfc_enqueue(P):- pfc_enqueue(P,_S).

pfc_enqueue(P,_):- show_pfc_success(que,lookup_m(que(P,_))),!.
%pfc_enqueue(P,_):- nb_current('$current_why',wp(_,P)),!,trace_or_throw_ex(why(P)).
%pfc_enqueue(P,_):- t_l:busy(P),!,nop(dmsg_pretty(t_l:busy(P))).
%pfc_enqueue(P,S):- locally_each(t_l:busy(P),pfc_enqueue2(P,S)).
pfc_enqueue(P,S):-
 (var(S)->current_why(S);true),
 (must_ex(get_fc_mode(P,S,Mode)) 
  -> pfc_enqueue_w_mode(S,Mode,P)
   ; pfcError("No pm mode")).

pfc_enqueue_w_mode(S,Mode,P):-
       (Mode=direct  -> pfc_enqueue_direct(S,P) ;
        Mode=thread  -> pfc_enqueue_thread(S,P) ;
	Mode=depth   -> pfc_asserta_w_support(que(P,S),S) ;
        Mode=paused  -> pfc_asserta_w_support(que(P,S),S) ;
	Mode=breadth -> pfc_assertz_w_support(que(P,S),S) ;
        Mode=next   -> pfc_asserta_w_support(que(P,S),S) ;
        Mode=last -> pfc_assertz_w_support(que(P,S),S) ;
	true     -> pfcError("Unrecognized pm mode: ~p", Mode)).

is_fwc_mode(direct).
is_fwc_mode(thread).
is_fwc_mode(depth).
is_fwc_mode(paused).
is_fwc_mode(breadth).
is_fwc_mode(next).
is_fwc_mode(last).


get_support_module(mfl4(_,Module,_,_), Module).
get_support_module((S1,S2),Module):- !, (get_support_module(S1,Module);get_support_module(S2,Module)).
get_support_module((S2:S1),Module):- !, (get_support_module(S1,Module);get_support_module(S2,Module)).

of_queue_module(_, M:_, M):- atom(M), !.
of_queue_module(S, _, Module):- get_support_module(S, Module), !.
of_queue_module(_, _, Module):- get_query_from(Module), !.

pfc_enqueue_direct(S,P):-
  of_queue_module(S,P,Module),
  loop_check_term(Module:mpred_fwc(P),pfc_enqueueing(P),true).

/*
pfc_enqueue_thread(S,P):- 
      with_only_current_why(S,
        call_in_thread(
           with_fc_mode(direct, % maybe keep `thread` mode?
               loop_check_term(mpred_fwc(P),pfc_enqueueing(P),true)))).

*/

pfc_enqueue_thread(S,P):- 
      with_only_current_why(S,
        call_in_thread(fwc_wlc(P))).

fwc_wlc(P):- in_fc_call(loop_check_term(mpred_fwc(P),pfc_enqueueing(P),true)).

% maybe keep `thread` mode?
% in_fc_call(Goal):- with_fc_mode( thread, Goal).
in_fc_call(Goal):- with_fc_mode( direct, Goal).
% in_fc_call(Goal):- !, call(Goal).

%% pfcRemoveOldVersion( :TermIdentifier) is semidet.
%
% if there is a rule of the form Identifier ::: Rule then delete it.
%
pfcRemoveOldVersion((Identifier::::Body)):-
  % this should never happen.
  var(Identifier),
  !,
  pfcWarn("variable used as an  rule name in ~p :::: ~p",
          [Identifier,Body]).


pfcRemoveOldVersion((Identifier::::Body)):-
  nonvar(Identifier),
  clause_u((Identifier::::OldBody),_),
  \+(Body=OldBody),
  pfcWithdraw((Identifier::::OldBody)),
  !.
pfcRemoveOldVersion(_).



% pfc_run compute the deductive closure of the current database.
% How this is done depends on the propagation mode:
%    direct -  mpred_fwc has already done the job.
%    depth or breadth - use the queue mechanism.
                                                            
pfc_run :- get_fc_mode(Mode)->Mode=paused,!.
% pfc_run :- repeat, \+ pfc_step, !.
pfc_run:-
  pfc_step,
  pfc_run.
pfc_run:- retractall(t_l:busy(_)).


% pfc_step removes one entry from the queue and reasons from it.

:-thread_local(t_l:busy/1).
:-thread_local(t_l:busy_s/1).

pfc_step:-
  % if hs/1 is true, reset it and fail, thereby stopping inferencing. (hs=halt_signal)
  quietly_ex((lookup_m(hs(Was)))),
  pfc_retract_i(hs(Was)),
  pfc_trace_msg('Stopping on: ~p',[hs(Was)]),
  !,
  fail.

pfc_step:-
  % draw immediate conclusions from the next fact to be considered.
  % fails iff the queue is empty.
  get_next_fact(P),
  %asserta(t_l:busy(P)),
  ignore(mpred_fwc(P)),
 % ignore(retract(t_l:local_current_why(_,P))),
  %retractall(t_l:busy(P)),
  !.

get_next_fact(P):-
  %identifies the nect fact to mpred_fwc from and removes it from the queue.
  select_next_fact(P),
  remove_selection(P).

remove_selection(P):-
  lookup_u(que(P,_),Ref),
  erase(Ref),
  % must_ex(pfc_retract_i(que(P,_))),
  pfc_remove_supports_quietly(que(P,_)),
  !.
remove_selection(P):-
  brake(format("~Npfc_:get_next_fact - selected fact not on Queue: ~p",
               [P])).


% select_next_fact(P) identifies the next fact to reason from.
% It tries the user defined predicate first and, failing that,
%  the default mechanism.
:- dynamic(baseKB:pfc_select_hook/1).
select_next_fact(P):-  
  lookup_u(baseKB:pfc_select_hook(P)),
  !.
select_next_fact(P):-
  defaultpfc_select(P),
  !.

% the default selection predicate takes the item at the froint of the queue.
defaultpfc_select(P):- lookup_m(que(P,_)),!.

% pfc_halt stops the forward chaining.
pfc_halt:-  pfc_halt(anonymous(pfc_halt)).

pfc_halt(Format,Args):- format_to_message(Format,Args,Info), pfc_halt(Info).

pfc_halt(Now):-
  pfc_trace_msg("New halt signal ",[Now]),
  (lookup_m(hs(Was)) ->
       pfcWarn("pfc_halt finds halt signal already set to: ~p ",[Was])
     ; assert_u_no_dep(hs(Now))).


% stop_trace(Info):- quietly_ex((tracing,leash(+all),dtrace(dmsg_pretty(Info)))),!,rtrace.
stop_trace(Info):- dtrace(dmsg_pretty(Info)).

%% pfc_ain_trigger_reprop(+Trigger,+Support) is nondet.
%
%  Assert New Trigger and Propigate
%
pfc_ain_trigger_reprop(PT,Support):- PT = pt(Trigger,Body), !,
   pfc_trace_msg('~N~n\tAdding positive~n\t\ttrigger: ~p~n\t\tbody: ~p~n\t Support: ~p~n',[Trigger,Body,Support]),!,
   sanity(\+ string(Support)),sanity(\+ string(Trigger)),sanity(\+ string(Body)),
   must(pfc_mark_as(Support,Trigger,pfcPosTrigger)),
 must(((  
  %  (debugging(logicmoo(_))->dtrace;true),
  
  pfc_assert_w_support(PT,Support),
  copy_term(PT,Tcopy),!,
  forall(call_u_no_bc(Trigger), 
   forall(pfc_eval_lhs(Body,(Trigger,Tcopy)),true))))),!.
  


pfc_ain_trigger_reprop(nt(Trigger,Test,Body),Support):- NT = nt(TriggerCopy,Test,Body),!,
  copy_term_vn(Trigger,TriggerCopy),  
  pfc_mark_as(Support,Trigger,pfcNegTrigger),
  pfc_trace_msg('~N~n\tAdding negative~n\t\ttrigger: ~p~n\t\ttest: ~p~n\t\tbody: ~p~n\t Support: ~p~n',[Trigger,Test,Body,Support]),
  pfc_assert_w_support(NT,Support),
  %stop_trace(pfc_assert_w_support(NT,Support)),
  !,
  ignore((\+ call_u_no_bc(Test),
  pfc_eval_lhs(Body,((\+Trigger),NT)))).

pfc_ain_trigger_reprop(BT,Support):- BT = bt(Trigger,Body),!,

  % UNEEDED Due to a trigger that creates it?
  % get_bc_clause(Trigger,Post),pfc_post1(Post),
  pfc_mark_as(Support,Trigger,pfcBcTrigger),
  % UNEEDED Due to a trigger that does it?
  % if_defined(kb_shared(Trigger),true),
  pfc_trace_msg('~N~n\tAdding backwards~n\t\ttrigger: ~p~n\t\tbody: ~p~n\t Support: ~p~n',[Trigger,Body,Support]),
  pfc_assert_w_support(BT,Support),
  !,
  pfc_bt_pt_combine(Trigger,Body,Support).

pfc_ain_trigger_reprop(X,Support):-
  pfcWarn("Unrecognized trigger to pfc_ain_trigger_reprop: ~p\n~~p~n",[X,Support]).


pfc_bt_pt_combine(Head,Body,Support):-
  %  a backward trigger (bt) was just added with head and Body and support Support
  %  find any pt''s with unifying heads and add the instantied bt body.
  lookup_u(pt(Head,Body)),
  pfc_eval_lhs(Body,Support),
  fail.
pfc_bt_pt_combine(_,_,_):- !.



%
%  predicates for manipulating action traces.
%   (Undoes side-effects)
%

pfc_ain_actiontrace(Action,Support):-
  % adds an action trace and it''s support.
  pfc_add_support(pfcAction(Action),Support).

fcUndo_action(pfcAction(Did)):-
  (clause_asserted_u(do_and_undo(Did,Undo))->true;lookup_u(do_and_undo(Did,Undo))),
  call_u_no_bc(Undo),
  !.

%%  pfc_prolog_retractall(X) is nondet.
pfc_prolog_retractall(X):-
 get_assertion_head_unnegated(X,P),
 pfc_prolog_retract(P),fail.
pfc_prolog_retractall(_).

%%  pfc_prolog_retract(X) is nondet.
pfc_prolog_retract(X):-
  %  retract an arbitrary thing.
  pfc_db_type(X,Type),!,
  pfc_retract_type(Type,X).
  


%%  pfc_retract_i(X) is det.
%
%  predicates to remove Pfc facts, triggers, action traces, and queue items
%  from the database.
%
pfc_retract_i(X):-
  %  retract an arbitrary thing.
  pfc_db_type(X,Type),!,
  pfc_retract_type(Type,X),
  !.

pfc_retract_type(fact(_FT),X):-
  %  db pfc_ain_db_to_head(X,X2), retract_u(X2).
  % stop_trace(pfc_retract_type(fact(FT),X)),
  (retract_u(X)
   *-> pfc_unfwc(X) ; (pfc_unfwc(X),!,fail)).

pfc_retract_type(rule(_RT),X):-
  %  db  pfc_ain_db_to_head(X,X2),  retract_u(X2).
  (retract_u(X)
      *-> pfc_unfwc(X) ; (pfc_unfwc(X),!,fail)).

pfc_retract_type(trigger(_TT),X):-
  retract_u(X)
    -> pfc_unfwc(X)
     ; pfcWarn("Trigger not found to retract_u: ~p",[X]).

pfc_retract_type(action,X):- fcUndo_action(X).


%%  pfc_ain_object(X)
%
% adds item P to some database
%
pfc_ain_object(X):-
  % what type of P do we have?
  pfc_db_type(X,Type),
  % call the appropriate predicate.
  pfc_ain_by_type(Type,X).

pfc_ain_by_type(fact(_FT),X):-
  pfc_unique_u(X),
  assert_u_confirmed_was_missing(X),!.
pfc_ain_by_type(rule(_RT),X):-
  pfc_unique_u(X),
  assert_u_confirmed_was_missing(X),!.
pfc_ain_by_type(trigger(_TT),X):-
  assert_u_confirmed_was_missing(X).
pfc_ain_by_type(action,_ZAction):- !.



%% pfcWithdraw(P,S) removes support S from P and checks to see if P is still supported.
%% If it is not, then the fact is retreactred from the database and any support
%% relationships it participated in removed.

pfcWithdraw(P):- pfc_reduced_chain(pfcWithdraw,P),!.

pfcWithdraw(mfl4(_VarNameZ,_,_,_)):-!.
pfcWithdraw(P) :- 
  only_is_user_reason(UU),
  % iterate down the list of facts to be pfcWithdraw''ed.
  (is_list(P)->
  pfcWithdraw_list(P,UU);
    % pfcWithdraw/1 is the user's interface - it withdraws user support for P.
  pfcWithdraw(P,UU)).
  
  
pfcWithdraw_list(P) :- 
  only_is_user_reason(UU),
  pfcWithdraw_list(P,UU).

pfcWithdraw_list([H|T],UU) :-
  % pfcWithdraw each element in the list.
  pfcWithdraw(H,UU),
  pfcWithdraw_list(T,UU).

maybe_user_support(P,S,SS):- 
  (pfc_get_support(P,S) ->
  (frozen(S,Goals),
  (Goals == true  -> SS=S ; SS = freeze(S,Goals))); SS = unKnown_suppoRt).

pfcWithdraw(P,S) :-
  maybe_user_support(P,S,SS),
  (SS \== unKnown_suppoRt ->
  % pfcDebug(format("~Nremoving support ~p from ~p",[SS,P])),
  (pfc_trace_msg('\n    Removing support: ~p~n',[SS]),
  pfc_trace_msg('     Which was for: ~p~n',[P])); 
    nop(dmsg_pretty(pfcWithdraw(P,S)))),
  ignore(pfcWithdraw_fail_if_supported(P,S)).

pfcWithdraw_fail_if_supported(mfl4(_VarNameZ,_,_,_),_):-!.
pfcWithdraw_fail_if_supported(P,S):-
  maybe_user_support(P,S,SS),
  (((lookup_spft(P,F,T), S= (F,T), pfc_rem_support(P,S), nop(dmsg_pretty(found(pfc_rem_support1(P,S)))))
     -> (remove_if_unsupported(P),retractall(t_l:busy(_)))
      ; ((pfcWithdraw_fail_if_supported_maybe_warn(SS,P),
            \+ show_still_supported(P))))).

pfcWithdraw_fail_if_supported_maybe_warn(_,P):- P== singleValuedInArg(arity, 2).
pfcWithdraw_fail_if_supported_maybe_warn(_,P):- P= prologSingleValued(_Arity).
% pfcWithdraw_fail_if_supported_maybe_warn(_,~P):- nonvar(P),!.
pfcWithdraw_fail_if_supported_maybe_warn(unKnown_suppoRt,P):- 
  maybe_user_support(P,S,SS),
        (((lookup_spft(P,F,T), S= (F,T), call(pfc_rem_support(P,S)),
           nop(dmsg_pretty(found(pfc_rem_support2(P,S)))))
           -> (remove_if_unsupported(P),retractall(t_l:busy(_)))
            ; (( nop(pfcWithdraw_fail_if_supported_maybe_warn(SS,P)),
                  \+ show_still_supported(P))))).
pfcWithdraw_fail_if_supported_maybe_warn(S,P):- 
  pfc_get_support(P,S),SS=S,
        (((lookup_spft(P,F,T), S= (F,T), pfc_rem_support(P,S),dmsg_pretty(found(pfc_rem_support3(P,S))))
           -> (remove_if_unsupported(P),retractall(t_l:busy(_)))
            ; (( nop(pfcWithdraw_fail_if_supported_maybe_warn(SS,P)),
                  \+ show_still_supported(P))))).
pfcWithdraw_fail_if_supported_maybe_warn(SS,P):-
  pfc_trace_msg("pfcWithdraw/2 Could not find support ~p to remove (fact): ~p",[SS,P]).

show_still_supported(P):-  ((pfc_supported(P),pfc_trace_msg('~p',[still_supported(P)]))).


%% pfc_remove(P) is det.
%% pfc_remove2(P) is det.
%% pfc_remove2(P,S) is det.
%
% pfc_remove2 is like pfcWithdraw, but if P is still in the DB after removing the
% user's support, it is retracted by more forceful means (e.g. pfc_blast).
%
pfc_remove(P):- pfcWithdraw(P), (pfc_supported(P) -> pfc_blast(P); true).

pfc_remove2(P):- pfc_reduced_chain(pfc_remove2,P),!.

pfc_remove2(P) :-  only_is_user_reason(UU),
  % pfc_remove2/1 is the user's interface - it withdraws user support for P.
  pfc_remove2(P,UU).

pfc_remove2(P,S) :-
  pfcWithdraw(P,S),
  (call_u(P)
     -> ( pfc_blast(P) )
      ; true).

pfc_retract_is_complete(mfl4(_VarNameZ,_,_,_)):-!.
pfc_retract_is_complete(P) :- \+ pfc_supported(local,P), \+ call_u(P).

pfc_retract(P):- pfcWithdraw(P), pfc_retract_is_complete(P),!,pfc_trace_msg('    Withdrew: ~p',[P]).
pfc_retract(P):- pfc_retract_preconds(P), pfc_retract_is_complete(P),!,pfc_trace_msg('    Retracted: ~p~n',[P]).
pfc_retract(P):- listing(P),pfcWhy_1(P),show_call(pfc_blast(P)),pfc_retract_is_complete(P),!,pfc_trace_msg('    Blasted: ~p~n',[P]).
pfc_retract(P):- ok_left_over(P),pfc_trace_msg('    Still True (ok_left_over): ~p~n',[P]),!,ignore((with_no_retry_undefined((pfcWhy_1(P),listing(P))))).
pfc_retract(P):- listing(P),pfcWhy_1(P),!,with_no_retry_undefined(P),pfcWarn('    Still True: ~p~n',[P]),
  log_failure_red,sleep(2),!,ok_left_over(P).
  

ok_left_over(P):- strip_module(P,M,H),ok_left_over(M,H).
ok_left_over(_,arity(_,_)).

pfc_retract_preconds(P):- pfc_retract_1preconds(P).

pfc_retract_1preconds(P):- 
  supporters_list0(P,WhyS),
  member(S,WhyS),
  pfc_db_type(S,fact(_)),
  pfc_children(S,Childs),
  Childs=[C],C=@=P,
  pfc_trace_msg('    Removing support1: ~p~n',[S]),
  pfc_trace_msg('       Which was for: ~p~n',[P]),
  show_call(pfc_retract(S)).  

pfc_retract_1preconds(P):- 
  supporters_list0(P,WhyS),
  member(S,WhyS),
  pfc_db_type(S,fact(_)),
  pfc_children(S,Childs),
  pfc_trace_msg('    Removing support2: ~p~n',[S]),
  pfc_trace_msg(' Childs: ~p~n',[Childs]),
  show_call(pfc_retract(S)).



pfc_retract1(P):- 
  supporters_list0(P,WhyS),
  must_maplist(pfc_retract_if_fact,WhyS).


pfc_retract_if_fact(P):-  pfc_db_type(P,fact(_)),!, pfc_retract1(P).
pfc_retract_if_fact(_).

%
%  pfc_blast(+F) retracts fact F from the DB and removes any dependent facts
%

pfc_blast(F) :- 
  pfcRemoveSupports(F),
  fcUndo(F).

pfc_retract_all(P):- 
  repeat, \+ pfc_retract(P).

% removes any remaining supports for fact F, complaining as it goes.

pfcRemoveSupports(P) :- 
  lookup_spft(P,F,S),
  pfc_trace_msg("~p was still supported by ~p",[F,S]),
  %  pfc_retract_i_or_warn(spft(P,F,S)).
  fail.
pfcRemoveSupports(_).

pfc_remove_supports_quietly(F) :- 
  pfc_rem_support(F,_),
  fail.
pfc_remove_supports_quietly(_).


%% fcUndo(X) undoes X.
%
% - a positive or negative trigger.
% - an action by finding a method and successfully executing it.
% - or a random fact, printing out the trace, if relevant.
%

fcUndo(P):- pfc_reduced_chain(fcUndo,P),!.
fcUndo(X):- fcUndo1(X),!.


% maybe still un-forward chain?
fcUndo_unfwd(Fact):-
  % undo a random fact, printing out the dtrace, if relevant.
  (pfc_unfwc(Fact) *-> pfc_trace_msg(pfc_unfwc(Fact));pfc_trace_msg( \+ pfc_unfwc(Fact))).
% fcUndo(X):- doall(fcUndo1(X)).

fcUndo1((H:-B)):- reduce_clause(unpost,(H:-B),HB), HB\=@= (H:-B),!,fcUndo1((HB)).
fcUndo1(pfcAction(A)):-
  % undo an action by finding a method and successfully executing it.
  !,
  show_call(fcUndo_action(pfcAction(A))).

fcUndo1(pt(Key,Head,Body)):-
  % undo a positive trigger 3.
  %
  !,
  (show_pfc_success(fcUndo1_pt_unfwc_3,retract_u(pt(Key,Head,Body)))
    -> pfc_unfwc(pt(Head,Body))
     ; pfcWarn("Trigger not found to undo: ~p",[pt(Head,Body)])).

fcUndo1(pt(Head,Body)):- 
  % undo a positive trigger.
  %
  !,
  (show_pfc_success(fcUndo1_pt_unfwc_2,retract_u(pt(Head,Body)))
    -> pfc_unfwc(pt(Head,Body))
     ; pfcWarn("Trigger not found to undo: ~p",[pt(Head,Body)])).

fcUndo1(nt(Head,Condition,Body)):-
  % undo a negative trigger.
  !,
  (
   show_pfc_success(fcUndo1_nt_unfwc,(nt(Head,Condition,Body),
       dmsg_pretty(fcUndo1(nt(Head,Condition,Body))),retract_u(nt(Head,Condition,Body))))
    -> (pfc_unfwc(nt(Head,Condition,Body))->true;show_call(assert_u(nt(Head,Condition,Body))))
     ; pfc_trace_msg("WARNING?? Trigger not found to undo: ~p",[nt(Head,Condition,Body)])).

fcUndo1(P):- pfc_reduced_chain(fcUndo1,P),!.

fcUndo1(Fact):-
  % undo a random fact, printing out the dtrace, if relevant.
  (retract_u(Fact)*->true; pfc_trace_msg(show_failure(fcUndo1,retract_u(Fact)))),
  pfc_trace_op(rem,Fact),
  pfc_unfwc(Fact).



%%  pfc_unfwc(+P)
%
% "un-forward-chains" from fact P.  That is, fact P has just
%  been removed from the database, so remove all support relations it
%  participates in and check the things that they support to see if they
%  should stay in the database or should also be removed.
%

pfc_unfwc(P):- pfc_reduced_chain(pfc_unfwc,P),!.
pfc_unfwc(F):-
  show_failure(pfc_retract_supported_relations(F)),
  pfc_unfwc1(F).

pfc_unfwc1(F):-
  pfc_unfwc_check_triggers(F),
  % is this really the right place for pfc_run<?
  pfc_run,!.


pfc_unfwc_check_triggers(F):- 
 loop_check(pfc_unfwc_check_triggers0(F), 
    (pfcWarn(looped_pfc_unfwc_check_triggers0(F)), pfc_run)).

pfc_unfwc_check_triggers0(F):-
  pfc_db_type(F,_),
 doall(( copy_term_vn(F,Fcopy),
  lookup_u(nt(Fcopy,Condition,Action)),
  \+ call_u_no_bc(Condition),
  pfc_eval_lhs(Action,((\+F),nt(F,Condition,Action))))),
 !.


pfc_unfwc_check_triggers0(F):-
  pfc_db_type(F,FT),
  dmsg_pretty(unknown_rule_type(pfc_db_type(F,FT))),!.



pfc_retract_supported_relations(Fact):-
  pfc_db_type(Fact,Type),Type=trigger(_),
  pfc_rem_support_if_exists(P,(_,Fact)),
  must_ex(nonvar(P)),
  remove_if_unsupported(P),
  fail.

pfc_retract_supported_relations(Fact):-
  pfc_rem_support_if_exists(P,(Fact,_)),
  must_ex(nonvar(P)),
  remove_if_unsupported(P),
  fail.

pfc_retract_supported_relations(_).



%  remove_if_unsupported(+Ps) checks to see if all Ps are supported and removes
%  it from the DB if they are not.
remove_if_unsupported(P):-
  loop_check(remove_if_unsupported0(P),true).
remove_if_unsupported0(P):- \+ pfc_supported(P),!,doall((fcUndo(P))).
remove_if_unsupported0(P):- \+ is_single_valued(P),!,pfc_trace_msg('~p',[still_supported(P)]).
remove_if_unsupported0(P):- pfc_trace_msg('~p',[sv_still_supported(P)]), doall((fcUndo(P))).

is_single_valued(P):- get_unnegated_functor(P,F,_)->call_u(prologSingleValued(F)).



%%  mpred_fwc(+X) is det.
%
% forward chains from a fact or a list of facts X.
%
mpred_fwc(Ps):- each_E(mpred_fwc0,Ps,[]).
:- module_transparent((mpred_fwc0)/1).

%%  mpred_fwc0(+X) is det.
%
%  Avoid loop while calling mpred_fwc1(P)
%
% this line filters sequential (and secondary) dupes
 % mpred_fwc0(genls(_,_)):-!.
mpred_fwc0(Fact):- fail, quietly_ex(ground(Fact)),
   \+ t_l:is_repropagating(_),
   quietly_ex((once(((fwc1s_post1s(_One,Two),Six is Two * 1))))), 
   show_pfc_success(filter_buffer_n_test,(filter_buffer_n_test('$last_mpred_fwc1s',Six,Fact))),!.
mpred_fwc0(Fact):- quietly_ex(copy_term_vn(Fact,FactC)),
      loop_check(mpred_fwc1(FactC),true).


filter_buffer_trim(Name,N):- quietly_ex((
  filter_buffer_get_n(Name,List,N),
  nb_setval(Name,List))).

filter_buffer_get_n(Name,FactS,N):-
  nb_current(Name,Fact1s),
  length(Fact1s,PFs),!,
  ((PFs =< N)
    -> FactS=Fact1s;
   (length(FactS,N),append(FactS,_,Fact1s))).
filter_buffer_get_n(_,[],_).


% filter_buffer_n_test(_Name,_,_Fact):- \+ need_speed, !,fail.
filter_buffer_n_test(Name,N,Fact):- filter_buffer_get_n(Name,FactS,N),
   (memberchk(Fact,FactS)-> true ; (nb_setval(Name,[Fact|FactS]),fail)).

:- meta_predicate(pfc_reduced_chain(1,*)).
:- meta_predicate(pfc_reduced_chain(*,*)).
pfc_reduced_chain(P1,(Fact:- (FWC, BODY))):- FWC==fwc,!,call(P1,{BODY}==>Fact).
pfc_reduced_chain(P1,(Fact:- (BWC, BODY))):- BWC==bwc,!,call(P1,(Fact<-BODY)).
pfc_reduced_chain(P1,(P:-AB)):- compound(AB),AB=attr_bind(L,R),!,must_ex(attr_bind(L)),call(P1,(P:-R)).
pfc_reduced_chain(P1,(P:-True)):- True==true,call(P1,P).

pfc_reduced_chain(P1,==>(Fact),P1):- sanity(nonvar(Fact)),!,
  must_ex(full_transform(mpred_fwc1,==>(Fact),ExpandFact)),!,  
  pfc_trace_msg((expanding_pfc_chain(P1,Fact) ==> ExpandFact)),
  sanity(ExpandFact\== (==>(Fact))),
  each_E(P1,ExpandFact,[]).


%% mpred_fwc1(+P) is det.
%
% forward chains for a single fact.
%  Avoids loop while calling mpred_fwc1(P)
mpred_fwc1(clause_asserted_u(Fact)):-!,sanity(clause_asserted_u(Fact)).
mpred_fwc1(P):- pfc_reduced_chain(mpred_fwc1,P),!.
mpred_fwc1(support_hilog(_,_)):-!.
mpred_fwc1(pfc_unload_option(_,_)):-!.

% mpred_fwc1(singleValuedInArg(_, _)):-!.
% this line filters sequential (and secondary) dupes
% mpred_fwc1(Fact):- current_prolog_flag(unsafe_speedups , true) , ground(Fact),fwc1s_post1s(_One,Two),Six is Two * 3,filter_buffer_n_test('$last_mpred_fwc1s',Six,Fact),!.
mpred_fwc1(Prop):-'$current_source_module'(Sm),pfc_m_fwc1(Sm,Prop).


:-thread_local(t_l:busy_f/1).
:-thread_local(t_l:busy_s/1).

pfc_m_fwc1(Sm,Prop):- fixed_syntax(Prop,After),!,must(Prop\=@=After),pfc_m_fwc1(Sm,After).
pfc_m_fwc1(Sm,Prop):- clause_asserted(t_l:busy_s(Prop)),dmsg_pretty(Sm:warn(busy_pfc_m_fwc1(Prop))),!.
pfc_m_fwc1(Sm,Prop):- clause_asserted(t_l:busy_f(Prop)),dmsg_pretty(Sm:warn(busy_pfc_m_fwc1_f(Prop))),!.
pfc_m_fwc1(Sm,Prop):- % clause_asserted(t_l:busy_f(Prop)),!,
   setup_call_cleanup(
     asserta(t_l:busy_s(Prop),R),
     ignore(pfc_m_fwc2(Sm,Prop)),
     ignore(catch(erase(R),_,fail))).
% pfc_m_fwc1(Sm,Prop):- pfc_m_fwc2(Sm,Prop).

pfc_m_fwc2(Sm,Prop):-   
  pfc_trace_msg(Sm:mpred_fwc1(Prop)),
  %ignore((pfc_non_neg_literal(Prop),remove_negative_version(Prop))),
  \+ \+ ignore(pfc_do_rule(Prop)),
  setup_call_cleanup(
    asserta(t_l:busy_f(Prop),R),
    ignore(pfc_do_fact(Prop)),
    ignore(catch(erase(R),_,fail))).



%% pfc_do_rule(P) is det.
% does some special, built in forward chaining if P is
%  a rule.

pfc_do_rule((P==>Q)):-
  !,
  processRule(P,Q,(P==>Q)).
pfc_do_rule((Name::::P==>Q)):-
  !,
  processRule(P,Q,(Name::::P==>Q)).
pfc_do_rule((P<==>Q)):-
  !,
  processRule(P,Q,(P<==>Q)),
  processRule(Q,P,(P<==>Q)).
pfc_do_rule((Name::::P<==>Q)):-
  !,
  processRule(P,Q,((Name::::P<==>Q))),
  processRule(Q,P,((Name::::P<==>Q))).

pfc_do_rule(('<-'(P,Q))):-
  !,
  pfcDefineBcRule(P,Q,('<-'(P,Q))).

pfc_do_rule(('<=='(P,Q))):-
  !,
  pfcDefineBcRule(P,Q,('<-'(P,Q))).

pfc_do_rule((H:-B)):- fail, 
  !,
  pfc_do_hb_catchup(H,B).


is_head_LHS(H):- nonvar(H),get_functor(H,F,A),must_ex(suggest_m(M)),lookup_u(pfc_prop(M,F,A,pfcLHS)).
body_clause(SK,Cont):-nonvar(SK),SK=Cont.

pfc_do_hb_catchup(H, _B):- \+ is_head_LHS(H),!.
pfc_do_hb_catchup(_H, B):- \+ \+ (B=true),!.
pfc_do_hb_catchup(_H, B):- compound(B), \+ \+ reserved_body_helper(B),!. 

% prolog_clause pfc_do_rule VAR_H
pfc_do_hb_catchup(H,B):- sanity(nonvar(B)),
  var(H),!,dmsg_pretty(warn(is_VAR_H((H:-B)))),
  trace,   % THe body needs to sanify (bind) the Head
  forall(call_u(B),
     (sanity(nonvar(H)),pfc_ain(H))),!.

pfc_do_hb_catchup(H,Body):- is_head_LHS(H),
   body_clause(Body,attr_bind(AG,B)),
% Should we repropagate(H) ?
   attr_bind(AG),!,
   pfc_do_hb_catchup_now(H,B).


% prolog_clause pfc_do_rule pfcLHS
pfc_do_hb_catchup(H,B):- %is_head_LHS(H),  
% Should we repropagate(H) if body failed?
   pfc_do_hb_catchup_now(H,B).
                     
% pfc_do_hb_catchup(H,B):- !,pfc_do_hb_catchup_now(H,B).

% pfc_do_hb_catchup_now_maybe(_,_):-!.
pfc_do_hb_catchup_now_maybe(H,B):- B\=(cwc,_),
  pfc_do_hb_catchup_now(H,B).

% pfc_do_hb_catchup_now(_,_):-!.
pfc_do_hb_catchup_now(H,B):- B\=(cwc,_),nonvar(B),
  with_exact_assertions(catch( (forall(call_u(B),mpred_fwc(H));true),_,true)),!.


% prolog_clause pfc_do_clause COMMENTED
% pfc_do_clause(Fact,H,B):- nonvar(H),pfc_do_fact({clause(H,B)}),fail.

% prolog_clause pfc_do_clause (_ :- _)

pfc_do_clause(H,B):-
 with_exact_assertions(pfc_do_clause0(H,B)).

pfc_do_clause0(Var, B):- is_ftVar(Var),!,trace_or_throw(var_pfc_do_clause0(Var, B)).
pfc_do_clause0((=>(_,_)),_):-!.
pfc_do_clause0((==>(_,_)),_):-!.
pfc_do_clause0(H,B):-
  % Fact = {clause(H,B)},
  Fact = (H :- B),  B\=(cwc,_),!,
  copy_term(Fact,Copy),
  % check positive triggers
  loop_check(pfc_do_fcpt(Copy,Fact),true), % dmsg_pretty(trace_or_throw_ex(pfc_do_clause(Copy)))),
  % check negative triggers
  pfc_do_fcnt(Copy,Fact),
  pfc_do_hb_catchup(H,B).

:- dynamic(baseKB:todo_later/1).
is_cutted(Cutted):- contains_var(!,Cutted).
do_later(pfc_do_clause(_,Cutted)):- is_cutted(Cutted),!.
do_later(pfc_do_clause(~_H,_B)):- !.
do_later(G):- assertz(baseKB:todo_later(G)),nop(dmsg(do_later(G))).

% prolog_clause pfc_do_fact (_ :- _)
pfc_do_fact(Fact):-
  Fact = (_:-_), 
  copy_term_vn(Fact,(H:-B)),
  B\=(cwc,_),!,
  do_later(pfc_do_clause(H,B)),!.

pfc_do_fact(Fact):-
  copy_term_vn(Fact,Copy),
  % check positive triggers
  loop_check(pfc_do_fcpt(Copy,Fact),true), % dmsg_pretty(trace_or_throw_ex(pfc_do_rule(Copy)))),
  % check negative triggers
  pfc_do_fcnt(Copy,Fact),
  nop(pfc_do_clause(Fact,true)).


get_tms_mode(_P,Mode):- lookup_m(tms(ModeO)),!,ModeO=Mode.
get_tms_mode(_P,Mode):- Mode=local.


% do all positive triggers
pfc_do_fcpt(pfc_prop(swish_help, index_json, 2, kb_shared),_):- dumpST, break.
pfc_do_fcpt(Copy,Trigger):-
  forall((call_u(pt(Trigger,Body)),
  pfc_trace_msg('~N~n\tFound positive trigger: ~p~n\t\tbody: ~p~n',
		[Trigger,Body])),
    forall(pfc_eval_lhs_no_nc(Body,(Copy,pt(Trigger,Body))),
     true)),!.
  
%pfc_do_fcpt(Trigger,F):-
%  lookup_u(pt(presently(F),Body)),
%  pfc_e val_lhs(Body,(presently(Fact),pt(presently(F),Body))),
%  fail.
% pfc_do_fcpt(_,_).

% do all negative triggers
pfc_do_fcnt(_ZFact,Trigger):-
  NT = nt(Trigger,Condition,Body),
  (call_u(NT)*-> lookup_spft(X,F1,NT) ; lookup_spft(X,F1,NT)),
  %clause(SPFT,true),
  pfc_trace_msg('~N~n\tFound negative trigger: ~p~n\t\tcond: ~p~n\t\tbody: ~p~n\tSupport: ~p~n',
                 [Trigger,Condition,Body,spft(X,F1,NT)]),  
  call_u_no_bc(Condition),
  pfcWithdraw(X,(F2,NT)),
  sanity(F1=F2),
  fail.
pfc_do_fcnt(_,_).


%% pfcDefineBcRule(+Head,+Body,+Parent_rule)
%
% defines a backward chaining rule and adds the
% corresponding bt triggers to the database.
%
pfcDefineBcRule(Head,_ZBody,Parent_rule):-
  (\+ pfcLiteral_nonvar(Head)),
  pfcWarn("Malformed backward chaining rule.  ~p not atomic.",[Head]),
  pfcError("caused by rule: ~p",[Parent_rule]),
  !,
  fail.

pfcDefineBcRule(Head,Body,Parent_rule):-
  must_notrace_pfc(get_source_mfl(U)),!,
  copy_term(Parent_rule,Parent_ruleCopy),
  buildrhs(U,Head,Rhs),
  % kb_local(Head),
  % UNEEDED Due to a trigger that creates it?
  % get_bc_clause(Head,Post),ain(Post),
  foreach(pfc_nf(Body,Lhs),
          ignore((buildTrigger(Parent_ruleCopy,Lhs,rhs(Rhs),Trigger),
           ain_fast(bt(Head,Trigger),(Parent_ruleCopy,U))))).
   
get_bc_clause(Head,(HeadC:- BodyC)):- get_bc_clause(Head,HeadC,BodyC).

get_bc_clause(HeadIn, ~HeadC, Body):- compound(HeadIn), HeadIn = ~Head,!,
     Body = ( awc, 
            ( nonvar(HeadC)-> (HeadC = Head,!) ; (HeadC = Head)), 
              pfc_bc_and_with_pfc(~Head)).
get_bc_clause(Head, Head, Body):-  % % :- is_ftNonvar(Head).
     Body = ( awc, !, pfc_bc_and_with_pfc(Head)).

:- thread_initialization(nb_setval('$pfc_current_choice',[])).

push_current_choice:- current_prolog_flag(pfc_support_cut,false),!.
push_current_choice:- prolog_current_choice(CP),push_current_choice(CP),!.
push_current_choice(CP):- nb_current('$pfc_current_choice',Was)->b_setval('$pfc_current_choice',[CP|Was]);b_setval('$pfc_current_choice',[CP]).

cut_c:- current_prolog_flag(pfc_support_cut,false),!.
cut_c:- must_ex(nb_current('$pfc_current_choice',[CP|_WAS])),prolog_cut_to(CP).

%% pfc_eval_lhs(X,Support) is nondet.
%
%  eval something on the LHS of a rule.
%


pfc_eval_lhs(X,S):-
   push_current_choice,
   Loop = _,
   with_current_why(S,
     loop_check(pfc_eval_lhs_0(X,S),Loop=true)),
   (nonvar(Loop)-> (fail,dumpST,break) ; true).

pfc_eval_lhs_no_nc(X,S):- pfc_eval_lhs_0(X,S).


%% pfc_eval_lhs_0(X,Support) is det.
%
%  Helper of evaling something on the LHS of a rule.
%
pfc_eval_lhs_0(rhs(X),Support):- !, pfc_eval_rhs(X,Support).
pfc_eval_lhs_0(X,Support):- fcEvalLHS(X,Support).


%% fcEvalLHS(X,Support) is det.
%
%  Helper Secondary of evaling something on the LHS of a rule.
%
fcEvalLHS(Var,Support):- var(Var),!,trace_or_throw_ex(var_pfc_eval_lhs_0(Var,Support)).
fcEvalLHS((Test *-> Body),Support):-  % Noncutted *->
  !,
  (call_u_no_bc(Test) *-> pfc_eval_lhs_0(Body,Support)).

fcEvalLHS((Test -> Body),Support):- !,  % cutted ->
  call_u_no_bc(Test) -> pfc_eval_lhs_0(Body,Support).


%fcEvalLHS(snip(X),Support):-
%  snip(Support),
%  fcEvalLHS(X,Support).

fcEvalLHS(X,Support):- pfc_db_type(X,trigger(_TT)),!,must(pfc_ain_trigger_reprop(X,Support)),!.

fcEvalLHS(X,_):- 
    pfcWarn("Unrecognized item found in trigger body, namely ~p.",[X]).


args_swapped(~P1,~P2):-!,args_swapped(P1,P2).
args_swapped(P1,P2):- P1  univ_safe  [F,Y,X], P2  univ_safe  [F,X,Y].
fxy_args_swapped(F,X,Y,P1,P2):- P1  univ_safe  [F,X,Y], P2  univ_safe  [F,Y,X].


%%  pfc_eval_rhs1(What,Support) is nondet.
%
%  eval something on the RHS of a rule.
%
pfc_eval_rhs([],_):- !.
pfc_eval_rhs([Head|Tail],Support):-
  pfc_eval_rhs1(Head,Support),
  pfc_eval_rhs(Tail,Support).

pfc_eval_rhs1(Action,Support):- is_ftVar(Action),throw(pfc_eval_rhs1(Action,Support)).
pfc_eval_rhs1([X|Xrest],Support):-
 % embedded sublist.
 !,
 pfc_eval_rhs([X|Xrest],Support).

pfc_eval_rhs1({Action},Support):-
 % evaluable Prolog code.
 !,
 fc_eval_action(Action,Support).

pfc_eval_rhs1( \+ ~P, _Support):-  nonvar(P), !, 
  %pfc_trace_msg('~N~n~n\t\tRHS-Withdrawing: ~p \n\tSupport: ~p~n',[~P,Support]),
   pfcWithdraw(~P).


% if negated litteral \+ P
pfc_eval_rhs1(\+ P,Support):- nonvar(P),
 % predicate to remove.
  \+ pfc_negated_literal( P),
  %TODO Shouldn''t we be pfcWithdrawing the Positive version?
  % perhaps we aready negated here dirrent nf1_*
  pfc_trace_msg('~N~n~n\t\tRHS-Withdrawing-Neg: ~p \n\tSupport: ~p~n',[P,Support]),
  !,
  pfcWithdraw(P).


% Dmiles replaced with this
pfc_eval_rhs1( P,Support):- 
 % predicate to remove.
  P\= ~(_),
  pfc_unnegate( P , PN),!,
  %TODO Shouldn''t we be pfcWithdrawing the Positive version?  (We are)
  % perhaps we aready negated here from pfc_nf1_negation?!
  pfc_trace_msg('~N~n~n\t\tNegation causes RHS-Withdrawing: ~p \n\tSupport: ~p~n',[P,Support]),
  !,
  pfcWithdraw(PN).


% if negated litteral \+ P
pfc_eval_rhs1( P,Support):-
 % predicate to remove.
  P \= ~(_),
  \+ \+ pfc_negated_literal( P),
  %TODO Shouldn''t we be pfcWithdrawing the Positive version?
  % perhaps we aready negated here dirrent nf1_*
  pfc_trace_msg('~N~n~n\t\tRHS-Withdrawing-pfc_negated_literal: ~p \n\tSupport: ~p~n',[P,Support]),
  !,
  pfcWithdraw(P).

pfc_eval_rhs1(Assertion,Support):- !,
 % an assertion to be added.
 pfc_trace_msg('~N~n~n\tRHS-Post1: ~p \n\tSupport: ~p~n',[Assertion,Support]),!,
 (quietly(pfc_post(Assertion,Support)) *->
    true;
    pfcWarn("\n\t\t\n\t\tMalformed rhs of a rule (pfc_post1 failed)\n\t\tPost1: ~p\n\t\tSupport=~p.",[Assertion,Support])).

% pfc_eval_rhs1(X,_):-  pfcWarn("Malformed rhs of a rule: ~p",[X]).


%% fc_eval_action(+Action,+Support)
%
%  evaluate an action found on the rhs of a rule.
%

fc_eval_action(CALL,Support):-
  pfc_METACALL(fc_eval_action_rev(Support),CALL).

fc_eval_action_rev(Support,Action):-
  (call_u_no_bc(Action)),
  (show_success(action_is_undoable(Action))
     -> pfc_ain_actiontrace(Action,Support)
      ; true).

/*
%
%
%

trigger_trigger(Trigger,Body,_ZSupport):-
 trigger_trigger1(Trigger,Body).
trigger_trigger(_,_,_).


%trigger_trigger1(presently(Trigger),Body):-
%  !,
%  copy_term_vn(Trigger,TriggerCopy),
%  call_u(Trigger),
%  pfc_eval_lhs(Body,(presently(Trigger),pt(presently(TriggerCopy),Body))),
%  fail.

trigger_trigger1(Trigger,Body):-
  copy_term_vn(Trigger,TriggerCopy),
  call_u(Trigger),
  pfc_eval_lhs(Body,(Trigger,pt(TriggerCopy,Body))),
  fail.
*/


call_m_g(To,_M,G):- To:call(G).
lookup_m_g(To,_M,G):- clause(To:G,true).

%%  call_u(F) is det.
%
%  is true iff F is a fact available *for* forward chaining
%  (or *from* the backchaining rules)
%  Note: a bug almost fixed is that this sometimes the side effect of catching
%  facts and not assigning the correct justifications
%
% call_u(P):- predicate_property(P,number_of_rules(N)),N=0,!,lookup_u(P).

% :- table(call_u/1).




call_u(functorDeclares(H)):-  get_var_or_functor(H,F),!,clause_b(functorDeclares(F)).
call_u(singleValuedInArg(H,A)):- get_var_or_functor(H,F),!,clause_b(singleValuedInArg(F,A)).
call_u(singleValuedInArgAX(H,A,N)):- get_var_or_functor(H,F),!,clause_b(singleValuedInArgAX(F,A,N)).
call_u(ttRelationType(C)):- !, clause_b(ttRelationType(C)).

% call_u(M:G):- !,module_sanity_check(M),call_u_mp(M,G).

%call_u(G):- \+  current_prolog_flag(retry_undefined, kb_shared),!,
%   strip_module(G,M,P), no_repeats(gripe_time(5.3,on_x_rtrace(call_u_mp(M,P)))).
%call_u(M:G):- !, M:call(G).

% prolog_clause call_u ?
%call_u(G):- G \= (_:-_), !, quietly_ex(defaultAssertMt(M)),!,call_u_mp(M,G).
call_u(G):- strip_module(G,M,P), !, call_u_mp(M,P).

get_var_or_functor(H,F):- compound(H)->get_functor(H,F);H=F.

%call_u(G):- strip_module(G,M,P), no_repeats(gripe_time(5.3,on_x_rtrace(call_u_mp(M,P)))).


call_u_mp(pfc_lib, P1 ):- !, call_u_mp(query, P1 ).
% call_u_mp(pfc_lib, P1 ):- !, break_ex,'$current_source_module'(SM),SM\==pfc_lib,!,  call_u_mp(SM,P1).
call_u_mp(query, P1 ):- !, must(get_query_from(SM)),sanity(pfc_lib\==SM),call_u_mp(SM,P1).
call_u_mp(assert, P1 ):- !, must(get_assert_to(SM)),call_u_mp(SM,P1).
call_u_mp(System, P1 ):-  is_code_module(System),!, call_u_mp(query,P1).
call_u_mp(M,P):- var(P),!,call((clause_b(mtExact(M))->mpred_fact_mp(M,P);(defaultAssertMt(W),with_umt(W,mpred_fact_mp(W,P))))).
call_u_mp(_, M:P1):-!,call_u_mp(M,P1).
call_u_mp(M, (P1,P2)):-!,call_u_mp(M,P1),call_u_mp(M,P2).
call_u_mp(M, (P1*->P2;P3)):-!,(call_u_mp(M,P1)*->call_u_mp(M,P2);call_u_mp(M,P3)).
call_u_mp(M, (P1->P2;P3)):-!,(call_u_mp(M,P1)->call_u_mp(M,P2);call_u_mp(M,P3)).
call_u_mp(M, (P1->P2)):-!,(call_u_mp(M,P1)->call_u_mp(M,P2)).
call_u_mp(M, (P1*->P2)):-!,(call_u_mp(M,P1)*->call_u_mp(M,P2)).
call_u_mp(M, (P1;P2)):- !,(call_u_mp(M,P1);call_u_mp(M,P2)).
call_u_mp(M,( \+ P1)):-!, \+ call_u_mp(M,P1).
call_u_mp(M,must_ex(P1)):-!, must_ex( call_u_mp(M,P1)).
call_u_mp(M, 't'(P1)):-!, call_u_mp(M,P1).
call_u_mp(M,'{}'(P1)):-!, call_u_mp(M,P1).
call_u_mp(M,ttExpressionType(P)):-!,clause_b(M:ttExpressionType(P)).
call_u_mp(M,mtHybrid(P)):-!,clause_b(M:mtHybrid(P)).
%call_u_mp(_,is_string(P)):- !, logicmoo_util_bugger:is_string(P).
call_u_mp(M,call(O,P1)):- append_term(O,P1,P),!,call_u_mp(M,P).
call_u_mp(M,call(P1)):- !, call_u_mp(M,P1).
call_u_mp(M,call_u(P1)):- !, call_u_mp(M,P1).
% call_u_mp(MaseKB,call_u_no_bc(P)):- !, call_u_mp(MaseKB,P).


/*
call_u_mp(M,call_u(X)):- !, call_u_mp(M,X).
call_u_mp(M,clause(H,B,Ref)):-!,M:clause_u(H,B,Ref).
call_u_mp(M,clause(H,B)):-!,M:clause_u(H,B).
call_u_mp(M,clause(HB)):- expand_to_hb(HB,H,B),!, M:clause_u(H,B).
call_u_mp(M,asserta(X)):- !, M:pfc_aina(X).
call_u_mp(M,assertz(X)):- !, M:pfc_ainz(X).
call_u_mp(M,assert(X)):- !, M:pfc_ain(X).
call_u_mp(M,retract(X)):- !, M:pfc_prolog_retract(X).
call_u_mp(M,retractall(X)):- !, M:pfc_prolog_retractall(X).
*/


% prolog_clause call_u
% call_u_mp(M, (H:-B)):- B=@=call(BA),!,B=call(BA),!, (M:clause_u(H,BA);M:clause_u(H,B)),sanity(\+ reserved_body(B)).
call_u_mp(M, (H:-B)):- !,call_u_mp(M,clause_u(H,B)),(\+ reserved_body(B)).
% call_u_mp(M, (H:-B)):- !,call_u_mp(M,clause_u(H,B)),sanity(\+ reserved_body(B)).

% call_u_mp(M,P1):- predicate_property(M:P1,foreign),!,M:call(P1).
% call_u_mp(M,P1):- predicate_property(M:P1,static),!,M:call(P1).

call_u_mp(M,P1):- !,M:call(P1).


%call_u_mp(M,P1):- predicate_property(M:P1,built_in),!, M:call(P1).
%call_u_mp(M,P1):- predicate_property(M:P1,dynamic),!, M:call(P1).
%call_u_mp(M,P1):- predicate_property(M:P1,defined),!, M:call(P1).
% NEVER GETS HERE 
call_u_mp(M,P):- safe_functor(P,F,A), call_u_mp_fa(M,P,F,A).

make_visible(R,M:F/A):- wdmsg_pretty(make_visible(R,M:F/A)),fail.
make_visible(_,_):- !.
make_visible(M,M:F/A):- quietly_ex(M:export(M:F/A)).
make_visible(R,M:F/A):- must_det_l((M:export(M:F/A),R:import(M:F/A),R:export(M:F/A))).

make_visible(R,M,F,A):- wdmsg_pretty(make_visible(R,M,F,A)),fail.
make_visible(system,M,F,A):- trace_or_throw_ex(unexpected(make_visible(system,M,F,A))).
make_visible(user,M,F,A):- trace_or_throw_ex(unexpected(make_visible(user,M,F,A))).
make_visible(TM,M,F,A):- 
   must_ex((TM:import(M:F/A),TM:export(TM:F/A))),
   must_ex((TM:module_transparent(M:F/A))). % in case this has clauses th

reserved_body(B):-var(B),!,fail.
reserved_body(attr_bind(_)).
reserved_body(attr_bind(_,_)).
reserved_body(B):-reserved_body_helper(B).

reserved_body_helper(B):- \+ compound(B),!,fail.
reserved_body_helper((ZAWC,_)):- atom(ZAWC),is_pfc_chained(ZAWC).
%reserved_body_helper(inherit_above(_,_)).
%reserved_body_helper(Body):- get_bc_clause(_Head,_Head2,BCBody),!,Body=BCBody.
%reserved_body_helper((_,Body)):-!,reserved_body_helper(Body).

call_u_mp_fa(M,P,F,A):- !,loop_check(call_u_mp_lc(M,P,F,A)).

call_u_mp_fa(_,P,F,_):- (F==t; ( \+ clause_b(prologBuiltin(F)),
  F \= isT,F \= isTT, \+ predicate_property(P,file(_)))),if_defined(t_ify0(P,TGaf),fail), if_defined(isT(TGaf),false).
call_u_mp_fa(M,P,F,A):- loop_check(call_u_mp_lc(M,P,F,A)).

%call_u_mp_lc(pfc_lib,P,F,A):-!, call_u_mp_lc(baseKB,P,F,A).
%call_u_mp_lc(M,P,F,A):- current_predicate(M:F/A),!,throw(current_predicate(M:F/A)),catch(M:P,E,(wdmsg_pretty(call_u_mp(M,P)),wdmsg_pretty(E),dtrace)).
% call_u_mp_lc(baseKB,P,F,A):- kb_shared(F/A),dmsg_pretty(kb_shared(F/A)),!, call(P).

call_u_mp_lc(M,P,_,_):- !, M:call_u_mp(M,P).
call_u_mp_lc(M,P,_,_):- !, M:call(P).

/*
call_u_mp_lc(M,P,_,_):- predicate_property(M:P,file(_)),!,call(M:P).
call_u_mp_lc(M,P,_,_):- source_file(M:P,_),!,call(M:P).
call_u_mp_lc(R,P,F,A):- source_file(M:P,_),!,make_visible(R,M:F/A),call(R:P).
call_u_mp_lc(R,P,F,A):- find_module(R:P,M),dmsg_pretty(find_module(R:P,M)),make_visible(R,M:F/A),!,catch(R:call(P),E,(wdmsg_pretty(call_u_mp(R,M:P)),wdmsg_pretty(E),dtrace)).
%call_u_mp_lc(M,P):- \+ clause_b(mtHybrid(M)),!,clause_b(mtHybrid(MT)),call_u_mp(MT,P).
call_u_mp_lc(M,P,F,A):- wdmsg_pretty(dynamic(M:P)),must_det_l((dynamic(M:F/A),make_visible(user,M:F/A),multifile(M:F/A))),!,fail.
*/
/*       
Next
call_u_mp(_G,M,P):- var(P),!,call((baseKB:mtExact(M)->mpred_fact_mp(M,P);(defaultAssertMt(W),with_umt(W,mpred_fact_mp(W,P))))).
% call_u_mp(mtHybrid(P),_,mtHybrid(P)):-!,baseKB:mtHybrid(P).
call_u_mp((P),M,(P)):-!,catch(call(P),E,(wdmsg_pretty(M:call_u_mp(P)),wdmsg_pretty(E),dtrace)).
% call_u_mp(P,M,P):- !,catch(M:call(P),E,(wdmsg_pretty(M:call_u_mp(P)),wdmsg_pretty(E),dtrace)).
call_u_mp(_G,M,P):- call((baseKB:mtExact(M)->M:call(P);call(P))).
*/

pfc_BC_w_cache(W,P):- must_ex(pfc_BC_CACHE(W,P)),!,clause(P,true).

pfc_BC_CACHE(M,P0):-  ignore( \+ loop_check_early(pfc_BC_CACHE0(M,P0),trace_or_throw_ex(pfc_BC_CACHE(P0)))).

pfc_BC_CACHE0(_,P00):- var(P00),!.
pfc_BC_CACHE0(M,must_ex(P00)):-!,pfc_BC_CACHE0(M,P00).
pfc_BC_CACHE0(_,P):- predicate_property(P,static),!.
% pfc_BC_CACHE0(_,P):- predicate_property(P,built_in),!.
pfc_BC_CACHE0(_, :-(_,_)):-!.
pfc_BC_CACHE0(_,bt(_,_)):-!.
pfc_BC_CACHE0(_,clause(_,_)):-!.
pfc_BC_CACHE0(_,spft(_,_,_)):-!.
pfc_BC_CACHE0(_,P):-
 ignore((
  cyclic_break(P),
 % trigger any bc rules.
  lookup_u(bt(P,Trigger)),
  copy_term_vn(bt(P,Trigger),bt(CP,CTrigger)),
  must_ex(lookup_spft(bt(CP,_Trigger),F,T)),
  pfc_eval_lhs(CTrigger,(F,T)),
  fail)).



% I''d like to remove this soon
%call_u_no_bc(P0):- strip_module(P0,M,P), sanity(stack_check),var(P),!, M:mpred_fact(P).
%call_u_no_bc(_:true):-!.
call_u_no_bc(P):- no_repeats(call_u(P)).
% call_u_no_bc(P):- !, call_u(P).
%call_u_no_bc(G):- !, call(G).
% call_u_no_bc(P):- no_repeats(loop_check(pfc_METACALL(call_u, P))).

% pfc_call_no_bc0(P):- lookup_u(P).
% pfc_call_no_bc0(P):-  defaultAssertMt(Mt), Mt:lookup_u(P).
% pfc_call_no_bc0((A,B)):-!, pfc_call_no_bc0(A),pfc_call_no_bc0(B).
%pfc_call_no_bc0(P):-  defaultAssertMt(Mt),current_predicate(_,Mt:P),!,Mt:call(P).
%pfc_call_no_bc0(P):-  defaultAssertMt(Mt),rtrace(Mt:call(P)).
% TODO .. pfc_call_no_bc0(P):-  defaultAssertMt(Mt), clause_b(genlMt(Mt,SuperMt)), call_umt(SuperMt,P).
%pfc_call_no_bc0(P):- pfc_call_with_no_triggers(P).
% pfc_call_no_bc0(P):- nonvar(P),predicate_property(P,defined),!, P.
pfc_call_no_bc0(P):- current_prolog_flag(unsafe_speedups , true) ,!,call(P).
pfc_call_no_bc0(P):- loop_check(pfc_METACALL(ereq, P)).

pred_check(A):- var(A),!.
% catch module prefix issues
pred_check(A):- nonvar(A),must_ex(atom(A)).

%pfc_METACALL(How,P):- current_prolog_flag(unsafe_speedups , true) ,!,call(How,P).
pfc_METACALL(How,P):- pfc_METACALL(How, Cut, P), (var(Cut)->true;(Cut=cut(CutCall)->(!,CutCall);call_u_no_bc(Cut))).

pfc_METACALL(How, Cut, Var):- var(Var),!,trace_or_throw_ex(var_pfc_METACALL_MI(How,Cut,Var)).
pfc_METACALL(How, Cut, (H:-B)):-!,pfc_METACALL(How, Cut, clause_asserted_call(H,B)).
%  this is probably not advisable due to extreme inefficiency.
pfc_METACALL(_How,_Cut, Var):-is_ftVar(Var),!,pfc_call_with_no_triggers(Var).
pfc_METACALL(How, Cut, call_u_no_bc(G0)):- !,pfc_METACALL(How, Cut, (G0)).
pfc_METACALL(_How, Cut, pfc_METACALL(How2, G0)):- !,pfc_METACALL(How2, Cut, (G0)).
pfc_METACALL(How, Cut, pfc_METACALL(G0)):- !,pfc_METACALL(How, Cut, (G0)).
pfc_METACALL(_How, cut(true), !):- !.

pfc_METACALL(How, Cut, (C1->C2;C3)):-!,(pfc_METACALL(How, Cut, C1)->pfc_METACALL(How, Cut, C2);pfc_METACALL(How, Cut, C3)).
pfc_METACALL(How, Cut, (C1*->C2;C3)):-!,(pfc_METACALL(How, Cut, C1)*->pfc_METACALL(How, Cut, C2);pfc_METACALL(How, Cut, C3)).

pfc_METACALL(How, Cut, (C1->C2)):-!,(pfc_METACALL(How, Cut, C1)->pfc_METACALL(How, Cut, C2)).
pfc_METACALL(How, Cut, (C1*->C2)):-!,(pfc_METACALL(How, Cut, C1)*->pfc_METACALL(How, Cut, C2)).
pfc_METACALL(How, Cut, (C1,C2)):-!,pfc_METACALL(How, Cut, C1),pfc_METACALL(How, Cut, C2).
pfc_METACALL(How, Cut, (C1;C2)):-!,(pfc_METACALL(How, Cut, C1);pfc_METACALL(How, Cut, C2)).
%  check for system predicates first
% pfc_METACALL(_How, _SCut, P):- predicate_property(P,built_in),!, call(P).


pfc_METACALL(How, Cut, M):- fixed_syntax(M,O),!,pfc_METACALL(How, Cut, O).
pfc_METACALL(How, Cut, U:X):-U==user,!,pfc_METACALL(How, Cut, X).
% pfc_METACALL(How, Cut, t(A,B)):-(atom(A)->true;(no_repeats(arity(A,1)),atom(A))),ABC univ_safe [A,B],pfc_METACALL(How, Cut, ABC).
% pfc_METACALL(How, Cut, isa(B,A)):-(atom(A)->true;(no_repeats(tCol(A)),atom(A))),ABC univ_safe [A,B],pfc_METACALL(How, Cut, ABC).
%pfc_METACALL(How, Cut, t(A,B)):-!,(atom(A)->true;(no_repeats(arity(A,1)),atom(A))),ABC univ_safe [A,B],pfc_METACALL(How, Cut, ABC).
pfc_METACALL(How, Cut, t(A,B,C)):-!,(atom(A)->true;(no_repeats(arity(A,2)),atom(A))),ABC univ_safe [A,B,C],pfc_METACALL(How, Cut, ABC).
pfc_METACALL(How, Cut, t(A,B,C,D)):-!,(atom(A)->true;(no_repeats(arity(A,3)),atom(A))),ABC univ_safe [A,B,C,D],pfc_METACALL(How, Cut, ABC).
pfc_METACALL(How, Cut, t(A,B,C,D,E)):-!,(atom(A)->true;(no_repeats(arity(A,4)),atom(A))),ABC univ_safe [A,B,C,D,E],pfc_METACALL(How, Cut, ABC).
pfc_METACALL(How, Cut, call(X)):- !, pfc_METACALL(How, Cut, X).
pfc_METACALL(How, Cut, call_u(X)):- !, pfc_METACALL(How, Cut, X).
pfc_METACALL(How, Cut, once(X)):- !, once(pfc_METACALL(How, Cut, X)).
pfc_METACALL(How, Cut, must_ex(X)):- !, must_ex(pfc_METACALL(How, Cut, X)).
pfc_METACALL(How, Cut, \+(X)):- !, \+ pfc_METACALL(How, Cut, X).
pfc_METACALL(How, Cut, not(X)):- !,\+ pfc_METACALL(How, Cut, X).
pfc_METACALL(_How, _Cut, clause(H,B,Ref)):-!,clause_u(H,B,Ref).
pfc_METACALL(_How, _Cut, clause(H,B)):-!,clause_u(H,B).
pfc_METACALL(_How, _Cut, clause(HB)):-expand_to_hb(HB,H,B),!,clause_u(H,B).
pfc_METACALL(_How, _Cut, asserta(X)):- !, aina(X).
pfc_METACALL(_How, _Cut, assertz(X)):- !, ainz(X).
pfc_METACALL(_How, _Cut, assert(X)):- !, pfc_ain(X).
pfc_METACALL(_How, _Cut, retract(X)):- !, pfc_prolog_retract(X).
pfc_METACALL(_How, _Cut, retractall(X)):- !, pfc_prolog_retractall(X).
% TODO: test removal
%pfc_METACALL(How, Cut, prologHybrid(H)):-get_functor(H,F),!,isa_asserted(F,prologHybrid).
% pfc_METACALL(How, Cut, HB):-quietly_ex((full_transform_warn_if_changed(pfc_METACALL,HB,HHBB))),!,pfc_METACALL(How, Cut, HHBB).
%pfc_METACALL(How, Cut, argIsa(pfc_isa,2,pfc_isa/2)):-  trace_or_throw_ex(pfc_METACALL(How, Cut, argIsa(pfc_isa,2,pfc_isa/2))),!,fail.
% TODO: test removal
% pfc_METACALL(How, Cut, isa(H,B)):-!,isa_asserted(H,B).
pfc_METACALL(_How, _Cut, (H:-B)):- !, clause_u((H :- B)).
pfc_METACALL(_How, _Cut, M:(H:-B)):- !, clause_u((M:H :- B)).

% TODO: pfc_METACALL(_How, _Cut, M:HB):- current_prolog_flag(unsafe_speedups , true) ,!, call(M:HB).

%pfc_METACALL(_How, _SCut, P):- fail, predicate_property(P,built_in),!, call(P).
%pfc_METACALL(How, Cut, (H)):- is_static_pred(H),!,show_pred_info(H),dtrace(pfc_METACALL(How, Cut, (H))).
pfc_METACALL( How,   Cut, P) :- fail, predicate_property(P,number_of_clauses(_)),!,
     clause_u(P,Condition),
     pfc_METACALL(How,Cut,Condition),
       (var(Cut)->true;(Cut=cut(CutCall)->(!,CutCall);call_u_no_bc(Cut))).

% pfc_METACALL(_How,_SCut, P):- must_ex(current_predicate(_,M:P)),!, call_u(M:P).
%pfc_METACALL(How, Cut, H):- !, locally_tl(infAssertedOnly(H),call_u(H)).
pfc_METACALL(How, _SCut, P):- call(How,P).




%% action_is_undoable(+G)
%
% an action is action_is_undoable if there exists a method for undoing it.
%
action_is_undoable(G):- lookup_u(do_and_undo(G,_)).
action_is_undoable(G):- safe_functor(G,F,_),lookup_u(do_and_undo(F,Undo)),atom(Undo).



%% pfc_nf(+In,-Out)
%
% maps the LHR of a Pfc rule In to one normal form
%  Out.  It also does certain optimizations.  Backtracking into this
%  predicate will produce additional clauses.
%

/*
pfc_nf({LHS},List):- !,
  pfc_nf((nondet,{LHS}),List).
*/

pfc_nf(LHS,List):-
  pfc_nf1(LHS,List2),
  pfc_nf_negations(List2,List).


%%  pfc_nf1(+In,-Out)
%
% maps the LHS of a Pfc rule In to one normal form
%  Out.  Backtracking into this predicate will produce additional clauses.

% handle a variable.

pfc_nf1(P,[P]):- is_ftVar(P), !.

% these next two rules are here for upward compatibility and will go
% away eventually when the P/Condition form is no longer used anywhere.

pfc_nf1(P/Cond,[(\+P)/Cond]):- pfc_negated_literal(P), !, 
  nop(dmsg_pretty(warn(pfc_nf1(P/Cond,[(\+P)/Cond])))).

pfc_nf1(P/Cond,[P/Cond]):- var(P),!.
pfc_nf1(P/Cond,[P/Cond]):- ((pfc_db_type(P,trigger(_));pfcLiteral_nonvar(P))), !.

%  handle a negated form

pfc_nf1(NegTerm,NF):-
  pfc_unnegate(NegTerm,Term),
  !,
  pfc_nf1_negation(Term,NF).

%  disjunction.

pfc_nf1((P;Q),NF):-
  !,
  (pfc_nf1(P,NF) ;   pfc_nf1(Q,NF)).


%  conjunction.

pfc_nf1((P,Q),NF):-
  !,
  pfc_nf1(P,NF1),
  pfc_nf1(Q,NF2),
  append(NF1,NF2,NF).

pfc_nf1([P|Q],NF):-
  !,
  pfc_nf1(P,NF1),
  pfc_nf1(Q,NF2),
  append(NF1,NF2,NF).


% prolog_clause pfc_nf1
pfc_nf1((H :- B)  , [(H :- B)]):-  
  pfcPositiveLiteral(H),!.

/*
% prolog_clause pfc_nf1 COMMENTED
pfc_nf1((H :- B)  ,[P]):-   
  pfcPositiveLiteral(H),
  P={clause(H , B)},
  dmsg_pretty(warn(pfc_nf1((H :- B)  ,[P]))),!.

% prolog_clause pfc_nf1 COMMENTED
pfc_nf1((H :- B)  ,[P]):-   
  pfcPositiveLiteral(H),
  P={clause(H , B)},
  dmsg_pretty(warn(pfc_nf1((H :- B)  ,[P]))),!.
*/

%  handle a random literal.

pfc_nf1(P,[P]) :- is_ftVar(P), !.
pfc_nf1(P,[P]):-
  pfcLiteral_nonvar(P),
  !.

pfc_nf1(Term,[Term]):- pfc_trace_msg("pfc_nf Accepting ~p",[Term]),!.


%=% shouldn''t we have something to catch the rest as errors?
pfc_nf1(Term,[Term]):-
  pfcWarn("pfc_nf doesn't know how to normalize ~p",[Term]),dtrace,!,fail.

notiffy_p(P,\+(P)):- var(P),!. % prevents next line from binding
notiffy_p(\+(P),P):- dmsg_pretty(notiffy_p(\+(P),P)), !.
notiffy_p(P,\+(P)).

%% pfc_nf1_negation(+P, ?NF) is semidet.
%
% is true if NF is the normal form of \+P.
%
pfc_nf1_negation(P,[\+P]):- is_ftVar(P),!.
pfc_nf1_negation((P/Cond),[NOTP/Cond]):- notiffy_p(P,NOTP), !.

pfc_nf1_negation((P;Q),NF):-
  !,
  pfc_nf1_negation(P,NFp),
  pfc_nf1_negation(Q,NFq),
  append(NFp,NFq,NF).

pfc_nf1_negation((P,Q),NF):-
  % this code is not correct! twf.
  !,
  pfc_nf1_negation(P,NF)
  ;
  (pfc_nf1(P,Pnf),
   pfc_nf1_negation(Q,Qnf),
   append(Pnf,Qnf,NF)).

pfc_nf1_negation(P,[\+P]).


%%  pfc_nf_negations(List2,List) is det.
%
% sweeps through List2 to produce List,
%  changing -{...} to {\+...}
% % ? is this still needed? twf 3/16/90

%% pfc_nf_negations( :TermX, :TermX) is semidet.
%
% PFC Normal Form Negations.
%
pfc_nf_negations(X,X) :- !.  % I think not! twf 3/27/90

pfc_nf_negations([],[]).

pfc_nf_negations([H1|T1],[H2|T2]):-
  pfc_nf_negation(H1,H2),
  pfc_nf_negations(T1,T2).


%% pfc_nf_negation(+X, ?X) is semidet.
%
% PFC Normal Form Negation.
%
pfc_nf_negation(Form,{\+ X}):-
  nonvar(Form),
  Form=(-({X})),
  !.
pfc_nf_negation(X,X).



%%  buildRhs(+Sup,+Conjunction,-Rhs)
%

buildRhs(_Sup,X,[X]):-
  var(X),
  !.

buildRhs(Sup,(A,B),[A2|Rest]):-
  !,
  pfcCompileRhsTerm(Sup,A,A2),
  buildRhs(Sup,B,Rest).

buildRhs(Sup,X,[X2]):-
   pfcCompileRhsTerm(Sup,X,X2).


pfcCompileRhsTerm(_Sup,P,P):-is_ftVar(P),!.

% TODO confirm this is not reversed (mostly confirmed this is correct now)
pfcCompileRhsTerm(Sup, \+ ( P / C), COMPILED) :- nonvar(C), !,
  pfcCompileRhsTerm(Sup, ( \+ P ) / C , COMPILED).

% dmiles added this to get PFC style lazy BCs
pfcCompileRhsTerm(Sup,(P/C),((P0 <- C0))) :- fail, !,pfcCompileRhsTerm(Sup,P,P0),
   build_code_test(Sup,C,C0),!.

pfcCompileRhsTerm(Sup,(P/C),((P0 :- C0))) :- !,pfcCompileRhsTerm(Sup,P,P0),
   build_code_test(Sup,C,C0),!.

pfcCompileRhsTerm(Sup,I,O):- pfcCompileRhsTerm_consquent(Sup,I,O).





     %% pfc_unnegate(+N, ?P) is semidet.
     %
     %  is true if N is a negated term and P is the term
     %  with the negation operator stripped.  (not Logical ~ negation however)
     %
     pfc_unnegate(P,_):- is_ftVar(P),!,fail.
     pfc_unnegate((\+(P)),P).
     pfc_unnegate((-P),P).
     pfc_unnegate((~P),P).



     %% pfc_negated_literal(+P) is semidet.
     %
     % PFC Negated Literal.
     %
     %pfc_negated_literal(P):- is_ftVar(P),!,fail.
     pfc_negated_literal(P):-
       pfc_unnegate(P,Q),
       pfcPositiveLiteral(Q).
     %pfc_negated_literal(~(_)).


     pfcLiteral_or_var(X):- is_ftVar(X),!.
     pfcLiteral_or_var(X):- pfc_negated_literal(X),!.
     pfcLiteral_or_var(X):- pfcPositiveLiteral(X),!.

     pfcLiteral(X):- is_ftVar(X),!.
     pfcLiteral(X):- pfc_negated_literal(X),!.
     pfcLiteral(X):- pfcPositiveLiteral(X),!.

     pfcLiteral_nonvar(X):- is_ftVar(X),!,fail.
     pfcLiteral_nonvar(X):- pfc_negated_literal(X),!.
     pfcLiteral_nonvar(X):- pfcPositiveLiteral(X),!.

     pfcPositiveLiteral(X):-
       is_ftNonvar(X),
       X \= ~(_), % MAYBE COMMENT THIS OUT
       \+ pfc_db_type(X,rule(_RT)),
       get_functor(X,F,_),
       \+ pfc_neg_connective(F),
       !.

     pfc_positive_fact(X):-  pfcPositiveLiteral(X), X \= ~(_), 
        pfc_db_type(X,fact(_FT)), \+ pfc_db_type(X,trigger).

     pfc_is_trigger(X):-   pfc_db_type(X,trigger(_)).



     pfcConnective(Var):-var(Var),!,fail.
     pfcConnective(';').
     pfcConnective(',').
     pfcConnective('/').
     pfcConnective('{}').
     pfcConnective('|').
     pfcConnective(('==>')).
     pfcConnective(('<-')).
     pfcConnective('<==>').
     pfcConnective('-').
     % pfcConnective('~').
     pfcConnective(('\\+')).


     pfc_neg_connective('-').
     % pfc_neg_connective('~').
     pfc_neg_connective('\\+').

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
     is_active_lhs(pfcAction(_Act)).
     is_active_lhs('{}'(_Act)).
     is_active_lhs((Lhs1/Lhs2)):- !,is_active_lhs(Lhs1);is_active_lhs(Lhs2).
     is_active_lhs((Lhs1,Lhs2)):- !,is_active_lhs(Lhs1);is_active_lhs(Lhs2).
     is_active_lhs((Lhs1;Lhs2)):- !,is_active_lhs(Lhs1);is_active_lhs(Lhs2).


     add_lhs_cond(Lhs1/Cond,Lhs2,Lhs1/(Cond,Lhs2)):-!.
     add_lhs_cond(Lhs1,Lhs2,Lhs1/Lhs2).


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
     constrain_meta(P,pfc_positive_fact(P)):- is_ftVar(P),!.
     % NEG chaining
     constrain_meta(~ P, CP):- !,  constrain_meta(P,CP).
     constrain_meta(\+ P, CP):- !,  constrain_meta(P,CP).
     % FWD chaining
     constrain_meta((_==>Q),nonvar(Q)):- !, is_ftVar(Q).
     % EQV chaining
     constrain_meta((P<==>Q),(nonvar(Q);nonvar(P))):- (is_ftVar(Q);is_ftVar(P)),!.
     % BWD chaining
     constrain_meta((Q <- _),pfcLiteral_nonvar(Q)):- is_ftVar(Q),!.
     constrain_meta((Q <- _),CQ):- !, constrain_meta(Q,CQ).
     % CWC chaining
     constrain_meta((Q :- _),pfcLiteral_nonvar(Q)):- is_ftVar(Q),!.
     constrain_meta((Q :- _),CQ):- !, constrain_meta(Q,CQ).




%% processRule(+Lhs, ?Rhs, ?Parent_rule) is semidet.
%
% Process Rule.
%

/*

Next Line converts:
((prologHybrid(F),arity(F,A))==>{kb_shared(F/A)}).

To:
arity(F,A)/prologHybrid(F)==>{kb_shared(F/A)}.
prologHybrid(F)/arity(F,A)==>{kb_shared(F/A)}.

In order to reduce the number of postivie triggers (pt/2s)
*/

processRule(LhsIn,Rhs,Parent_rule):- constrain_meta(LhsIn,How),!,
  processRule0(LhsIn/How,Rhs,Parent_rule).

processRule(LhsIn,Rhs,Parent_rule):- is_simple_lhs(LhsIn),LhsIn = (Lhs1,Lhs2),
  Lhs2\=(_,_),
  add_lhs_cond(Lhs1,Lhs2,LhsA),
  add_lhs_cond(Lhs2,Lhs1,LhsB),
  processRule0(LhsA,Rhs,Parent_rule),
  processRule0(LhsB,Rhs,Parent_rule).
processRule(Lhs,Rhs,Parent_rule):-processRule0(Lhs,Rhs,Parent_rule).

processRule0(Lhs,Rhs,Parent_rule):-
  must_notrace_pfc(get_source_mfl(U)),!,
  copy_term(Parent_rule,Parent_ruleCopy),
  buildRhs(U,Rhs,Rhs2),
  foreach(pfc_nf(Lhs,Lhs2),
    ignore(buildRule(Lhs2,rhs(Rhs2),(Parent_ruleCopy,U)))).


%% buildRule(+Lhs, ?Rhs, ?Support) is semidet.
%
% Build Rule.
%
buildRule(Lhs,Rhs,Support):-
  copy_term_vn(Support,WS),
  pfc_mark_as(WS,Lhs,pfcLHS),
  buildTrigger(WS,Lhs,Rhs,Trigger),
  cyclic_break((Lhs,Rhs,WS,Trigger)),
  doall(pfc_eval_lhs_no_nc(Trigger,Support)).

buildTrigger(WS,[],Consequent,ConsequentO):-
   pfcCompileRhsTerm_consquent(WS,Consequent,ConsequentO).

buildTrigger(WS,[V|Triggers],Consequent,pt(V,X)):-
  is_ftVar(V),
  !,
  buildTrigger(WS,Triggers,Consequent,X).

% T1 is a negation in the next two clauses
buildTrigger(WS,[TT|Triggers],Consequent,nt(T2,Test2,X)):- 
  compound(TT),
  TT=(T1/Test),
  pfc_unnegate(T1,T2),
  !,
  build_neg_test(WS,T2,Test,Test2),
  buildTrigger(WS,Triggers,Consequent,X).

buildTrigger(WS,[(T1)|Triggers],Consequent,nt(T2,Test,X)):-
  pfc_unnegate(T1,T2),
  !,
  build_neg_test(WS,T2,true,Test),
  buildTrigger(WS,Triggers,Consequent,X).

buildTrigger(WS,[{Test}|Triggers],Consequent,(Test*->Body)):- % Noncutted ->
  !,
  buildTrigger(WS,Triggers,Consequent,Body).

buildTrigger(WS,[T/Test|Triggers],Consequent,pt(T,X)):-
  !,
  build_code_test(WS, Test,Test2),
  buildTrigger(WS,[{Test2}|Triggers],Consequent,X).


%buildTrigger(WS,[snip|Triggers],Consequent,snip(X)):-
%  !,
%  buildTrigger(WS,Triggers,Consequent,X).


buildTrigger(WS,[T|Triggers],Consequent,Reslt):- 
  constrain_meta(T,Test)->
  buildTrigger(WS,[T/Test|Triggers],Consequent,Reslt),!.

buildTrigger(WS,[T|Triggers],Consequent,pt(T,X)):-
  !,
  buildTrigger(WS,Triggers,Consequent,X).


%%  build_neg_test(+WhyBuild,+Test,+Testin,-Testout).
%
%  builds the test used in a negative trigger (nt/3).  This test is a
%  conjunction of the check than no matching facts are in the db and any
%  additional test specified in the rule attached to this - term.
%

build_neg_test(WS,T,Testin,Testout):-
  build_code_test(WS,Testin,Testmid),
  pfc_conjoin((call_u_no_bc(T)),Testmid,Testout).

%% check_never_assert(+Pred) is semidet.
%
% Check Never Assert.
%

%check_never_assert(_Pred):-!.
%:-dumpST.
check_never_assert(MPred):- strip_module(MPred,M,_Pred),
  quietly_ex(ignore((check_db_sanity(never_assert_u,M,MPred)))).

check_db_sanity(Checker,CModule,Pred):- 
 (current_predicate(CModule:Checker/2)->Module=CModule;Module=baseKB),!,
 copy_term_and_varnames(Pred,Pred_2),
 CheckerCall  univ_safe [ Checker,Pred_2,_Why],
 call_u_no_bc(Module:CheckerCall),
 sanity(variant_u(Pred,Pred_2)),
 trace_or_throw_ex(Module:CheckerCall).

%check_never_assert(Pred):- quietly_ex(ignore(( copy_term_and_varnames(Pred,Pred_2),call_u_no_bc(never_assert_u(Pred_2)),variant_u(Pred,Pred_2),trace_or_throw_ex(never_assert_u(Pred))))).
%check_never_assert(Pred):- quietly_ex((( copy_term_and_varnames(Pred,Pred_2),call_u_no_bc(never_assert_u(Pred_2,Why)), variant_u(Pred,Pred_2),trace_or_throw_ex(never_assert_u(Pred,Why))))),fail.

%% check_never_retract(+Pred) is semidet.
%
% Check Never Retract.
%

%check_never_retract(_Pred):-!.
check_never_retract(MPred):- strip_module(MPred,M,_Pred),
  quietly_ex(ignore((check_db_sanity(never_retract_u,M,MPred)))).


:- export(pfc_mark_as_ml/3).

%% pfc_mark_as_ml(+Sup, ?Type, ?P) is semidet.
%
% PFC Mark Converted To Ml.
%
pfc_mark_as_ml(Sup,Type,P):- pfc_mark_as(Sup,P,Type).


%% pos_2_neg(+P, ?P) is semidet.
%
% pos  Extended Helper Negated.
%
pos_2_neg(p,n):-!.
pos_2_neg(n,p):-!.
pos_2_neg(P,~(P)):- (var(P); P \= '~'(_)),!.
% pos_2_neg(P,~(P)).


%% pfc_mark_as(+VALUE1, ?VALUE2, :TermP, ?VALUE4) is semidet.
%
% PFC Mark Converted To.
%
pfc_mark_as(_,P,_):- is_ftVar(P),!.
pfc_mark_as(Sup,M:P,Type):- atom(M),mtHybrid(M),!,M:pfc_mark_as(Sup,P,Type).
pfc_mark_as(Sup,_:P,Type):- !, pfc_mark_as(Sup,P,Type).
pfc_mark_as(Sup,\+(P),Type):- !,pfc_mark_as(Sup,P,Type).
pfc_mark_as(Sup,~(P),Type):- !,pfc_mark_as(Sup,P,Type).
pfc_mark_as(Sup,-(P),Type):- !,pfc_mark_as(Sup,P,Type).
pfc_mark_as(Sup,not(P),Type):- !,pfc_mark_as(Sup,P,Type).
pfc_mark_as(Sup,[P|PL],Type):- is_list(PL), !,must_maplist(pfc_mark_as_ml(Sup,Type),[P|PL]).
pfc_mark_as(Sup,( P / CC ),Type):- !, pfc_mark_as(Sup,P,Type),pfc_mark_as(Sup,( CC ),pfcCallCode).
pfc_mark_as(Sup,( P :- _CC), Type):- !, pfc_mark_as(Sup,P, Type) /* , pfc_mark_as(Sup, ( CC ), pfcCallCode) */ .
pfc_mark_as(Sup,'{}'(  CC ), _Type):- pfc_mark_as(Sup,( CC ),pfcCallCode).
pfc_mark_as(Sup,( A , B), Type):- !, pfc_mark_as(Sup,A, Type),pfc_mark_as(Sup,B, Type).
pfc_mark_as(Sup,( A ; B), Type):- !, pfc_mark_as(Sup,A, Type),pfc_mark_as(Sup,B, Type).
pfc_mark_as(Sup,( A ==> B), Type):- !, pfc_mark_as(Sup,A, Type),pfc_mark_as(Sup,B, pfcRHS).
pfc_mark_as(Sup,( B <- A), Type):- !, pfc_mark_as(Sup,A, Type),pfc_mark_as(Sup,B, pfcRHS).
pfc_mark_as(Sup,P,Type):-get_functor(P,F,A),ignore(pfc_mark_fa_as(Sup,P,F,A,Type)),!.


%% pfc_mark_fa_as(+Sup, ?P, ?F, ?A, ?Type) is semidet.
%
% PFC Mark Functor-arity Converted To.
%

% pfc_mark_fa_as(_Sup,_P,'\=',2,_):- dtrace.
% BREAKS SIMPLE CASES
% pfc_mark_fa_as(_Sup,_P,_,_,Type):- Type \== pfcLHS, Type \== pfcRHS, current_prolog_flag(unsafe_speedups , true) ,!.
pfc_mark_fa_as(_Sup,_P,isa,_,_):- !.
%pfc_mark_fa_as(_Sup,_P,_,_,pfcCallCode):- !.
pfc_mark_fa_as(_Sup,_P,t,_,_):- !.
pfc_mark_fa_as(_Sup,_P,argIsa,N,_):- !,must_ex(N=3).
pfc_mark_fa_as(_Sup,_P,arity,N,_):- !,must_ex(N=2).
pfc_mark_fa_as(_Sup,_P,pfc_prop,N,_):- !,must_ex(N=4).
%pfc_mark_fa_as(_Sup,_P,pfc_isa,N,_):- must_ex(N=2).
pfc_mark_fa_as(_Sup,_P,'[|]',N,_):- dtrace,must_ex(N=2).
pfc_mark_fa_as(_Sup,_P,_:pfc_prop,N,_):- must_ex(N=4).
pfc_mark_fa_as(Sup, _P,F,A,Type):- really_pfc_mark(Sup,Type,F,A),!.

% i hope i am not exagerating but anniepoo used to enter this yearly contest for whom could build graphical assets the most pretty and complex the quickest in secondlife.. (now it makes sense she used a 3d mouse)  she won so much, they and she had to ban herself becasue she always won hands down.. so with this agility to create the physical aspects of a wolrd veery easily .. we realized we could make a fun leanring inpiring world for AIs .. however 

really_pfc_mark(_  ,Type,F,A):- call_u_no_bc(pfc_prop(_M,F,A,Type)),!.
really_pfc_mark(Sup,Type,F,A):-
  current_assertion_module(M),
  MARK = pfc_prop(M,F,A,Type),
  check_never_assert(MARK),
  why_marked(M,Sup,WM),
  with_no_pfc_trace_exec(with_fc_mode(direct,pfc_post1(MARK,(WM,ax)))).
  %with_no_pfc_trace_exec(with_fc_mode(direct,pfc_post1(MARK,(why_marked(Sup),ax)))).
  % with_no_pfc_trace_exec(with_fc_mode(direct,mpred_fwc1(MARK,(why_marked(Sup),ax)))),!.

why_marked(M,_Sup,mfl4(VarNameZ,M,F,L)):- source_location(F,L),!,varnames_load_context(VarNameZ).
why_marked(_,Sup,Sup).

%% fa_to_p(+F, ?A, ?P) is semidet.
%
% Functor-arity Converted To Pred.
%
fa_to_p(F,A,P):-is_ftNameArity(F,A),safe_functor(P,F,A),
  ( P \= call_u_no_bc(_) ),( P \= '$VAR'(_)).


%% build_code_test(+WS, ?Test, ?TestO) is semidet.
%
% Build Code Test.
%
% what this does...
%
%   strips away any currly brackets
%   converts cuts to cut_c/0
%   converts variable Ps to call_u_no_bc(P)
%
build_code_test(_Support,Test,TestO):- is_ftVar(Test),!,must_ex(TestO=call_u_no_bc(Test)).
build_code_test(WS,{Test},TestO) :- !,build_code_test(WS,Test,TestO).
build_code_test(_Sup,!,cut_c):-!.
build_code_test(WS,rhs(Test),rhs(TestO)) :- !,build_code_test(WS,Test,TestO).
build_code_test(WS,Test,TestO):- is_list(Test),must_maplist(build_code_test(WS),Test,TestO).
build_code_test(_WS,(H:-B),clause_asserted_u(H,B)):- !.
build_code_test(_WS,M:(H:-B),clause_asserted_u(M:H,B)):- !.
build_code_test(WS,Test,TestO):- code_sentence_op(Test),Test univ_safe [F|TestL],must_maplist(build_code_test(WS),TestL,TestLO),TestO univ_safe [F|TestLO],!.
build_code_test(WS,Test,Test):- must_ex(pfc_mark_as(WS,Test,pfcCallCode)),!.
build_code_test(_,Test,Test).


%% pfcCompileRhsTerm_consquent(+Support, +TestIn, -TestOut) is semidet.
%
% Build Consequent.
%
pfcCompileRhsTerm_consquent(_      ,Test,Test):- is_ftVar(Test),!.
pfcCompileRhsTerm_consquent(_      ,Test,TestO):-is_ftVar(Test),!,TestO=added(Test).
pfcCompileRhsTerm_consquent(_Sup,!,{cut_c}):-!.
pfcCompileRhsTerm_consquent(WS,'{}'(Test),'{}'(TestO)) :- !,build_code_test(WS,Test,TestO).
pfcCompileRhsTerm_consquent(WS,rhs(Test),rhs(TestO)) :- !,pfcCompileRhsTerm_consquent(WS,Test,TestO).
pfcCompileRhsTerm_consquent(WS,Test,TestO):- is_list(Test),must_maplist(pfcCompileRhsTerm_consquent(WS),Test,TestO).

pfcCompileRhsTerm_consquent(_WS,(H:-B),(H:-B)):-!.

pfcCompileRhsTerm_consquent(WS,Test,TestO):-
   code_sentence_op(Test),Test univ_safe [F|TestL],
   must_maplist(pfcCompileRhsTerm_consquent(WS),TestL,TestLO),
   TestO univ_safe [F|TestLO],!.

pfcCompileRhsTerm_consquent(Sup,I,O):-
  % TODO replace the next line with  I=O,
    full_transform_warn_if_changed(compile_rhs,I,O),
    must_ex(pfc_mark_as(Sup,O,pfcRHS)),!.



%% code_sentence_op( :TermVar) is semidet.
%
% Code Sentence Oper..
%
code_sentence_op(Var):-is_ftVar(Var),!,fail.
code_sentence_op(rhs(_)).
code_sentence_op(~(_)).
code_sentence_op(-(_)).
code_sentence_op(-(_)).
code_sentence_op((_,_)).
code_sentence_op((_;_)).
code_sentence_op(\+(_)).
code_sentence_op(call(_)).
code_sentence_op(call_u(_)).
code_sentence_op(call_u_no_bc(_,_)).
code_sentence_op(Test:-_):-!,code_sentence_op(Test).
code_sentence_op(Test):-
  predicate_property(Test,built_in),
  predicate_property(Test,meta_predicate(PP)), \+ (( arg(_,PP,N), N \= 0)).


%% all_closed(+C) is semidet.
%
% All Closed.
%
all_closed(C):- \+is_ftCompound(C)->true;(safe_functor(C,_,A),A>1,\+((arg(_,C,Arg),is_ftVar(Arg)))),!.


%head_to_functor_name(I,F):- is_ftCompound(I),get_head(I,H),is_ftCompound(I),get_functor_name(I,F).
head_to_functor_name(I,F):- is_ftCompound(I),get_functor(I,F).


%% pfc_db_type(+VALUE1, ?Type) is semidet.
%
% PFC Database Type.
%
%  simple typeing for Pfc objects
%
pfc_db_type(Var,Type):- var(Var),!, Type=fact(_FT).
pfc_db_type(_:X,Type):- !, pfc_db_type(X,Type).
pfc_db_type(~_,Type):- !, Type=fact(_FT).
pfc_db_type(('==>'(_,_)),Type):- !, Type=rule(fwd).
pfc_db_type(('<==>'(_,_)),Type):- !, Type=rule(<==>).
pfc_db_type(('<-'(_,_)),Type):- !, Type=rule(bwc).
pfc_db_type((':-'(_,_)),Type):- !, Type=rule(cwc).
pfc_db_type(pt(_,_,_),Type):- !, Type=trigger(pt).
pfc_db_type(pt(_,_),Type):- !, Type=trigger(pt).
pfc_db_type(nt(_,_,_),Type):- !,  Type=trigger(nt).
pfc_db_type(bt(_,_),Type):- !,  Type=trigger(bt).
pfc_db_type(pfcAction(_),Type):- !, Type=action.
pfc_db_type((('::::'(_,X))),Type):- !, pfc_db_type(X,Type).
pfc_db_type(_,fact(_FT)):-
  %  if it''s not one of the above, it must_ex be a fact!
  !.

pfc_assert_w_support(P,Support):-
  (clause_asserted_u(P) ; assert_u_confirmed_was_missing(P)),
  !,
  pfc_add_support(P,Support).

pfc_asserta_w_support(P,Support):-
  (clause_asserted_u(P) ; asserta_u(P)),
  !,
  pfc_add_support(P,Support).

pfc_assertz_w_support(P,Support):-
  (clause_asserted_u(P) ; assertz_u(P)),
  !,
  pfc_add_support(P,Support).



%% clause_asserted_u(+Head) is semidet.
%
% PFC Clause For User Interface.
%

:- module_transparent(clause_asserted_call/2).
clause_asserted_call(H,B):-clause_asserted(H,B).

clause_asserted_u(P):- clause_asserted_i(P),!.
  

/*
clause_asserted_u0(P):-clause_asserted(P),!,sanity(clause_asserted_u1(P)),!.
clause_asserted_u0(P):- sanity( \+ clause_asserted_u1(P)),fail.
clause_asserted_u1(M:(H:-B)):- nonvar(M),!, clause_asserted_u0(M,H,B). 
clause_asserted_u1((M:H):-B):- nonvar(M),!, clause_asserted_u0(M,H,B). 
clause_asserted_u1(MH):- strip_module(MH,M,H),clause_asserted_u0(M,H,true),!. 

clause_asserted_u0(M,H,_):- sanity((nonvar(H), ignore(show_failure(\+ is_static_predicate(M:H))))),fail.
% clause_asserted_u0(MH,_):- \+ ground(MH),must_notrace_pfc(full_transform(change(assert,assert_u),MH,MA)),MA\=@=MH,!,clause_asserted_u(MA).
% clause_asserted_u0(M,H,B):- current_prolog_flag(unsafe_speedups, true), !,clause_asserted_ii(M,H,B).
clause_asserted_u0(M,H,B):- must_ex(quietly_ex(fix_mp(clause(clause,clause_asserted_u),M:H,M,H))),clause_asserted_ii(M,H,B).
*/
clause_asserted_ii(M,H,B):- system:clause(M:H,B,Ref),system:clause(_:HH,BB,Ref),H=@=HH,B=@=BB,!.

variant_m(_:H,_:HH):-!,H=@=HH.
variant_m(H,_:HH):-!,H=@=HH.
variant_m(_:H,HH):-!,H=@=HH.
variant_m(H,HH):-!,H=@=HH.

variant_u(HeadC,Head_copy):-variant_i(HeadC,Head_copy).

/*
%% foreach(+Binder, ?Body) is det.
%
% Foreachl Do.
%
foreach(Binder,Body):- Binder,pfcl_do(Body),fail.
foreach(_,_).


%% pfcl_do(+X) is semidet.
%
% executes P once and always succeeds.
%
pfcl_do(X):- X,!.
pfcl_do(_).
*/

%% pfc_union(L1,L2,L3) is semidet.
%
%  true if set L3 is the result of appending sets
%  L1 and L2 where sets are represented as simple lists.
%
pfc_union([],L,L).
pfc_union([Head|Tail],L,Tail2):-
  memberchk(Head,L),
  !,
  pfc_union(Tail,L,Tail2).
pfc_union([Head|Tail],L,[Head|Tail2]):-
  pfc_union(Tail,L,Tail2).


%  pfc_conjoin(+Conjunct1,+Conjunct2,?Conjunction).
%  arg3 is a simplified expression representing the conjunction of
%  args 1 and 2.

pfc_conjoin(True,X,X):- True==true, !.
pfc_conjoin(X,True,X):- True==true, !.
pfc_conjoin(C1,C2,(C1,C2)).


%   File   : pfcdb.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Author :  Dave Matuszek, dave@prc.unisys.com
%   Author :  Dan Corpron
%   Updated: 10/11/87, ...
%   Purpose: predicates to manipulate a Pfc database (e.ax. save,
% 	restore, reset, etc.)

%% pfc_reset_kb() is det.
%
% removes all forward chaining rules, facts and justifications from each db.
%
pfc_reset:- 
  pfc_reset_kb,
  forall((clause_b(mtHybrid(Module)),Module\==baseKB),
       pfc_reset_kb(Module)).

%% pfc_reset_kb() is det.
%% pfc_reset_kb(+Module) is det.
%
% removes all forward chaining rules, facts and justifications from db.
%
pfc_reset_kb:- defaultAssertMt(Module),
  (Module\==baseKB->pfc_reset_kb(Module);true).

pfc_reset_kb_facts(Module):- nop(Module).

mfl_module(mfl4(_VarNameZ,M,_,_),Module):- Module==M,!.
mfl_module(mfl4(_VarNameZ,_,F,_),Module):- atom(F),
   module_property(M,file(F)),  
   \+ ((module_property(M2,file(F)),M\==M2)),
   Module==M.

pfc_reset_kb(Module):-
  with_exact_kb(Module,pfc_reset_kb_0(Module)).

pfc_reset_kb_0(Module):- pfc_reset_kb_facts(Module),fail.
pfc_reset_kb_0(Module):- 
  only_is_user_reason((ZF,ZTrigger)),
  clause(Module:spft(P,ZF,ZTrigger),_,Ref),
  nonvar(P),
  once(clause_property(Ref,module(Module)); mfl_module(ZF,Module)),
  must_ex(pfc_reset_mp(Module,P)), 
  ( \+ clause(Module:spft(P,ZF,ZTrigger),_,Ref) -> true;
     (must_ex((clause(_SPFT,_SB,Ref),erase(Ref))))),  %     must_ex((pfc_retract_i_or_warn_1(P);(fail,pfc_retract_i_or_warn(SPFT)))),
  fail.
pfc_reset_kb_0(Module):- 
  clause(Module:spft(P,ZF,ZTrigger),_,Ref),
  nonvar(P),
  once(clause_property(Ref,module(Module)); mfl_module(ZF,Module)),
  must_ex(pfc_reset_mp(Module,P)), 
  ( \+ clause(Module:spft(P,ZF,ZTrigger),_,Ref) -> true;
     (must_ex((clause(_SPFT,_SB,Ref),erase(Ref))))),  %     must_ex((pfc_retract_i_or_warn_1(P);(fail,pfc_retract_i_or_warn(SPFT)))),
  fail.

pfc_reset_kb_0(Module):- pfc_reseted_kb_check(Module),!.


pfc_reseted_kb_check(Module):- with_exact_kb(Module,pfc_reseted_kb_check_0(Module)).

pfc_reseted_kb_check_0(Module):- \+ pfc_database_item(Module,_),!,pfc_trace_msg("Reset DB complete for ~p",[Module]).
pfc_reseted_kb_check_0(Module):- pfc_trace_msg("Couldn't full pfc_reseted_kb_check(~w).~n",[Module]),
  pp_DB,pfc_database_item(Module,T),
  wdmsg_pretty(pfc_database_item(Module,T)),!.
  %pfcWarn("Pfc database [~w] not empty: ~p.~n",[Module,T]),!,
  %pfcError("Pfc database [~w] not empty: ~p.~n",[Module,T]),!.
  
pfc_reset_mp(Module,P):- P \= ( _:-_ ), pfc_retract(Module:P),!.
pfc_reset_mp(Module,P):-
     doall((
     expand_to_hb(P,H,B),
     clause_asserted(Module:H,B,PRef1),
     clause_property(PRef1,module(Module)),
     % show_failure((((lookup_u(Module:P,PRef2),PRef2==PRef1)))),
  (must_ex(pfc_retract_i(Module:P))->true;pfcWarn("Couldn't retract ~p: ~p.~n",[Module,P])),
  sanity(\+ clause_asserted(_H0,_B0,PRef1)))).


% true if there is some Pfc crud still in the database.
pfc_database_item(Module,P):- 
   current_module(Module),
  pfc_database_term(F,A,Type),
  Type\=debug,Type\=setting,
  safe_functor(H,F,A),
  % H \= ~(_),  
  P = (H:-B),
  Module:clause(H,B,Ref),
  clause_property(Ref,module(Module)),
  \+ reserved_body_helper(B).


pfc_retract_i_or_warn(X):- ignore(show_failure((pfc_retract_i_or_warn_1(X) *-> true; pfc_retract_i_or_warn_2(X)))).

pfc_retract_i_or_warn_1(X):- sanity(is_ftNonvar(X)), 
  ((((X=spft(_,_,_), call_u(X), retract_u(X))) *-> true ; retract_u(X))),
  nop((pfc_trace_msg('~NSUCCESS: ~p~n',[retract_u(X)]))).

% pfc_retract_i_or_warn_2(SPFT):- \+ \+ SPFT = spft(_,a,a),!,fail.
% pfc_retract_i_or_warn_2(X):- fail,pfcWarn("Couldn't retract_u ~p.~n",[X]),(debugging_logicmoo(logicmoo(pfc))->rtrace(retract_u(X));true),!.
pfc_retract_i_or_warn_2(X):- pfc_trace_msg("Couldn't retract_i: ~p.~n",[X]),fail.
%pfc_retract_i_or_warn_2(X):- pfcWarn("Couldn't retract_i: ~p.~n",[X]),!.




%   File   : pfcdebug.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Author :  Dave Matuszek, dave@prc.unisys.com
%   Updated:
%   Purpose: provides predicates for examining the database and debugginh
%   for Pfc.

%:- pfc_set_default(baseKB:pfcWarnings(_), baseKB:pfcWarnings(true)).
%  tms is one of {none,local,cycles} and controles the tms alg.
% :- during_boot(pfc_set_default(pfcWarnings(_), pfcWarnings(true))).

%  mpred_fact(P) is true if fact P was asserted into the database via add.

mpred_fact_mp(M,G):- current_predicate(_,M:G),\+ predicate_property(M:G,imported_from(_)),
  mpred_fact(G),ignore((lookup_u(G,Ref),clause_property(Ref,module(MW)))),MW=M.

mpred_fact(P):- mpred_fact(P,true).

%  mpred_fact(P,C) is true if fact P was asserted into the database via
%  add and contdition C is satisfied.  For example, we might do:
%
%   mpred_fact(X,pfc_userFact(X))
%

mpred_fact(P,C):- mpred_fact0(P,C).
mpred_fact(P,C):- compound(P),safe_functor(P,F,2),clause_b(rtSymmetricBinaryPredicate(F)),args_swapped(P,Q),mpred_fact0(Q,C).
mpred_fact(~P,C):- compound(P),safe_functor(P,F,2),clause_b(rtSymmetricBinaryPredicate(F)),args_swapped(P,Q),mpred_fact0(~Q,C).
mpred_fact0(P,C):-
  pfc_get_support(P,_),
  pfc_db_type(P,fact(_FT)),
  call_u_no_bc(C).

%  mpred_facts_in_kb(MM,-ListofPmpred_facts) returns a list of facts added.

mpred_facts(L):- mpred_facts_in_kb(_,L).
mpred_facts_in_kb(MM,L):- mpred_facts_in_kb(MM,_,true,L).

mpred_facts(P,L):- mpred_facts_in_kb(_,P,L).
mpred_facts(KB,P,L):- mpred_facts_in_kb(KB,P,L).
mpred_facts_in_kb(MM,P,L):- mpred_facts_in_kb(MM,P,true,L).

%  mpred_facts_in_kb(MM,Pattern,Condition,-ListofPmpred_facts) returns a list of facts added.

%% mpred_facts_in_kb(MM,+P, ?C, ?L) is semidet.
%
% PFC Facts.
%
mpred_facts_in_kb(MM,P,C,L):- with_exact_kb(MM,setof(P,mpred_fact(P,C),L)).


%% brake(+X) is semidet.
%
% Brake.
%
brake(X):-  X, break.


%
%  predicates providing a simple tracing facility
%

% this is here for upward compat. - should go away eventually.
pfc_trace_op(Add,P):- 
  not_not_ignore_quietly_ex((get_why_uu(Why), !, pfc_trace_op(Add,P,Why))).


pfc_trace_op(Add,P,S):-
   not_not_ignore_quietly_ex((pfc_trace_maybe_print(Add,P,S),
      pfc_trace_maybe_break(Add,P,S))).


pfc_trace_maybe_print(Add,P,S):-
  not_not_ignore_quietly_ex((
  \+ get_pfc_is_tracing(P) -> true;
  (
   ((to_u(S,U),atom(U))
       -> wdmsg_pretty("~NOP: ~p (~p) ~p",[Add,U,P])
        ; wdmsg_pretty("~NOP: ~p (:) ~p~N\tSupported By: ~q",[Add,P,S]))))),!.

to_u(S,U):-S=(U,ax),!.
to_u(S,U):-S=(U,_),!.
to_u(S,U):-S=(U),!.


pfc_trace_maybe_break(Add,P0,_ZS):-
  get_head_term(P0,P),
   (
  \+ call_u(lmcache:pfc_is_spying_pred(P,Add)) -> true;
   (wdmsg_pretty("~NBreaking on ~p(~p)",[Add,P]),
    break)).



pfc_hide(P):-call(P).

pfc_trace:- pfc_trace(_).

pfc_trace(Form0):-  get_head_term(Form0,Form),
  assert_u_no_dep(lmcache:pfc_is_spying_pred(Form,print)).

%% get_pfc_is_tracing(:PRED) is semidet.
%
% PFC If Is A Tracing.
%
get_pfc_is_tracing(_):-!,fail.
get_pfc_is_tracing(Form0):- get_head_term(Form0,Form), t_l:hide_pfc_trace_exec,!,
  \+ \+ ((quietly_ex(call_u(lmcache:pfc_is_spying_pred(Form,print))))).
get_pfc_is_tracing(Form0):- get_head_term(Form0,Form),
  once(t_l:pfc_debug_local ; tracing ; clause_asserted_u(pfc_is_tracing_exec) ;
     call_u(lmcache:pfc_is_spying_pred(Form,print))).


%% pfc_trace(+Form, ?Condition) is semidet.
%
% PFC Trace.
%
pfc_trace(Form0,Condition):- get_head_term(Form0,Form),
  assert_u_no_dep((lmcache:pfc_is_spying_pred(Form,print):- Condition)).

pfc_spy(Form):- pfc_spy(Form,[add,rem],true).

pfc_spy(Form,Modes):- pfc_spy(Form,Modes,true).

pfc_spy(Form0,List,Condition):- is_list(List),!,get_head_term(Form0,Form),
  !,must_maplist(pfc_spy1(Condition,Form),List).

pfc_spy(Form0,Mode,Condition):- get_head_term(Form0,Form),
  pfc_spy1(Condition,Form,Mode).

pfc_spy1(Condition,Form0,Mode):- get_head_term(Form0,Form),
  assert_u_no_dep((lmcache:pfc_is_spying_pred(Form,Mode):- Condition)).

pfc_nospy:- pfc_nospy(_,_,_).

pfc_nospy(Form):- pfc_nospy(Form,_,_).

pfc_nospy(Form0,Mode,Condition):- get_head_term(Form0,Form),
  clause_u(lmcache:pfc_is_spying_pred(Form,Mode), Condition, Ref),
  erase(Ref),
  fail.
pfc_nospy(_,_,_).

pfc_notrace:- pfc_untrace.
pfc_untrace:- pfc_untrace(_).
pfc_untrace(Form0):- get_head_term(Form0,Form), retractall_u(lmcache:pfc_is_spying_pred(Form,print)).


% not_not_ignore_quietly_ex(G):- ignore(quietly(\+ \+ G)).
% not_not_ignore_quietly_ex(G):- ignore( \+ (G)).
not_not_ignore_quietly_ex(G):- notrace(ignore(quietly_ex(\+ \+ G))).

% needed:  pfc_trace_rule(Name)  ...

log_failure(ALL):- quietly_ex((log_failure_red,maybe_pfc_break(ALL),log_failure_red)).

log_failure_red:- quietly(doall((
  show_current_source_location,
  between(1,3,_),
  ansifmt(red,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find log_failure_red in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"),
  ansifmt(yellow,"%%%%%%%%%%%%%%%%%%%%%%%%%%% find log_failure_red in srcs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n")))).

%% with_no_breaks(+P) is semidet.
%
% Dont break even if PFC Test fails
%
:- thread_local(t_l:no_breaks/0).
with_no_breaks(G):- locally_tl(no_breaks,G). 

break_ex:- quietly((log_failure_red,dumpST,log_failure_red)),
  (t_l:no_breaks -> ansifmt(red,"NO__________________DUMP_BREAK/0") ;dbreak).

maybe_pfc_break(Info):- (t_l:no_breaks->true;(debugging(logicmoo(pfc))->dtrace(dmsg_pretty(Info));(dmsg_pretty(Info)))),break_ex.
%maybe_pfc_break(Info):- (t_l:no_breaks->true;(debugging(logicmoo(pfc))->dtrace(dmsg_pretty(Info));(dmsg_pretty(Info)))),break_ex.

% if the correct flag is set, dtrace exection of Pfc
pfc_trace_msg(_):- current_prolog_flag(pfc_pfc_silent,true).
pfc_trace_msg(Info):- not_not_ignore_quietly_ex(((((clause_asserted_u(pfc_is_tracing_exec);tracing)->(show_wdmsg(Info));true)))).
pfc_trace_msg(Format,Args):- not_not_ignore_quietly_ex((((clause_asserted_u(pfc_is_tracing_exec);tracing)-> (show_wdmsg(Format,Args))))),!.
% pfc_trace_msg(Format,Args):- not_not_ignore_quietly_ex((((format_to_message(Format,Args,Info),pfc_trace_msg(Info))))).

show_wdmsg(A,B):- current_prolog_flag(pfc_pfc_silent,true)-> true; wdmsg_pretty(A,B).
show_wdmsg(A):- current_prolog_flag(pfc_pfc_silent,true)-> true; wdmsg_pretty(A).

pfcWarn(Info):- not_not_ignore_quietly_ex((((color_line(red,1), lookup_u(pfcWarnings(true));tracing) ->
  wdmsg_pretty(warn(logicmoo(pfc),Info)) ; pfc_trace_msg('WARNING/PFC:  ~p ',[Info])),
  nop(maybe_pfc_break(Info)))).

pfcWarn(Format,Args):- not_not_ignore_quietly_ex((((format_to_message(Format,Args,Info),pfcWarn(Info))))).

pfcError(Info):- not_not_ignore_quietly_ex(((tracing -> wdmsg_pretty(error(logicmoo(pfc),Info)) ; pfcWarn(error(Info))))).
pfcError(Format,Args):- not_not_ignore_quietly_ex((((format_to_message(Format,Args,Info),pfcError(Info))))).

pfc_pfc_silent(TF):-set_prolog_flag(pfc_pfc_silent,TF).


pfcWatch:- pfc_trace_exec,pfc_pfc_silent(false).
pfc_nowatch:-  pfc_notrace_exec.

pfc_trace_exec:- assert_u_no_dep(pfc_is_tracing_exec),pfc_pfc_silent(false).
pfc_notrace_exec:- retractall_u(pfc_is_tracing_exec).

pfc_trace_all:- pfc_trace_exec,pfc_trace,pfc_set_warnings(true),pfc_pfc_silent(false).
pfc_notrace_all:- pfc_notrace_exec,pfc_notrace,pfc_set_warnings(false).


:- thread_local(t_l:hide_pfc_trace_exec/0).

%% with_pfc_trace_exec( +P) is semidet.
%
% Using Trace exec.
%

% with_pfc_trace_exec(P):- locally_each(-t_l:hide_pfc_trace_exec,locally_each(t_l:pfc_debug_local, must_ex(show_if_debug(P)))).

with_pfc_trace_exec(P):- lookup_u(pfc_is_tracing_exec),!,show_if_debug(P).
with_pfc_trace_exec(P):-
   locally_each(-t_l:hide_pfc_trace_exec,
       locally_each(t_l:pfc_debug_local,
           must_ex(show_if_debug(P)))).


%% with_pfc_trace_exec( +P) is semidet.
%
% Without Trace exec.
%
with_no_pfc_trace_exec(P):-
 with_no_dmsg((
   locally_each(-t_l:pfc_debug_local,locally_each(t_l:hide_pfc_trace_exec, must_ex(/*show_if_debug*/(P)))))).

%% show_if_debug( :GoalA) is semidet.
%
% Show If Debug.
%
:- meta_predicate(show_if_debug(0)).
% show_if_debug(A):- !,show_call(why,A).
show_if_debug(A):-  get_pfc_is_tracing(A) -> show_call(pfc_is_tracing,call_u(A)) ; call_u(A).

:- thread_local(t_l:pfc_debug_local/0).

%% pfc_is_silent is det.
%
% If Is A Silient.
%
pfc_is_silent :- t_l:hide_pfc_trace_exec,!, \+ tracing.
pfc_is_silent :- quietly_ex(( \+ t_l:pfc_debug_local, \+ lookup_u(pfc_is_tracing_exec), \+ lookup_u(lmcache:pfc_is_spying_pred(_,_)),
  current_prolog_flag(debug,false), is_release)) ,!.

oinfo(O):- xlisting((O, - spft, - ( ==> ), - pt , - nt , - bt , - mdefault, - lmcache)).

pfc_must(\+ G):-!, ( \+ call_u(G) -> true ; (log_failure(failed_pfc_test(\+ G)),!,ignore(why_was_true(G)),!,break_ex)).
pfc_must(G):- (call_u(G) -> true ; (ignore(sanity(why_was_true(\+ G))),(log_failure(failed_pfc_test(G))),!,break_ex)).


pfc_load_term(:- module(_,L)):-!, call_u_no_bc(maplist(export,L)).
pfc_load_term(:- TermO):- call_u_no_bc(TermO).
pfc_load_term(TermO):-pfc_ain_object(TermO).


%
%  These control whether or not warnings are printed at all.
%    pfcWarn.
%    nopfcWarn.
%
%  These print a warning message if the flag pfcWarnings is set.
%    pfcWarn(+Message)
%    pfcWarn(+Message,+ListOfArguments)
%

pfcWarn:-
  retractall_u(pfcWarnings(_)),
  assert_u_no_dep(pfcWarnings(true)).

nopfcWarn:-
  retractall_u(pfcWarnings(_)),
  assert_u_no_dep(pfcWarnings(false)).


%%  pfc_set_warnings(+TF) is det.
%   true = sets flag to cause Pfc warning messages to print.
%   false = sets flag to cause Pfc warning messages not to print.
%
pfc_set_warnings(True):-
  retractall_u(pfcWarnings(_)),
  assert_u_no_dep(pfcWarnings(True)).
pfc_set_warnings(false):-
  retractall_u(pfcWarnings(_)).


%%  pfc_trigger_key(+Trigger,-Key)
%
%  Arg1 is a trigger.  Key is the best term to index it on.
%
%  Get a key from the trigger that will be used as the first argument of
%  the trigger base clause that stores the trigger.

pfc_trigger_key(X,X):- var(X), !.
pfc_trigger_key(pt(Key,_),Key).
pfc_trigger_key(pk(Key,_,_),Key).
pfc_trigger_key(nt(Key,_,_),Key).
pfc_trigger_key(Key,Key).

% For chart parser
pfc_trigger_key(chart(word(W),_ZL),W):- !.
pfc_trigger_key(chart(stem([Char1|_ZRest]),_ZL),Char1):- !.
pfc_trigger_key(chart(Concept,_ZL),Concept):- !.
pfc_trigger_key(X,X).


:-module_transparent(pfc_ain/1).
:-module_transparent(pfc_aina/1).
:-module_transparent(pfc_ainz/1).
:-system:import(pfc_ain/1).
:-system:import(pfc_ain/2).

/*
:-module_transparent(pfc_ain/1).
:-module_transparent(pfc_aina/1).
:-module_transparent(pfc_ainz/1).
*/

% :- '$current_source_module'(M),forall(pfc_database_term(F,A,_),(abolish(pfc_lib:F/A),abolish(user:F/A),abolish(M:F/A))).
% :- initialization(ensure_abox(baseKB)).


% % :- set_prolog_flag(pfc_mpred_file,true).
% local_testing

:- set_prolog_flag(expect_mpred_file,never).

:- fixup_exports.

% :- kb_shared(lmcache:pfc_is_spying_pred/2).

 
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.



:- must_ex(pfc_reset_kb_0).

:- defaultAssertMt(M),dynamic((M:current_ooZz/1,M:default_ooZz/1,M:if_mooZz/2)).

:- pfc_trace.
:- pfcWatch.


% this should have been ok
% (if_mooZz(Missing,Create) ==> ((\+ Missing/(Missing\==Create), \+ Create , \+ ~(Create)) ==> Create)).
:- ((pfc_ain((if_mooZz(Missing,Create) ==>
 ( ( \+ Missing/ \+ (variant_u(Missing,Create))) ==> Create))))).

:- pfc_ain((default_ooZz(X) ==> if_mooZz(current_ooZz(_),current_ooZz(X)))).

:- pfc_ain(default_ooZz(booZz)).

:- pfc_test(current_ooZz(booZz)).

% :- pp_DB.

:- (pfc_ain(current_ooZz(fooZz))).

:- pfc_test(\+current_ooZz(booZz)).

:- (pfc_ain(\+ current_ooZz(fooZz))).

:- pfc_test(current_ooZz(booZz)).

:- (pfcWithdraw( default_ooZz(booZz) )).

:- listing([current_ooZz,default_ooZz]).

:- pfc_test( \+current_ooZz(booZz)).

:- pfc_ain(~ current_ooZz(fooZz)).

% :- pp_DB.

:- pfc_test(~current_ooZz(fooZz)).

:- pfc_ain(default_ooZz(booZz)).

:- pfc_test(current_ooZz(booZz)).

:- pfc_reset_kb_0.



/*  

% File used as storage place for all predicates which change as
% the world is run.
%
% props(Obj,height(ObjHt))  == k(height,Obj,ObjHt) == rdf(Obj,height,ObjHt) == height(Obj,ObjHt)
% padd(Obj,height(ObjHt))  == padd(height,Obj,ObjHt,...) == add(QueryForm)
% kretract[all](Obj,height(ObjHt))  == kretract[all](Obj,height,ObjHt) == pretract[all](height,Obj,ObjHt) == del[all](QueryForm)
% keraseall(AnyTerm).
%
%
% Dec 13, 2035
% Douglas Miles
*/
% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/mpred/pfc_kb_ops.pl
%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
hide_this_pfc_kb_ops :- fail, nop( module(pfc_kb_ops,[])).


:- include('pfc_header.pi').


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
arity_no_bc(F,A):- suggest_m(M),clause_b(pfc_prop(M,F,AA,_)),nonvar(AA),A=AA.
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

assert_arity(F,A):- sanity(\+ ((bad_arity(F,A), trace_or_throw_ex(assert_arity(F,A))))), arity_no_bc(F,A),!.
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


%:- endif.
% :- ensure_loaded(library('logicmoo/util/logicmoo_util_bugger.pl')).
%:- ensure_loaded(pfc_lib).
%:- use_module(pfc_type_isa).
%:- use_module(library(util_varnames)).

/*
:- module_transparent retract_mu/1,
         assert_mu/4,
         asserta_mu/2,
         assertz_mu/2,
         assert_u/1,
         asserta_u/1,
         assertz_u/1,
         attempt_side_effect/1.
*/
:- module_transparent(attvar_op/2).


:- meta_predicate 
      pred_head(1,*),
      attempt_side_effect(+),
      call_s(*),
      oncely(*),
      naf(*),
      call_s2(*),
      pfc_update_literal(*,*,0,*),
      pfc_retry(*),
%      pfc_op(?, ?),
      mpred_facts_only(*),
      map_unless(1,:,*,*),      
      is_callable(*),     
%      deducedSimply(*),
      cnstrn0(:,+),
      cnstrn(*),
      cnstrn(+,:),
      attvar_op(*,*),
      % clause_u(+,+,-),
      % call_u(+),
      assertz_mu(+),      
      assertz_mu(+,+),
      if_missing1(*),
      assert_mu(+),
      assert_mu(+,+,+,+),
      ain_minfo_2(1,*),
      ain_minfo(1,*),                                    
%      whenAnd(0,0),
      pfc_call_0(*),
      pfc_bc_only(*),
      pfc_bc_only0(*),
      pfc_prove_neg(*),
      call_u_req(*),
      pfcBC_NoFacts(*).

 :- meta_predicate pfc_get_support_one(0,*).
 :- meta_predicate pfc_get_support_precanonical_plus_more(0,*).
 % :- meta_predicate '__aux_maplist/2_cnstrn0+1'(*,0).
 :- meta_predicate repropagate_1(*).
 :- meta_predicate trigger_supporters_list(0,*).
 :- meta_predicate repropagate_meta_wrapper_rule(*).
 :- meta_predicate repropagate_0(*).


% oncely later will throw an error if there where choice points left over by call
:- meta_predicate(oncely(*)).
:- was_export(oncely/1).


%% oncely( :Goal) is semidet.
%
% Oncely.
%
oncely(:-(Call)):-!,Call,!.
oncely(:-(Call)):-!,call_u(Call).
oncely(Call):-once(Call).
% ================================================
% pfc_op/2
% ================================================

/*
query(t, call_u, G):- call_u(G).
query(_, _, Op, G):- dtrace(call_u(call(Op,G))).
once(A,B,C,D):-trace_or_throw_ex(once(A,B,C,D)).
*/




% ================================================
% is_callable/call_u/naf
% ================================================

%:- was_dynamic(naf/1).
:- meta_predicate(naf(*)).
:- was_export(naf/1).



%% naf( :Goal) is semidet.
%
% Negation-By-Faliure.
%
naf(Goal):- (\+ call_u(Goal)).

:- meta_predicate(is_callable(*)).
:- was_export(is_callable/1).



%% is_callable( :GoalC) is semidet.
%
% If Is A Callable.
%
is_callable(C):-current_predicate(_,C),!.


:- style_check(+singleton).

% TODO READD
%:- foreach(arg(_,isEach(prologMultiValued,prologOrdered,prologNegByFailure,prologPTTP,prologKIF,pfcControlled,ttRelationType,
%     prologHybrid,predCanHaveSingletons,prologDynamic,prologBuiltin,functorIsMacro,prologListValued,prologSingleValued),P),.. )


% TODO ISSUE https://github.com/TeamSPoon/PrologMUD/issues/7

%% check_context_module is semidet.
%
% Check Context Module. (throws if it turns out wrong)
%

check_context_module:- !.
% check_context_module:- is_release,!.
check_context_module:- 
  sanity((source_context_module(M1),clause_b(mtHybrid(M1)))),
  sanity((defaultAssertMt(M2),clause_b(mtHybrid(M2)))).

%% check_real_context_module is semidet.
%
% Check Real Context Module (throws if it turns out wrong)
%
check_real_context_module:- is_release,!.
check_real_context_module:-!.
check_real_context_module:- sanity((context_module(M1),defaultAssertMt(M2),must(M1==M2))).


% ======================= mpred_file('pfcsyntax').	% operator declarations.

:-
 op(1199,fx,('==>')), 
 op(1190,xfx,('::::')),
 op(1180,xfx,('==>')),
 op(1170,xfx,'<==>'),  
 op(1160,xfx,('<-')),
 op(1150,xfx,'=>'),
 op(1140,xfx,'<='),
 op(1130,xfx,'<=>'), 
 op(600,yfx,'&'), 
 op(600,yfx,'v'),
 op(350,xfx,'xor'),
 op(300,fx,'~'),
 op(300,fx,'-').




%% mreq( +G) is semidet.
%
% Mreq.
%
mreq(G):- if_defined(call_u(G),fail).

% ======================= mpred_file('pfccore').	% core of Pfc.

%   File   : pfccore.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Updated: 10/11/87, ...
%            4/2/91 by R. McEntire: added calls to valid_dbref as a
%                                   workaround for the Quintus 3.1
%                            bug in the recorded database.
%   Purpose: core Pfc predicates.

/*

LogicMOO is mixing Mark Stickel's PTTP (prolog techn theorem prover) to create horn clauses that 
 PFC forwards and helps maintain in visible states )  in prolog knowledge baseable.. We use spft/3 to track deductions
Research~wise LogicMOO has a main purpose is to prove that grounded negations (of contrapostives) are of first class in importance in helping
with Wff checking/TMS 
Also alows an inference engine constrain search.. PFC became important since it helps memoize and close off (terminate) transitive closures

*/


%% is_side_effect_disabled is semidet.
%
% If Is A Side Effect Disabled.
%
is_side_effect_disabled:- t_l:no_attempt_side_effects,!.
is_side_effect_disabled:- t_l:side_effect_ok,!,fail.
is_side_effect_disabled:- t_l:noDBaseMODs(_),!.



%% f_to_mfa( +EF, ?R, ?F, ?A) is semidet.
%
% Functor Converted To Module-functor-arity.
%
f_to_mfa(EF,R,F,A):-w_get_fa(EF,F,A),
              (((current_predicate(F/A),functor(P,F,A),predicate_property(_M:P,imported_from(R)))*->true;
              current_predicate(F/A),functor(P,F,A),source_file(R:P,_SF))),
              current_predicate(R:F/A).


%% w_get_fa( +PI, ?F, ?A) is semidet.
%
% W Get Functor-arity.
%
w_get_fa(PI,_F,_A):-is_ftVar(PI),!.
w_get_fa(F/A,F,A):- !.
w_get_fa(PI,PI,_A):- atomic(PI),!.
w_get_fa(PI,F,A):- is_ftCompound(PI),!,functor(PI,F,A).
w_get_fa(Mask,F,A):-get_functor(Mask,F,A).



:- multifile(baseKB:pfc_hook_rescan_files/0).
:- dynamic(baseKB:pfc_hook_rescan_files/0).
:- use_module(library(logicmoo_common)).
%:- was_dynamic(use_presently/0).
% used to annotate a predciate to indicate PFC support


%% is_pfc_action( :TermP) is semidet.
%
% If Is A Managed Predicate Action.
%
is_pfc_action('$VAR'(_)):-!,fail.
is_pfc_action(remove_if_unsupported(_,_)).
is_pfc_action(P):-is_static_predicate(P).

%% pfc_is_builtin( +P) is semidet.
%
% PFC If Is A Builtin.
%
pfc_is_builtin(P):- predicate_property(P,built_in), \+ predicate_property(P,dynamic).
pfc_is_builtin(P):- callable(P),functor(P,F,_),clause_b(prologBuiltin(F)).
pfc_is_builtin(F):- current_predicate(F/A),A>0,functor(P,F,A),pfc_is_builtin(P).

/* UNUSED TODAY

:- use_module(library(mavis)).
:- use_module(library(type_check)).
:- use_module(library(typedef)).
*/



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
add_side_effect(Op,Data0):- current_why(Why),serialize_attvars(Data0,Data),assert(t_l:side_effect_buffer(Op,Data,Why)).


%% attvar_op( +:PRED1, ?Data) is semidet.
%
% Attribute Variable Oper..
%


listing_s(P):-call_s(xlisting(P)).

assert_s(H):- assertz_s(H).
retractall_s(H):- forall(clause_s(H,_,R),erase(R)).
clause_s(H,B):- clause_s(H,B,_).

retract_s(H):- lookup_s(H,R),erase(R).

lookup_s(H):- lookup_s(H,_). 

lookup_s(M:(H:-B),R):- !,clause_s(M:H,B,R).
lookup_s((H:-B),R):-  !,clause_s(H,B,R).
lookup_s(H,R):- clause_s(H,true,R).

lookq_s(X):-lookq_s(X,_Ref).

lookq_s(M:(H:-B),R):- !,clauseq_s(M:H,B,R).
lookq_s((H:-B),R):- !, clauseq_s(H,B,R).
lookq_s(H,R):- clauseq_s(H,true,R).

asserta_s(H):- fix_mp(clause(assert,asserta_s),H,M,H0),asserta_i(M:H0).
assertz_s(H):- fix_mp(clause(assert,assertz_s),H,M,H0),assertz_i(M:H0).
clause_s(H,B,R):- fix_mp(clause(clause,clause_s),H,M,H0),clause_u(M:H0,B,R).
clauseq_s(H,B,R):- fix_mp(clause(clause,clauseq_s),H,M,H0),clause_u(M:H0,B,R),clause(M:HC,BC,R),H0=@=HC,BC=@=B.

call_s(G0):-
  strip_module(G0,_,G),functor(G,F,A),
  (memberchk(F/A,[(',')/2])->
  pfc_METACALL(call_s,G);
  call_s2(G0)).

call_s2(G0):-
  strip_module(G0,WM,G),
  defaultAssertMt(U),  
  must(current_predicate(_,U:G)->(CALL=U:G);(current_predicate(_,WM:G0)->CALL=WM:G0; fail)),
  call(call,(
 '$set_source_module'(S,U),'$module'(M,U),
  setup_call_cleanup( % _each
    ('$set_source_module'(U),'$set_typein_module'(U)),
       call(CALL),
     ('$set_source_module'(S),'$set_typein_module'(M))))).


:- module_transparent(attvar_op/2).

% % attvar_op(Op,Data):- deserialize_attvars(Data,Data0), attvar_op(Op,Data0).
attvar_op(Op,MData):-
 must_det_l((
   strip_module(Op,_,OpA), sanity( \+ atom(OpA)),
   fix_mp(clause(assert,OpA),MData,M,Data),
   add_side_effect(OpA,M:Data),
   quietly(current_prolog_flag(assert_attvars,true)->deserialize_attvars(Data,Data0);Data=Data0))),!,
   attempt_side_effect_mpa(M,OpA,Data0).


:- thread_local(t_l:no_attempt_side_effects/0).

%% attempt_side_effect( +PSE) is semidet.
%
% Physical Side Effect.
%
attempt_side_effect(PSE):- to_physical_mpa(PSE,M,P,A),!,attempt_side_effect_mpa(M,P,A).

to_physical_mpa(PSE,M,P,A):- strip_module(PSE,M,PA),to_physical_pa(PA,P,A).
to_physical_pa(PA,P,A):-PA=..[P,A],!. to_physical_pa(PA,call,PA).


:- meta_predicate(db_op_call(*,1,?)).
db_op_call(_What,How,Data):- call(How,Data).

% attempt_side_effect_mpa(M,OpA,Data):- record_se,!,add_side_effect(OpA,M:Data).
attempt_side_effect_mpa(M,db_op_call(_,retract_u0),Data0):- \+ lookup_u(M:Data0),!,fail.
attempt_side_effect_mpa(M,OpA,Data0):- \+ record_se, is_side_effect_disabled,!,pfcWarn('no_attempt_side_effects ~p',attempt_side_effect_mpa(M,OpA,Data0)).
% @TODO BROKEN phys ical_side_effect_call(M,assertz_i,Data0):- must((compile_aux_clauses(M:Data0))),!.
attempt_side_effect_mpa(M,OpA,Data0):- show_failure(M:call(M:OpA,M:Data0)).


/*

  b_setval(th_asserts,[]),
  call_u(G),
  b_getval(th_asserts,List).

attempt_side_effect_mpa(C) :- 
   b_getval(th_asserts,List),
   b_setval(th_asserts,[C|List]),!.



*/
%% erase_w_attvars( +Data0, ?Ref) is semidet.
%
% Erase W Attribute Variables.
%
erase_w_attvars(Data0,Ref):- attempt_side_effect(erase(Ref)),add_side_effect(erase,Data0).


%% pfc_nochaining( +Goal) is semidet.
%
% PFC No Chaining.
%
pfc_nochaining(Goal):- locally_tl(no_attempt_side_effects,call(Goal)).


%% with_chaining( +Goal) is semidet.
%
% PFC No Chaining.
%
with_chaining(Goal):- locally(- t_l:no_attempt_side_effects,call(Goal)).

% TODO ISSUE https://github.com/TeamSPoon/PrologMUD/issues/7


%% match_source_ref1( :TermARG1) is semidet.
%
% Match Source Ref Secondary Helper.
%
match_source_ref1(ax):-!.
match_source_ref1(mfl4(_VarNameZ,_,_,_)).

%% make_uu_remove( :TermU) is semidet.
%
% Make Uu Remove.
%
make_uu_remove((_,ax)).


%% has_functor( :TermC) is semidet.
%
% Has Functor.
%

% -- % has_functor(_):-!,fail.
has_functor(F/A):-!,is_ftNameArity(F,A),!.
has_functor(C):- (\+ is_ftCompound(C)),!,fail.
has_functor(C):- is_ftCompound(C),\+is_list(C).


%% pfc_each_literal( +P, ?E) is semidet.
%
% PFC Each Literal.
%
pfc_each_literal(P,E):-is_ftNonvar(P),P=(P1,P2),!,(pfc_each_literal(P1,E);pfc_each_literal(P2,E)).
pfc_each_literal(P,P). %:-conjuncts_to_list(P,List),member(E,List).



%% retract_eq_quitely( +H) is semidet.
%
% Retract Using (==/2) (or =@=/2) ) Quitely.
%
retract_eq_quitely(H):- call_u(retract_eq_quitely_f(H)).

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


%% pfc_is_tautology( +Var) is semidet.
%
% PFC If Is A Tautology.
%
% :- module_transparent( (pfc_is_tautology)/1).
pfc_is_tautology(V):- (is_ftVar(V) -> true;(copy_term_nat(V,VC),numbervars(VC),pfc_is_taut(VC))),!.



%% pfc_is_taut( :TermA) is semidet.
%
% PFC If Is A Taut.
%
pfc_is_taut(A):-var(A),!.
pfc_is_taut(A:-B):-!,pfc_is_taut(B==>A).
pfc_is_taut(A<-B):-!,pfc_is_taut(B==>A).
pfc_is_taut(A<==>B):-!,(pfc_is_taut(A==>B);pfc_is_taut(B==>A)).
pfc_is_taut(A==>B):- A==B,!.
pfc_is_taut((B,_)==>A):- pfc_is_assertable(B),pfc_is_taut(A==>B),!.
pfc_is_taut((_,B)==>A):- pfc_is_assertable(B),pfc_is_taut(A==>B),!.
pfc_is_taut(B==>(A,_)):- pfc_is_assertable(A),pfc_is_taut(A==>B),!.
pfc_is_taut(B==>(_,A)):- pfc_is_assertable(A),pfc_is_taut(A==>B),!.


% baseKB:decl_database_hook(Op,Hook):- loop_check_nr(pfc_provide_storage_op(Op,Hook)).


%% is_retract_first( +VALUE1) is semidet.
%
% If Is A Retract First.
%
is_retract_first(one).
is_retract_first(a).


%% pfc_provide_storage_op( +Op, ?I1) is semidet.
%
% Prolog Forward Chaining Provide Storage Oper..
%
pfc_provide_storage_op(Op,(I1,I2)):-!,pfc_provide_storage_op(Op,I1),pfc_provide_storage_op(Op,I2).
pfc_provide_storage_op(Op,(nesc(P))):-!,pfc_provide_storage_op(Op,P).
%pfc_provide_storage_op(change(assert,_AorZ),Fact):- loop_check_nr(ainPreTermExpansion(Fact)).
% pfcRem1 to just get the first
pfc_provide_storage_op(change(retract,OneOrA),FactOrRule):- is_retract_first(OneOrA),!,
            loop_check_nr(pfcWithdraw(FactOrRule)),
  ignore((ground(FactOrRule),pfc_remove(FactOrRule))).
% pfc_remove should be forcefull enough
pfc_provide_storage_op(change(retract,all),FactOrRule):- loop_check_nr(pfc_remove(FactOrRule)),!.
% pfc_provide_storage_op(clause_u,FactOrRule):- is_ftNonvar(FactOrRule),!,loop_check_nr(clause_u(FactOrRule)).


% pfcDatabaseGoal(G):-is_ftCompound(G),get_functor(G,F,A),pfcDatabaseTerm(F/A).




%% pfc_pbody( +H, ?B, ?R, ?BIn, ?WHY) is semidet.
%
% PFC Pbody.
%
%pfc_pbody(H,B,_R,fail,deduced(backchains)):- get_bc_clause(H,_H,B),!.
%pfc_pbody(H,infoF(INFO),R,B,Why):-!,pfc_pbody_f(H,INFO,R,B,Why).
%pfc_pbody(H,B,R,BIn,WHY):- is_true(B),!,BIn=B,get_why(H,H,R,WHY).
%pfc_pbody(H,B,R,B,asserted(R,(H:-B))).


%% get_why( +VALUE1, ?CL, ?R, :TermR) is semidet.
%
% Get Generation Of Proof.
%
get_why(_,CL,R,asserted(R,CL:-U)):- clause_u(spft(CL, U, ax),true),!.
get_why(H,CL,R,deduced(R,WHY)):- (pfc_get_support(H,WH)*->WHY=(H=WH);(pfc_get_support(CL,WH),WHY=(CL=WH))).



%% pfc_pbody_f( +H, ?CL, ?R, ?B, ?WHY) is semidet.
%
% PFC Pbody False.
%
pfc_pbody_f(H,CL,R,B,WHY):- CL=(B==>HH),sub_term_eq(H,HH),!,get_why(H,CL,R,WHY).
pfc_pbody_f(H,CL,R,B,WHY):- CL=(HH<-B),sub_term_eq(H,HH),!,get_why(H,CL,R,WHY).
pfc_pbody_f(H,CL,R,B,WHY):- CL=(HH<==>B),sub_term_eq(H,HH),get_why(H,CL,R,WHY).
pfc_pbody_f(H,CL,R,B,WHY):- CL=(B<==>HH),sub_term_eq(H,HH),!,get_why(H,CL,R,WHY).
pfc_pbody_f(H,CL,R,fail,infoF(CL)):- trace_or_throw_ex(pfc_pbody_f(H,CL,R)).


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
all_different_head_vals_2(H,[A,R|EST]):-get_assertion_head_arg(_,H,E1),E1 ==A,dif(A,E2),get_assertion_head_arg(_,H,E2),\+ contains_var(A,E2),all_different_vals(dif_matrix,[A,E2,R|EST]),!.
all_different_head_vals_2(_H,[A,B|C]):-all_different_vals(dif_matrix,[A,B|C]),!.
all_different_head_vals_2(HB,_):- \+ compound(HB),!.
all_different_head_vals_2(H,[A]):-get_assertion_head_arg(_,H,E1),E1 ==A, H=..[_|ARGS], all_different_vals(dif_matrix,ARGS),!.
all_different_head_vals_2(H,[A]):-get_assertion_head_arg(_,H,E1),E1 ==A,  get_assertion_head_arg(_,H,E2), A\==E2, \+ contains_var(A,E2), dif(A,E2),!.
all_different_head_vals_2(H,[A]):-get_assertion_head_arg(_,H,E1),E1\==A, compound(E1), contains_var(A,E1), all_different_head_vals_2(E1,[A]),!.
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
pfc_rule_hb_0((Ante1=>Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Ante1->Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Ante1*->Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
% pfc_rule_hb_0((Outcome/Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0(rhs([Outcome]),OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
% pfc_rule_hb_0(rhs([OutcomeH|OutcomeT]),OutcomeO,Ante2):- !, pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0({Outcome},OutcomeO,Ante2):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Outcome<-Ante1),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
pfc_rule_hb_0((Ante1 & Outcome),OutcomeO,(Ante1,Ante2)):- (nonvar(Outcome)-> ! ; true), pfc_rule_hb(Outcome,OutcomeO,Ante2).
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
ain_minfo(How,(H<-B)):- !,ain_minfo(How,(H:-infoF(H<-B))),!,get_bc_clause(H,Post),ain_minfo(How,Post),ain_minfo_2(How,(B:-infoF(H<-B))).
ain_minfo(How,(B==>H)):- !,ain_minfo(How,(H:-infoF(B==>H))),!,ain_minfo_2(How,(B:-infoF(B==>H))).
ain_minfo(How,(B<==>H)):- !,ain_minfo(How,(H:-infoF(B<==>H))),!,ain_minfo(How,(B:-infoF(B<==>H))),!.
ain_minfo(How,((A,B):-INFOC)):-pfc_is_info(INFOC),(is_ftNonvar(A);is_ftNonvar(B)),!,ain_minfo(How,((A):-INFOC)),ain_minfo(How,((B):-INFOC)),!.
ain_minfo(How,((A;B):-INFOC)):-pfc_is_info(INFOC),(is_ftNonvar(A);is_ftNonvar(B)),!,ain_minfo(How,((A):-INFOC)),ain_minfo(How,((B):-INFOC)),!.
ain_minfo(How,(-(A):-infoF(C))):-is_ftNonvar(C),is_ftNonvar(A),!,ain_minfo(How,((A):-infoF((C)))). % attvar_op(How,(-(A):-infoF(C))).
ain_minfo(How,(~(A):-infoF(C))):-is_ftNonvar(C),is_ftNonvar(A),!,ain_minfo(How,((A):-infoF((C)))). % attvar_op(How,(-(A):-infoF(C))).
ain_minfo(How,(A:-INFOC)):- is_ftNonvar(INFOC), get_bc_clause(A,AA,INFOCC),A=AA,INFOC==INFOCC,!,attvar_op(How,(A:-INFOC)),!.
ain_minfo(How,bt(_ABOX,H,_)):-!,get_bc_clause(H,Post),attvar_op(How,Post).
ain_minfo(How,nt(H,Test,Body)):-!,attvar_op(How,(H:-fail,nt(H,Test,Body))).
ain_minfo(How,pt(H,Body)):-!,attvar_op(How,(H:-fail,pt(H,Body))).
ain_minfo(How,(A0:-INFOC0)):- pfc_is_info(INFOC0), copy_term_and_varnames((A0:-INFOC0),(A:-INFOC)),!,must((pfc_rewrap_h(A,AA),imploded_copyvars((AA:-INFOC),ALLINFO), attvar_op(How,(ALLINFO)))),!.
%ain_minfo(How,G):-pfc_trace_msg(skipped_add_meta_facts(How,G)).
ain_minfo(_,_).

:- was_export(ain_minfo_2/2).

%% ain_minfo_2( :PRED1How, ?G) is semidet.
%
% Assert If New Metainformation  Extended Helper.
%
:- module_transparent(ain_minfo_2/2).
ain_minfo_2(How,G):-ain_minfo(How,G).


%% pfc_is_info( :TermC) is semidet.
%
% PFC If Is A Info.
%
pfc_is_info((CWC,Info)):- (atom(CWC),is_a_info(CWC));pfc_is_info(Info).
pfc_is_info(pfc_bc_only(C)):-is_ftNonvar(C),!.
pfc_is_info(infoF(C)):-is_ftNonvar(C),!.
pfc_is_info(inherit_above(_,_)).


is_a_info(fail).
is_a_info(CWC):- is_pfc_chained(CWC).

is_pfc_chained(cwc).
is_pfc_chained(awc).
is_pfc_chained(zwc).
is_pfc_chained(fwc).
is_pfc_chained(bwc).
is_pfc_chained(wac).



:- module_transparent(is_ain_clause/2).
is_ain_clause( _, Var):- var(Var),!, fail.
is_ain_clause( M,(:- Body)):- !, is_ain_body(M,Body),!.
is_ain_clause( M,(P:- Body)):- !,(is_ain_head(M,P);is_ain_body(M,Body)),!.
is_ain_clause( M,(P)):- !, is_ain_head(M, P).

:- module_transparent(is_ain_head/2).
is_ain_head(_, P):- var(P),!.
is_ain_head(_,(_,_)):- !.
is_ain_head(_,(_;_)):- !.
is_ain_head(_,not(_)):- !.
is_ain_head(_,\+(_)):- !.
is_ain_head(M, P):- is_ain_body(M, P),!.
is_ain_head(_,==>(_)):- !.
is_ain_head(_,==>(_,_)):- !.
is_ain_head(_,<==>(_,_)):- !.
is_ain_head(_,<==(_)):- !.
is_ain_head(_,<==(_,_)):- !.
is_ain_head(_,'::::'(_,_)):- !.
is_ain_head(baseKB,_).
is_ain_head(_,=>(_)):- !.
is_ain_head(_,=>(_,_)):- !.
is_ain_head(_,_):- get_how_virtualize_file(Lang),!,Lang=heads.

:- module_transparent(is_ain_body/2).
is_ain_body(_, P):- var(P),!,fail.
is_ain_body(M, (P,_)):- !, nonvar(P), is_ain_body(M, P).
is_ain_body(_, CWC):- atom(CWC),  is_pfc_chained(CWC).
is_ain_body(M, P):- functor(P,F,A), \+ \+ pfc_prop(M,F,A,_), !,
  \+ (pfc_prop(M,F,A,Prop), is_pfc_prolog_only_prop(Prop)).
is_ain_body(M, MP):- strip_module(MP,M2,P), M2\==M, !,is_ain_body(M2,P).

is_pfc_prolog_only_prop(prologOnly).
is_pfc_prolog_only_prop(prologBuiltin).


%cwc(Call):- callable(Call),Call.

%:- was_dynamic(not_not/1).

%% pfc_rewrap_h( +A, ?A) is semidet.
%
% PFC Rewrap Head.
%
pfc_rewrap_h(A,A):- is_ftNonvar(A),\+ is_static_predicate(A).
pfc_rewrap_h(A,F):- functor(A,F,_),\+ is_static_predicate(F),!.
%pfc_rewrap_h(A,not_not(A)):-!.


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

%% wac is semidet.
%
% Wac.
%
wac:-true.

awc:-true.
zwc:-true.


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
   WAC==P -> true ; (is_ftCompound(P),get_assertion_head_arg(1,P,E),has_body_atom(WAC,E))),!.

/*
has_body_atom(WAC,P,Rest):- call(WAC==P -> Rest = true ; (is_ftCompound(P),functor(P,F,A),is_atom_body_pfa(WAC,P,F,A,Rest))).
is_atom_body_pfa(WAC,P,F,2,Rest):-get_assertion_head_arg(1,P,E),E==WAC,get_assertion_head_arg(2,P,Rest),!.
is_atom_body_pfa(WAC,P,F,2,Rest):-get_assertion_head_arg(2,P,E),E==WAC,get_assertion_head_arg(1,P,Rest),!.
*/

:- module_transparent( (get_assertion_head_arg)/3).
get_assertion_head_arg(N,P,E):-get_assertion_head_unnegated(P,PP),!,arg(N,PP,E).

same_functors(Head1,Head2):-must_det(get_unnegated_functor(Head1,F1,A1)),must_det(get_unnegated_functor(Head2,F2,A2)),!,F1=F2,A1=A2.


%% pfc_update_literal( +P, ?N, ?Q, ?R) is semidet.
%
% PFC Update Literal.
%
pfc_update_literal(P,N,Q,R):-
    get_assertion_head_arg(N,P,UPDATE),call(replace_arg(P,N,Q_SLOT,Q)),
    must(call_u(Q)),update_value(Q_SLOT,UPDATE,NEW), 
    replace_arg(Q,N,NEW,R).


% spft(5,5,5).

%% update_single_valued_arg(+Module, +P, ?N) is semidet. 
%
% Update Single Valued Argument.
%
:- module_transparent( (update_single_valued_arg)/3).

update_single_valued_arg(M,M:Pred,N):-!,update_single_valued_arg(M,Pred,N).
update_single_valued_arg(_,M:Pred,N):-!,update_single_valued_arg(M,Pred,N).

update_single_valued_arg(world,P,N):- !, update_single_valued_arg(baseKB,P,N).
update_single_valued_arg(M,P,N):- break, \+ clause_b(mtHybrid(M)), trace, clause_b(mtHybrid(M2)),!,
   update_single_valued_arg(M2,P,N).

update_single_valued_arg(M,P,N):- 
  get_assertion_head_arg(N,P,UPDATE),
  is_relative(UPDATE),!,
  dtrace,
  break,
  replace_arg(P,N,OLD,Q),
  must_det_l((clause_u(Q),update_value(OLD,UPDATE,NEW),\+ is_relative(NEW), replace_arg(Q,N,NEW,R))),!,
  update_single_valued_arg(M,R,N).


update_single_valued_arg(M,P,N):- 
 call_u((must_det_l((

  call_u(mtHybrid(M)),
  pfc_type_args \= M,
  pfc_kb_ops \= M,
  get_assertion_head_arg(N,P,UPDATE),
  replace_arg(P,N,Q_SLOT,Q),
  var(Q_SLOT),
  same_functors(P,Q),
  % current_why(U),
  must_det_l((
     % rtrace(attvar_op(assert_if_new,M:spft(P,U,ax))),
     % (call_u(P)->true;(assertz_mu(P))),
     assertz_mu(M,P),
     doall((
          lookup_u(M:Q,E),
          UPDATE \== Q_SLOT,
          erase(E),
          pfc_unfwc1(M:Q))))))))).

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
map_literals(Pred,H,S):- pfcLiteral(H),must(apply(Pred,[H|S])),!.
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

%example pfcVerifyMissing(pfc_isa(I,D), pfc_isa(I,C), ((pfc_isa(I,C), {D==C});-pfc_isa(I,C))). 
%example pfcVerifyMissing(mudColor(I,D), mudColor(I,C), ((mudColor(I,C), {D==C});-mudColor(I,C))). 


%% pfcVerifyMissing( +GC, ?GO, ?GO) is semidet.
%
% Prolog Forward Chaining Verify Missing.
%
pfcVerifyMissing(GC, GO, ((GO, {D==C});\+ GO) ):-  GC=..[F,A|Args],append(Left,[D],Args),append(Left,[C],NewArgs),GO=..[F,A|NewArgs],!.

%example mpred_freeLastArg(pfc_isa(I,C),~(pfc_isa(I,C))):-is_ftNonvar(C),!.
%example mpred_freeLastArg(pfc_isa(I,C),(pfc_isa(I,F),C\=F)):-!.

%% mpred_freeLastArg( +G, ?GG) is semidet.
%
% PFC Free Last Argument.
%
mpred_freeLastArg(G,GG):- G=..[F,A|Args],append(Left,[_],Args),append(Left,[_],NewArgs),GG=..[F,A|NewArgs],!.
mpred_freeLastArg(_G,false).


%% pfc_current_op_support( +VALUE1) is semidet.
%
% PFC Current Oper. Support.
%
pfc_current_op_support((p,p)):-!.


%% pfcVersion( +VALUE1) is semidet.
%
% Prolog Forward Chaining Version.
%
pfcVersion(6.6).


% % :- '$set_source_module'(pfc_kb_ops).

%% correctify_support( +S, ?S) is semidet.
%
% Correctify Support.
%
correctify_support(U,(U,ax)):-var(U),!.
correctify_support((U,U),(U,ax)):-!.
correctify_support((S,T),(S,T)):-!.
correctify_support((U,_UU),(U,ax)):-!.
correctify_support([U],S):-correctify_support(U,S).
correctify_support(U,(U,ax)).


%% clause_asserted_local( :TermABOX) is semidet.
%
% Clause Asserted Local. 
%
clause_asserted_local(MCL):-
  strip_module(MCL,_,CL),
  must(CL=spft(P,Fact,Trigger )),!,
  clause_u(spft(P,Fact,Trigger),true,Ref),
  clause_u(spft(UP,UFact,UTrigger),true,Ref),
  (((UP=@=P,UFact=@=Fact,UTrigger=@=Trigger))).



%% is_already_supported( +P, ?S, ?UU) is semidet.
%
% If Is A Already Supported.
%
is_already_supported(P,(S,T),(S,T)):- clause_asserted_local(spft(P,S,T)),!.
is_already_supported(P,_S,UU):- clause_asserted_local(spft(P,US,UT)),must(get_source_uu(UU)),UU=(US,UT).

% TOO UNSAFE 
% is_already_supported(P,_S):- copy_term_and_varnames(P,PC),sp ftY(PC,_,_),P=@=PC,!.


if_missing1(Q):- pfcLiteral_nv(Q), call_u( \+ ~ Q), if_missing_mask(Q,R,Test),!, lookup_u(R), Test.


%% if_missing_mask( +Q, ?R, ?Test) is semidet.
%
% If Missing Mask.
%

if_missing_mask(M:Q,M:R,M:Test):- nonvar(Q),!,if_missing_mask(Q,R,Test).
if_missing_mask(Q,~Q,\+Q):- \+ is_ftCompound(Q),!.

%if_missing_mask(ISA, ~ ISA, \+ ISA):- functor(ISA,F,1),(F==tSwim;call_u(functorDeclares(F))),!.
if_missing_mask(HB,RO,TestO):- once(pfc_rule_hb(HB,H,B)),B\==true,HB\==H,!,
     if_missing_mask(H,R,TestO),subst(HB,H,R,RO).

if_missing_mask(ISA, ISA, \+ ISA):- functor(ISA, _F,1),!.% (F==tSwim;call_u(functorDeclares(F))),!.

if_missing_mask(Q,R,Test):-
   which_missing_argnum(Q,N),
   if_missing_n_mask(Q,N,R,Test),!.

if_missing_mask(ISA, ~ ISA, \+ ISA).

%% if_missing_n_mask( +Q, ?N, ?R, ?Test) is semidet.
%
% If Missing Mask.
%
if_missing_n_mask(Q,N,R,Test):-
  get_assertion_head_arg(N,Q,Was),
  (nonvar(R)-> (which_missing_argnum(R,RN),get_assertion_head_arg(RN,R,NEW));replace_arg(Q,N,NEW,R)),!,
   Test=dif:dif(Was,NEW).

/*
Old version
if_missing_mask(Q,N,R,dif:dif(Was,NEW)):- 
 must((is_ftNonvar(Q),acyclic_term(Q),acyclic_term(R),functor(Q,F,A),functor(R,F,A))),
  (singleValuedInArg(F,N) -> 
    (get_assertion_head_arg(N,Q,Was),replace_arg(Q,N,NEW,R));
    ((get_assertion_head_arg(N,Q,Was),is_ftNonvar(Was)) -> replace_arg(Q,N,NEW,R);
        (N=A,get_assertion_head_arg(N,Q,Was),replace_arg(Q,N,NEW,R)))).
*/


%% which_missing_argnum( +VALUE1, ?VALUE2) is semidet.
%
% Which Missing Argnum.
%
which_missing_argnum(Q,N):- compound(Q),\+ compound_name_arity(Q,_,0),
 must((acyclic_term(Q),is_ftCompound(Q),get_functor(Q,F,A))),
 F\=t,
  (call_u(singleValuedInArg(F,N)) -> true; which_missing_argnum(Q,F,A,N)).

which_missing_argnum(_,_,1,_):-!,fail.
which_missing_argnum(Q,_F,A,N):- between(A,1,N),get_assertion_head_arg(N,Q,Was),is_ftNonvar(Was).

pfc_run_pause:- asserta(t_l:pfc_run_paused).
pfc_run_resume:- retractall(t_l:pfc_run_paused).

without_running(G):- (t_l:pfc_run_paused->G;locally_tl(pfc_run_pause,G)).

pfc_remove_file_support(_File):- !.
pfc_remove_file_support(File):- 
  forall((filematch(File,File0),freeze(Match,contains_var(File0,Match))),
      forall(lookup_u(spft( W, Match, ax)),forall(retract_u(spft( W, Match, ax)),pfc_remove(W)))).

/*

%% remove_if_unsupported( +Why, ?P) is semidet.
%
% Remove If Unsupported.
%
remove_if_unsupported(Why,P) :- is_ftVar(P),!,trace_or_throw_ex(warn(var_remove_if_unsupported(Why,P))).
remove_if_unsupported(Why,P) :- ((\+ ground(P), P \= (_:-_) , P \= ~(_) ) -> pfc_trace_msg(warn(nonground_remove_if_unsupported(Why,P))) ;true),
   (((pfc_tms_supported(local,P,How),How\=unknown(_)) -> pfc_trace_msg(still_supported(How,Why,local,P)) ; (  fcUndo(Why,P)))),!.
   % pfc_run.

*/

%= pfc_tms_supported(+P,-How) succeeds if P is "supported". What "How" means
%= depends on the TMS mode selected.


%% pfc_tms_supported( +P, ?How) is semidet.
%
% PFC Truth Maintainence/wff Supported.
%
pfc_tms_supported(P,How) :-
  lookup_u(tms(Mode)),
  pfc_tms_supported0(Mode,P,How).



%% pfc_tms_supported( +Mode, ?P, ?How) is semidet.
%
% PFC Truth Maintainence/wff Supported.
%
pfc_tms_supported(Mode,P,How) :- is_ftVar(Mode),get_tms_mode(P,tms(Mode)),!,pfc_tms_supported0(Mode,P,How).
pfc_tms_supported(Mode,P,How) :- pfc_tms_supported0(Mode,P,How).
pfc_tms_supported(How,_P,unknown(How)).

:- module_transparent((pfcWfflist)/2).
:- module_transparent((pfcWff)/3).


%% pfc_tms_supported0( +TmsMode, ?P, ?How) is semidet.
%
% PFC Truth Maintainence/wff Supported Primary Helper.
%
pfc_tms_supported0(local,P,How) :-  pfc_get_support(P,How). % ,sanity(pfc_deep_support(How,S)).
pfc_tms_supported0(cycles,P,How) :-  well_founded(P,How).
pfc_tms_supported0(deep,P,How) :- pfc_deep_support(How,P).

% baseKB:hook_one_minute_timer_tick:- statistics.

%% well_founded( +Fact, ?How) is semidet.
%
% a fact is well founded if it is supported by the user
% or by a set of facts and a rules, all of which are well founded.
%
well_founded(Fact,How) :- pfcWff(Fact,[],How).



%% pfcWff( ?F, ?VALUE2, :TermHow) is semidet.
%
% PFC Well-formed Formula.
%
pfcWff(F,_,How) :-
  % supported by user (pfc_axiom) or an "absent" fact (assumption).
  ((pfc_axiom(F),How =pfc_axiom(F) ); (pfc_assumption(F),How=pfc_assumption(F))),
  !.

pfcWff(F,Descendants,wff(Supporters)) :-
  % first make sure we aren''t in a loop.
  (\+ memberchk(F,Descendants)),
  % find a justification.
  supporters_list(F,Supporters),
  % all of whose members are well founded.
  pfcWfflist(Supporters,[F|Descendants]),
  !.



%% pfcWfflist(+L1, ?L2) is semidet.
%
%  simply maps pfcWff over the list.
%
pfcWfflist([],_).
pfcWfflist([X|Rest],L) :-
  pfcWff(X,L,_How),
  pfcWfflist(Rest,L).


%% pfc_scan_tms( +P) is semidet.
%
% PFC Scan Truth Maintainence/wff.
%
pfc_scan_tms(P):-pfc_get_support(P,(S,SS)),
  (S==SS-> true;
   once((pfc_deep_support(_How,P)->true;
     (pfc_trace_msg(warn(now_maybe_unsupported(pfc_get_support(P,(S,SS)),fail))))))).


%% user_atom( +U) is semidet.
%
% User Atom.
%
user_atom(mfl4(_VarNameZ,_,_,_)):-!.
user_atom(ax).
user_atom(s(_)).


%% pfc_deep_support( +How, ?M) is semidet.
%
% PFC Deep Support.
%
pfc_deep_support(_How,unbound):-!,fail.
pfc_deep_support(How,M):-loop_check(pfc_deep_support0(How,M),fail).


%% pfc_deep_support0( +U, ?U) is semidet.
%
% PFC Deep Support Primary Helper.
%
pfc_deep_support0(user_atom(U),(U,ax)):-user_atom(U),!.
pfc_deep_support0(How,(A==>_)):-!,pfc_deep_support(How,A).
pfc_deep_support0(pt(HowA,HowB),pt(A,B)):-!,pfc_deep_support(HowA,A),pfc_deep_support(HowB,B).
pfc_deep_support0(HowA->HowB,(A->B)):-!,pfc_deep_support(HowA,A),pfc_deep_support(HowB,B).
pfc_deep_support0(HowA/HowB,(A/B)):-!,pfc_deep_support(HowA,A),pfc_deep_support(HowB,B).
pfc_deep_support0((HowA,HowB),(A,B)):-!,pfc_deep_support(HowA,A),pfc_deep_support(HowB,B).
pfc_deep_support0(How,rhs(P)):-!,maplist(pfc_deep_support,How,P).
pfc_deep_support0(pfc_call_only_facts(\+ P),\+ call_u(P)):-!,pfc_call_only_facts(\+ P).
pfc_deep_support0(pfc_call_only_facts(P),call_u(P)):-!,pfc_call_only_facts(P).
pfc_deep_support0(pfc_call_only_facts(P),{P}):-!,pfc_call_only_facts(P).
pfc_deep_support0(S==>How,P):-pfc_get_support(P,S),pfc_deep_support(How,S),!.
pfc_deep_support0(pfc_call_only_facts(\+(P)),\+(P)):-!, pfc_call_only_facts(\+(P)).
pfc_deep_support0(user_atom(P),P):-user_atom(P),!.
pfc_deep_support0(pfc_call_only_facts((P)),P):-pfc_call_only_facts(P).


%% pfc_get_support_precanonical_plus_more( +P, ?Sup) is semidet.
%
% PFC Get Support Precanonical Plus More.
%
pfc_get_support_precanonical_plus_more(P,Sup):- 
  pfc_get_support_one(P,Sup)*->true;
  ((fully_expand(pfc_get_support_precanonical_plus_more,P,PE),!,
    P\=@=PE,pfc_get_support_one(PE,Sup))).

%% pfc_get_support_one( +P, ?Sup) is semidet.
%
% PFC Get Support One.
%
pfc_get_support_one(P,Sup):- pfc_get_support(P,Sup)*->true;
  (pfc_get_support_via_clause_db(P,Sup)*->true;
     pfc_get_support_via_sentence(P,Sup)).


%% pfc_get_support_via_sentence( +Var, ?VALUE2) is semidet.
%
% PFC Get Support Via Sentence.
%
pfc_get_support_via_sentence(Var,_):-is_ftVar(Var),!,fail.
pfc_get_support_via_sentence((A,B),(FC,TC)):-!, pfc_get_support_precanonical_plus_more(A,(FA,TA)),pfc_get_support_precanonical_plus_more(B,(FB,TB)),conjoin(FA,FB,FC),conjoin(TA,TB,TC).
pfc_get_support_via_sentence(true,g):-!.
pfc_get_support_via_sentence(G,call_u(G)):- call_u(G).



%% pfc_get_support_via_clause_db( :TermP, ?OUT) is semidet.
%
% PFC Get Support Via Clause Database.
%
pfc_get_support_via_clause_db(\+ P,OUT):- pfc_get_support_via_clause_db(~(P),OUT).
pfc_get_support_via_clause_db(\+ P,(naf(g),g)):- !, predicate_property(P,number_of_clauses(_)),\+ clause(P,_Body).
pfc_get_support_via_clause_db(P,OUT):- predicate_property(P,number_of_clauses(N)),N>0,
   clause_u(P,Body),(Body==true->Sup=(g);
    (support_ok_via_clause_body(P),pfc_get_support_precanonical_plus_more(Body,Sup))),
   OUT=(Sup,g).



%% support_ok_via_clause_body( +H) is semidet.
%
% Support Ok Via Clause Body.
%
support_ok_via_clause_body(_H):-!,fail.
support_ok_via_clause_body(H):- get_functor(H,F,A),support_ok_via_clause_body(H,F,A).


%% support_ok_via_clause_body( +VALUE1, ?F, ?VALUE3) is semidet.
%
% Support Ok Via Clause Body.
%
support_ok_via_clause_body(_,(\+),1):-!,fail.
support_ok_via_clause_body(_,F,_):- lookup_u(rtArgsVerbatum(F)),!,fail.
support_ok_via_clause_body(H,F,A):- should_call_for_facts(H,F,A).




%% pfc_get_support_precanonical( +F, ?Sup) is semidet.
%
% PFC Get Support Precanonical.
%
pfc_get_support_precanonical(F,Sup):-fully_expand(pfc_get_support_precanonical,F,P),pfc_get_support(P,Sup).

%% spft_precanonical( +F, ?SF, ?ST) is semidet.
%
% Spft Precanonical.
%

spft_precanonical(F,SF,ST):- fully_expand(spft_precanonical,F,P),!,pfc_get_support(P,(SF,ST)).


%% trigger_supporters_list( +U, :TermARG2) is semidet.
%
% Trigger Supports Functor (list Version).
%
trigger_supporters_list(U,[]) :- match_source_ref1(U),!.
trigger_supporters_list(U,[]) :- atom(U),!.

trigger_supporters_list(Trigger,[Fact|MoreFacts]) :-
  pfc_get_support_precanonical_plus_more(Trigger,(Fact,AnotherTrigger)),
  must(trigger_supporters_list(AnotherTrigger,MoreFacts)).

pfc_retry(G):- fail; quietly(G).


%% { ?G} is semidet.
%
% an escape construct for bypassing the FOL''s salient body goals. 
% 
%
:- meta_predicate('{}'(*)).
:- module_transparent( ({})/1).
'{}'(G):- call_u(G).
:- sexport(({})/1).

%% neg_in_code( +G) is semidet.
%
% Negated In Code.
%
:- meta_predicate neg_in_code(*).
:- export(neg_in_code/1).
neg_in_code(G):- no_repeats(loop_check(neg_in_code0(G))).

:- kb_shared(baseKB:proven_neg/1).

:- meta_predicate neg_in_code0(*).
:- export(neg_in_code0/1).
/*
neg_in_code0(G):- cwc, loop_check(proven_neg(G)).
neg_in_code0(G):- cwc, var(G),!,loop_check(lookup_u(~ G)).
neg_in_code0(call_u(G)):- !,neg_in_code0(G).
neg_in_code0(~(G)):- nonvar(G),!,  \+ loop_check(~G) ,!.
neg_in_code0(G):-  is_ftNonvar(G), a(prologSingleValued,G),
      must((if_missing_mask(G,R,Test),nonvar(R),nonvar(Test))),call_u(R),!,call_u(Test).
neg_in_code0(G):- cwc, clause(~G,Call)*-> call_u(Call).
*/
neg_in_code0(G):- loop_check(neg_may_naf(G)), \+ loop_check(G),!.
% neg_in_code0(_:G):-!,baseKB:neg_in_code0(G).


:- meta_predicate neg_may_naf(*).
:- module_transparent(neg_may_naf/1).
:- export(neg_may_naf/1).

%% neg_may_naf( :GoalP) is semidet.
%
% Negated May Negation-by-faliure.
%
neg_may_naf(P):- pfc_non_neg_literal(P),get_functor(P,F),clause_u(prologNegByFailure(F),true),!.
neg_may_naf(P):- is_ftCompound(P),is_never_pfc(P).


%% call_u_req( +G) is semidet.
%
% Req.
%
call_u_req(G):- loop_check(pfc_call_0(G),fail).


%% pfc_call_only_facts(:Fact) is nondet.
%% pfc_call_only_facts(+Why,:Fact) is nondet.
%
% PFC Call Only Facts.
%
% is true iff Fact is a fact available for forward chaining.
%
% Note that this has the side effect [maybe] of catching unsupported facts and
% assigning them support from God. (g,ax)
%
pfc_call_only_facts(_Why,Clause):- pfc_call_only_facts(Clause).
pfc_call_only_facts(Clause) :-  strip_module(Clause,_,ClauseF), on_x_debug(no_repeats(loop_check(pfc_call_0(ClauseF),fail))). 


%% pfc_call_0( +Var) is semidet.
%
% PFC call  Primary Helper.
%
pfc_call_0(Var):-is_ftVar(Var),!,pfc_call_with_no_triggers(Var).
pfc_call_0(M):-fixed_negations(M,O),!,pfc_call_0(O).
pfc_call_0(U:X):-U==user,!,pfc_call_0(X).
pfc_call_0(t(A,B)):-(atom(A)->true;(no_repeats(arity_no_bc(A,1)),atom(A))),ABC=..[A,B],pfc_call_0(ABC).
pfc_call_0(isa(B,A)):-(atom(A)->true;(call_u(tCol(A)),atom(A))),ABC=..[A,B],pfc_call_0(ABC).
%pfc_call_0(t(A,B)):-!,(atom(A)->true;(no_repeats(arity_no_bc(A,1)),atom(A))),ABC=..[A,B],pfc_call_0(ABC).
pfc_call_0(t(A,B,C)):-!,(atom(A)->true;(no_repeats(arity_no_bc(A,2)),atom(A))),ABC=..[A,B,C],pfc_call_0(ABC).
pfc_call_0(t(A,B,C,D)):-!,(atom(A)->true;(no_repeats(arity_no_bc(A,3)),atom(A))),ABC=..[A,B,C,D],pfc_call_0(ABC).
pfc_call_0(t(A,B,C,D,E)):-!,(atom(A)->true;(no_repeats(arity_no_bc(A,4)),atom(A))),ABC=..[A,B,C,D,E],pfc_call_0(ABC).
pfc_call_0((C1,C2)):-!,pfc_call_0(C1),pfc_call_0(C2).
pfc_call_0((C1;C2)):-!,(pfc_call_0(C1);pfc_call_0(C2)).
pfc_call_0((C1->C2;C3)):-!,(pfc_call_0(C1)->pfc_call_0(C2);pfc_call_0(C3)).
pfc_call_0((C1*->C2;C3)):-!,(pfc_call_0(C1)*->pfc_call_0(C2);pfc_call_0(C3)).
pfc_call_0((C1->C2)):-!,(pfc_call_0(C1)->pfc_call_0(C2)).
pfc_call_0((C1*->C2)):-!,(pfc_call_0(C1)*->pfc_call_0(C2)).
pfc_call_0(call(X)):- !, pfc_call_0(X).
pfc_call_0(call_u(X)):- !, pfc_call_0(X).
pfc_call_0(\+(X)):- !, \+ pfc_call_0(X).
pfc_call_0(call_u(X)):- !, pfc_call_0(X).
pfc_call_0(clause(H,B,Ref)):-!,clause_u(H,B,Ref).
pfc_call_0(clause(H,B)):-!,clause_u(H,B).
pfc_call_0(clause(HB)):-expand_to_hb(HB,H,B),!,clause_u(H,B).
pfc_call_0(asserta(X)):- !, pfc_aina(X).
pfc_call_0(assertz(X)):- !, pfc_ainz(X).
pfc_call_0(assert(X)):- !, pfc_ain(X).
pfc_call_0(retract(X)):- !, pfc_prolog_retract(X).
pfc_call_0(retractall(X)):- !, pfc_prolog_retractall(X).

% TODO: test removal
%pfc_call_0(prologHybrid(H)):-get_functor(H,F),!,isa_asserted(F,prologHybrid).

pfc_call_0((H)):- !, call(H).

pfc_call_0((H)):- is_static_predicate(H),!,call(H).
pfc_call_0((H)):- is_static_predicate(H),!,show_pred_info(H),dtrace(pfc_call_0((H))).

%pfc_call_0(HB):-quietly((full_transform_warn_if_changed(pfc_call_0,HB,HHBB))),!,pfc_call_0(HHBB).
pfc_call_0(H):- !, locally_tl(infAssertedOnly(H),call_u(H)).
%pfc_call_0(argIsa(pfc_isa,2,pfc_isa/2)):-  trace_or_throw_ex(pfc_call_0(argIsa(pfc_isa,2,pfc_isa/2))),!,fail.
% TODO: test removal
% pfc_call_0(isa(H,B)):-!,isa_asserted(H,B).



pfc_call_0(M:P):-!,sanity(nonvar(P)),functor(P,F,_),pfc_call_1(M,P,F).
pfc_call_0(G):- strip_module(G,M,P),sanity(nonvar(P)),functor(P,F,_),pfc_call_1(M,P,F).



%% pfc_call_1( +VALUE1, ?G, ?VALUE3) is semidet.
%
% PFC call  Secondary Helper.
%
pfc_call_1(_,G,_):- is_side_effect_disabled,!,pfc_call_with_no_triggers(G).

pfc_call_1(M,G,F):- sanity(\+  is_side_effect_disabled),
               (ground(G); \+ current_predicate(_,M:G) ; \+ (predicate_property(M:G,number_of_clauses(CC)),CC>1)), 
    
                ignore((loop_check(call_with_bc_triggers(M:G)),maybeSupport(G,(g,ax)),fail)),
                 \+ current_predicate(F,M:G),\+ current_predicate(_,_:G),
                 doall(show_call(predicate_property(_UM:G,_PP))),
                 debug_logicmoo(logicmoo(_)),
                 fail,
                 %TODO remove this failure
                 must(show_call(kb_shared(M:G))),
                 kb_shared(M:G),!,fail.
pfc_call_1(_,G,_):- pfc_call_with_no_triggers(G).


:- thread_local t_l:infBackChainPrevented/1.


%% call_with_bc_triggers( +MP) is semidet.
%
% Call Using Backchaining Triggers.
%
call_with_bc_triggers(MP) :- strip_module(MP,_,P), functor(P,F,A), \+ t_l:infBackChainPrevented(F/A), 
  lookup_u(bt(P,Trigger)),
  no_repeats(pfc_get_support(bt(P,Trigger),S)),
  once(no_side_effects(P)),
  locally_tl(infBackChainPrevented(F/A),pfc_eval_lhs(Trigger,S)).


%% pfc_call_with_no_triggers( +Clause) is semidet.
%
% PFC Call Using No Triggers.
%
pfc_call_with_no_triggers(Clause) :-  strip_module(Clause,_,F),
  %= this (is_ftVar(F)) is probably not advisable due to extreme inefficiency.
  (is_ftVar(F)    ->  mpred_facts_and_universe(F) ;
     pfc_call_with_no_triggers_bound(F)).


%% pfc_call_with_no_triggers_bound( +F) is semidet.
%
% PFC Call Using No Triggers Bound.
%
pfc_call_with_no_triggers_bound(F):- pfc_call_with_no_triggers_uncaugth(F).

%% pfc_call_with_no_triggers_uncaugth( +Clause) is semidet.
%
% PFC Call Using No Triggers Uncaugth.
%
pfc_call_with_no_triggers_uncaugth(Clause) :-  strip_module(Clause,_,F),
  show_failure(pfc_call_with_no_triggers_bound,no_side_effects(F)),
  (\+ current_predicate(_,F) -> fail;call_u(F)).
  %= we check for system predicates as well.
  %has_cl(F) -> (clause_u(F,Condition),(Condition==true->true;call_u(Condition)));
  %call_u(F).


%% pfc_bc_only( +M) is semidet.
%
% PFC Backchaining Only.
%

%pfc_bc_only(G):- !,defaultAssertMt(W), loop_check(pfc_BC_w_cache(W,G)).
%pfc_bc_only(M:G):- !, loop_check(with_umt(M,pfc_bc_only0(G))).
pfc_bc_only(G):- no_repeats(loop_check(pfc_bc_only0(G))).

%% pfc_bc_only( +M) is semidet.
%
% PFC Backchaining + FACTS + Inheritance.
%
pfc_bc_and_with_pfc(G):- no_repeats(loop_check(pfc_bc_and_with_pfc_0(G))).

pfc_bc_and_with_pfc_0(G):- pfc_call_only_facts(G). % was missing
pfc_bc_and_with_pfc_0(G):- pfc_bc_only0(G).
pfc_bc_and_with_pfc_0(G):- strip_module(G,M,P),inherit_above(M,P).




% % :- '$set_source_module'(pfc_kb_ops).

%% pfc_bc_only0( +G) is semidet.
%
% PFC Backchaining Only Primary Helper.
%
pfc_bc_only0(G):- pfc_unnegate(G,Pos),!, show_call(why,\+ pfc_bc_only(Pos)).
% pfc_bc_only0(G):- pfcBC_NoFacts(G).
pfc_bc_only0(G):- pfc_BC_w_cache(G,G).

% pfc_bc_only0(G):- pfc_call_only_facts(G).

%%
%= pfcBC_NoFacts(F) is true iff F is a fact available for backward chaining ONLY.
%= Note that this has the side effect of catching unsupported facts and
%= assigning them support from God.
%= this Predicate should hide Facts from pfc_bc_only/1
%%

%% pfcBC_NoFacts( +F) is semidet.
%
% Prolog Forward Chaining Backtackable Class No Facts.
%
pfcBC_NoFacts(F):- pfcBC_NoFacts_TRY(F)*-> true ; (pfc_slow_search,pfcBC_Cache(F)).


%% pfc_slow_search is semidet.
%
% PFC Slow Search.
%
pfc_slow_search.


/*
%% ruleBackward( +R, ?Condition) is semidet.
%
% Rule Backward.
%
ruleBackward(R,Condition):- call_u(( ruleBackward0(R,Condition),functor(Condition,F,_),
  \+ consequent_arg(_,v(call_u_no_bc,call,call_u),F))).
%ruleBackward0(F,Condition):-clause_u(F,Condition),\+ (is_true(Condition);pfc_is_info(Condition)).

%% ruleBackward0( +F, ?Condition) is semidet.
%
% Rule Backward Primary Helper.
%
ruleBackward0(F,Condition):- call_u((  '<-'(F,Condition),\+ (is_true(Condition);pfc_is_info(Condition)) )).

%{X}:-dmsg_pretty(legacy({X})),call_u(X).
*/


%% pfcBC_NoFacts_TRY( +F) is semidet.
%
% Prolog Forward Chaining Backtackable Class No Facts Try.
%


pfcBC_NoFacts_TRY(F) :- no_repeats(ruleBackward(F,Condition,Support)),
  % neck(F),
  copy_term((Condition,Support),(CCondition,SupportC)),
  no_repeats(F,call_u(Condition)),  
  maybe_support_bt(F,CCondition,SupportC).

maybe_support_bt(P,_,_):-pfc_ignored(P),!.
maybe_support_bt(F,Condition,Support):-  
  doall((no_repeats(Why,call_u(bt(F,pt(A,Why)))) *-> pfc_add_support_fast(F,(A,Why)))),
  doall((no_repeats(Why,call_u(bt(F,Why))) *-> pfc_add_support_fast(F,(bt(F,Why),Support)))),
  ignore((maybeSupport(F,(Condition,Support)))).

:- meta_predicate pfcWhy_all(*).
pfcWhy_all(Call):- !,
      call_u(Call),
      doall((
        lookup_u(Call),
        ignore(show_failure(pfcWhy(Call))),
        dmsg_pretty(result=Call),nl)),
   forall(Call,ignore(show_failure(pfcWhy(Call)))).

pfcWhy_all(Call):-
      doall((
        call_u(Call),
        ignore(show_failure(pfcWhy(Call))),
        dmsg_pretty(result=Call),nl)).



%% pfcBC_Cache( +F) is semidet.
%
% Prolog Forward Chaining Backtackable Class Cache.
%
pfcBC_Cache(F) :- pfc_call_only_facts(pfcBC_Cache,F),
   ignore((ground(F),( (\+pfc_call_0(F)), maybeSupport(F,(g,ax))))).



%% maybeSupport( +P, ?VALUE2) is semidet.
%
% Maybe Support.
%
maybeSupport(P,_):-pfc_ignored(P),!.
maybeSupport(P,S):- fail, ( \+ ground(P)-> true;
  (predicate_property(P,dynamic)->pfc_post(P,S);true)).

maybeSupport(P,S):- 
   pfc_add_support_fast(P,S),
   maybeMaybeAdd(P,S).
 
maybeMaybeAdd(P,_):- \+ predicate_property(P,dynamic),!.
maybeMaybeAdd(P,_):- \+ \+ clause_u(P,true),!.
maybeMaybeAdd(P,S):- 
 locally_tl(assert_to(a),
    assert_u_confirmed_was_missing(P)),
   pfc_trace_op(add,P,S),
   pfc_enqueue(P,S).


%% pfc_ignored( :TermC) is semidet.
%
% PFC Ignored.
%
pfc_ignored(argIsa(F, A, argIsaFn(F, A))).
pfc_ignored(genls(A,A)).
pfc_ignored(isa(tCol,tCol)).
%pfc_ignored(isa(W,tCol)):-mreq(baseKB:hasInstance_dyn(tCol,W)).
pfc_ignored(isa(W,_)):-is_ftCompound(W),call_u(isa(W,meta_argtypes)).
pfc_ignored(C):-clause_safe(C,true). 
pfc_ignored(isa(_,Atom)):-atom(Atom),atom_concat(ft,_,Atom),!.
pfc_ignored(isa(_,argIsaFn(_, _))).



%% has_cl( +H) is semidet.
%
% Has Clause.
%
has_cl(H):-predicate_property(H,number_of_clauses(_)).

% an action is undoable if there exists a method for undoing it.


%% pfc_negation_w_neg( +P, ?NF) is semidet.
%
% PFC Negation W Negated.
%
pfc_negation_w_neg(~(P),P):-is_ftNonvar(P),!.
pfc_negation_w_neg(P,NF):-pfc_nf1_negation(P,NF).


%% hook_one_minute_timer_tick is semidet.
%
% Hook To [baseKB:hook_one_minute_timer_tick/0] For Module Mpred_pfc.
% Hook One Minute Timer Tick.
%
baseKB:hook_one_minute_timer_tick:-pfc_cleanup.


%% pfc_cleanup is semidet.
%
% PFC Cleanup.
%
pfc_cleanup:- forall((no_repeats(F-A,(call_u(pfc_prop(M,F,A,pfcRHS)),A>1))),pfc_cleanup(M,F,A)).


%% pfc_cleanup(M, +F, ?A) is semidet.
%
% PFC Cleanup.
%
pfc_cleanup(M,F,A):-functor(P,F,A),predicate_property(P,dynamic)->pfc_cleanup_0(M,P);true.


%% pfc_cleanup_0(M, +P) is semidet.
%
% PFC cleanup  Primary Helper.
%
pfc_cleanup_0(M,P):- findall(P-B-Ref,M:clause(P,B,Ref),L),
  M:forall(member(P-B-Ref,L),erase_w_attvars(clause(P,B,Ref),Ref)),forall(member(P-B-Ref,L),M:attvar_op(db_op_call(assertz,assertz_if_new),((P:-B)))).

% :-debug.
%isInstFn(A):-!,trace_or_throw_ex(isInstFn(A)).

%= pfc_unnegate(N,P) is true if N is a negated term and P is the term
%= with the negation operator stripped.

/*
%% pfc_unnegate( +P, ?P) is semidet.
%
% PFC Negation.
%
pfc_unnegate((-P),P).
% pfc_unnegate((~P),P).
pfc_unnegate((\+(P)),P).
*/
/*

%% pfc_negated_literal( +P) is semidet.
%
% PFC Negated Literal.
%
pfc_negated_literal(P):-is_reprop(P),!,fail.
pfc_negated_literal(P):-pfc_negated_literal(P,_).

%% pfc_negated_literal( +P, ?Q) is semidet.
%
% PFC Negated Literal.
%
pfc_negated_literal(P,Q) :- is_ftNonvar(P),
  pfc_unnegate(P,Q),
  pfcLiteral(Q).

*/

%% pfc_is_assertable( +X) is semidet.
%
% PFC If Is A Assertable.
%
pfc_is_assertable(X):- pfcLiteral_nv(X),\+ functor(X,{},_).

%% pfcLiteral_nv( +X) is semidet.
%
% PFC Literal Nv.
%
pfcLiteral_nv(X):-is_ftNonvar(X),pfcLiteral(X).

/*
%% pfcLiteral( +X) is semidet.
%
% PFC Literal.
%
pfcLiteral(X) :- is_reprop(X),!,fail.
pfcLiteral(X) :- cyclic_term(X),!,fail.
pfcLiteral(X) :- atom(X),!.
pfcLiteral(X) :- pfc_negated_literal(X),!.
pfcLiteral(X) :- pfcPositiveLiteral(X),!.
pfcLiteral(X) :- is_ftVar(X),!.

*/

%% is_reprop( +X) is semidet.
%
% If Is A Reprop.
%
is_reprop(X):- compound(X),is_reprop_0(X).

%% is_reprop_0( +X) is semidet.
%
% If Is A reprop  Primary Helper.
%
is_reprop_0(~(X)):-!,is_reprop(X).
is_reprop_0(X):-get_functor(X,repropagate,_).


%% pfc_non_neg_literal( +X) is semidet.
%
% PFC Not Negated Literal.
%
pfc_non_neg_literal(X):- is_reprop(X),!,fail.
pfc_non_neg_literal(X):- atom(X),!.
pfc_non_neg_literal(X):- sanity(stack_check),
    pfcPositiveLiteral(X), X \= ~(_), X \= pfc_prop(_,_,_,_), X \= conflict(_).

% ======================= mpred_file('pfcsupport').	% support maintenance


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

/*
% TODO not called yet
%= pfc_get_trigger_key(+Trigger,-Key)
%=
%= Arg1 is a trigger.  Key is the best term to index it on.

pfc_get_trigger_key(pt(Key,_),Key).
pfc_get_trigger_key(pk(Key,_,_),Key).
pfc_get_trigger_key(nt(Key,_,_),Key).
pfc_get_trigger_key(Key,Key).
*/

/*

the FOL i get from SUMO, CycL, UMBEL and many *non* RDF ontologies out there.. i convert to Datalog..  evidently my conversion process is unique as it preserves semantics most by the book conversions gave up on. 


% TODO not called yet
%=^L
%= Get a key from the trigger that will be used as the first argument of
%= the trigger baseable clause that stores the trigger.
%=
pfc_trigger_key(X,X) :- is_ftVar(X), !.
pfc_trigger_key(chart(word(W),_L),W) :- !.
pfc_trigger_key(chart(stem([Char1|_Rest]),_L),Char1) :- !.
pfc_trigger_key(chart(Concept,_L),Concept) :- !.
pfc_trigger_key(X,X).
*/
% ======================= mpred_file('pfcdb').	% predicates to manipulate database.

%   File   : pfcdb.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Author :  Dave Matuszek, dave@prc.unisys.com
%   Author :  Dan Corpron
%   Updated: 10/11/87, ...
%   Purpose: predicates to manipulate a pfc database (e.g. save,
%	restore, reset, etc).






%% clause_or_call( +H, ?B) is semidet.
%
% Clause Or Call.
%
clause_or_call(M:H,B):-is_ftVar(M),!,no_repeats(M:F/A,(f_to_mfa(H,M,F,A))),M:clause_or_call(H,B).
clause_or_call(isa(I,C),true):-!,call_u(isa_asserted(I,C)).
clause_or_call(genls(I,C),true):-!,on_x_log_throw(call_u(genls(I,C))).
clause_or_call(H,B):- clause(src_edit(_Before,H),B).
clause_or_call(H,B):- predicate_property(H,number_of_clauses(C)),predicate_property(H,number_of_rules(R)),((R*2<C) -> (clause_u(H,B)*->!;fail) ; clause_u(H,B)).
clause_or_call(H,true):- call_u(should_call_for_facts(H)),no_repeats(on_x_log_throw(H)).


% as opposed to simply using clause(H,true).

%% should_call_for_facts( +H) is semidet.
%
% Should Call For Facts.
%
should_call_for_facts(H):- get_functor(H,F,A),call_u(should_call_for_facts(H,F,A)).

%% should_call_for_facts( +VALUE1, ?F, ?VALUE3) is semidet.
%
% Should Call For Facts.
%
should_call_for_facts(_,F,_):- a(prologSideEffects,F),!,fail.
should_call_for_facts(H,_,_):- modulize_head(H,HH), \+ predicate_property(HH,number_of_clauses(_)),!.
should_call_for_facts(_,F,A):- clause_b(pfc_prop(_M,F,A,pfcRHS)),!,fail.
should_call_for_facts(_,F,A):- clause_b(pfc_prop(_M,F,A,pfcMustFC)),!,fail.
should_call_for_facts(_,F,_):- a(prologDynamic,F),!.
should_call_for_facts(_,F,_):- \+ a(pfcControlled,F),!.



%% no_side_effects( +P) is semidet.
%
% No Side Effects.
%
no_side_effects(P):-  (\+ is_side_effect_disabled->true;(get_functor(P,F,_),a(prologSideEffects,F))).


:- was_dynamic(functorIsMacro/1).


%% compute_resolve( +NewerP, ?OlderQ, ?SU, ?SU, ?OlderQ) is semidet.
%
% Compute Resolve.
%
compute_resolve(NewerP,OlderQ,SU,SU,(pfc_blast(OlderQ),pfc_ain(NewerP,S),pfcWithdraw(conflict(NewerP)))):-
  must(correctify_support(SU,S)),
  wdmsg_pretty(compute_resolve(newer(NewerP-S)>older(OlderQ-S))).
compute_resolve(NewerP,OlderQ,S1,[U],Resolve):-compute_resolve(OlderQ,NewerP,[U2],S1,Resolve),match_source_ref1(U),match_source_ref1(U2),!.
compute_resolve(NewerP,OlderQ,SU,S2,(pfc_blast(OlderQ),pfc_ain(NewerP,S1),pfcWithdraw(conflict(NewerP)))):-
  must(correctify_support(SU,S1)),
  wdmsg_pretty(compute_resolve((NewerP-S1)>(OlderQ-S2))).



%% compute_resolve( +NewerP, ?OlderQ, ?Resolve) is semidet.
%
% Compute Resolve.
%
compute_resolve(NewerP,OlderQ,Resolve):-
   supporters_list(NewerP,S1),
   supporters_list(OlderQ,S2),
   compute_resolve(NewerP,OlderQ,S1,S2,Resolve).



%% is_resolved( +C) is semidet.
%
% If Is A Resolved.
%
is_resolved(C):- Why= is_resolved, pfc_call_only_facts(Why,C),\+pfc_call_only_facts(Why,~(C)).
is_resolved(C):- Why= is_resolved, pfc_call_only_facts(Why,~(C)),\+pfc_call_only_facts(Why,C).

:- must(nop(_)).


%% pfc_prove_neg( +G) is semidet.
%
% PFC Prove Negated.
%
pfc_prove_neg(G):-  (dtrace), \+ pfc_bc_only(G), \+ mpred_fact(G).


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
   predicate_property(P,number_of_clauses(NC)),\+ predicate_property(P,number_of_rules(NC)), \+ \+ clause_u(P,true).



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


%% cnstrn( +X) is semidet.
%
% Cnstrn.
%
:- module_transparent(cnstrn/1).
cnstrn(X):-term_variables(X,Vs),maplist(cnstrn0(X),Vs),!.

%% cnstrn( +V, ?X) is semidet.
%
% Cnstrn.
%
:- module_transparent(cnstrn/2).
cnstrn(V,X):-cnstrn0(X,V).

%% cnstrn0( +X, ?V) is semidet.
%
% Cnstrn Primary Helper.
%
:- module_transparent(cnstrn0/2).
cnstrn0(X,V):-when(is_ftNonvar(V),X).


%% rescan_pfc is semidet.
%
% Rescan Prolog Forward Chaining.
%
rescan_pfc:-forall(clause(baseKB:pfc_hook_rescan_files,Body),show_entry(rescan_pfc,Body)).


%% mpred_facts_and_universe( +P) is semidet.
%
% PFC Facts And Universe.
%
mpred_facts_and_universe(P):- (is_ftVar(P)->pred_head_all(P);true),call_u(P). % (meta_wrapper_rule(P)->call_u(P) ; call_u(P)).


%% repropagate( :TermP) is semidet.
%
% Repropagate.
%
repropagate(_):-  check_context_module,fail.
%repropagate(P):-  check_real_context_module,fail.

repropagate(P):-  is_ftVar(P),!.
repropagate(==>P):- !,repropagate(P).
repropagate(P):-  meta_wrapper_rule(P),!,call_u(repropagate_meta_wrapper_rule(P)).
repropagate(P):-  \+ predicate_property(P,_),'$find_predicate'(P,PP),PP\=[],!,forall(member(M:F/A,PP),
                                                          must((functor(Q,F,A),repropagate_1(M:Q)))).
repropagate(F/A):- is_ftNameArity(F,A),!,functor(P,F,A),!,repropagate(P).
repropagate(F/A):- atom(F),is_ftVar(A),!,repropagate(F).

repropagate(P):-  \+ predicate_property(_:P,_),dmsg_pretty(undefined_repropagate(P)),dumpST,dtrace,!,fail.
repropagate(P):-  call_u(repropagate_0(P)).


predicate_to_goal(P,Goal):-atom(P),get_arity(P,F,A),functor(Goal,F,A).
predicate_to_goal(PF/A,Goal):-atom(PF),get_arity(PF,F,A),functor(Goal,F,A).
predicate_to_goal(G,G):-compound(G),!.

%% repropagate_0( +P) is semidet.
%
% repropagate  Primary Helper.
%
repropagate_0(P):- loop_check(call_u(repropagate_1(P)),true).

:- thread_local t_l:is_repropagating/1.


%% repropagate_1( +P) is semidet.
%
% repropagate  Secondary Helper.
%
repropagate_1(P):- is_ftVar(P),!.
repropagate_1(==>P):- !,repropagate_1(P).
repropagate_1(USER:P):- USER==user,!,repropagate_1(P).
%repropagate_1((P/_)):-!,repropagate_1(P).

repropagate_1(P):- call_u(repropagate_2(P)).

:- export(repropagate_2/1).
:- module_transparent(repropagate_2/1).

%% repropagate_2( +P) is semidet.
%
% repropagate  Extended Helper.
%
repropagate_2(P):-
 call_u(doall((no_repeats((mpred_facts_and_universe(P))),
    locally_tl(is_repropagating(P),ignore((once(show_failure(fwd_ok(P))),show_call(mpred_fwc(P)))))))).

% repropagate_meta_wrapper_rule(P==>_):- !, repropagate(P).

%% repropagate_meta_wrapper_rule( +P) is semidet.
%
% Repropagate Meta Wrapper Rule.
%
repropagate_meta_wrapper_rule(P):-repropagate_1(P).


%% fwd_ok( :TermP) is semidet.
%
% Forward Repropigated Ok.
%
fwd_ok(_):-!.
fwd_ok(P):-ground(P),!.
fwd_ok(if_missing1(_,_)).
fwd_ok(idForTest(_,_)).
fwd_ok(clif(_)).
fwd_ok(pfclog(_)).
fwd_ok(X):-compound(X),get_assertion_head_arg(_,X,E),compound(E),functor(E,(:-),_),!.
% fwd_ok(P):-must(ground(P)),!.


%% mpred_facts_only( +P) is semidet.
%
% PFC Facts Only.
%
mpred_facts_only(P):- (is_ftVar(P)->(pred_head_all(P),\+ meta_wrapper_rule(P));true),no_repeats(P).



:- thread_local(t_l:user_abox/1).

% :- ((prolog_load_context(file,F),  prolog_load_context(source,F))-> throw(prolog_load_context(source,F)) ; true). :- include('pfc_header.pi').
:- style_check(+singleton).

% TODO READD
%:- foreach(arg(_,isEach(prologMultiValued,prologOrdered,prologNegByFailure,prologPTTP,prologKIF,pfcControlled,ttRelationType,
%     prologHybrid,predCanHaveSingletons,prologDynamic,prologBuiltin,functorIsMacro,prologListValued,prologSingleValued),P),)

%% get

% =================================================
% ==============  UTILS BEGIN        ==============
% =================================================

%% ruleBackward(+R, ?Condition) is semidet.
%
% Rule Backward.
%
ruleBackward(R,Condition,Support):- ruleBackward0(R,Condition,Support),
  functor(Condition,F,_),\+ arg(_,v(call_u,pfc_bc_only,inherit_above),F).

%% ruleBackward0(+F, ?Condition) is semidet.
%
% Rule Backward Primary Helper.
%
ruleBackward0(F,Condition,Support):- call_u('<-'(FF,Condition)),copy_term('<-'(FF,Condition),Support),FF=F.
%ruleBackward0(F,Condition,(F :- Condition)):- clause_u(F,Condition),\+ (is_true(Condition);pfc_is_info(Condition)).


% ======================= 
% user''s program''s database
% ======================= 


%% assert_mu(+X) is semidet.
%
% Assert For User Code.
%

assert_mu(MH):-  fix_mp(clause(assert,assert_u), MH,M,H),get_unnegated_functor(H,F,A),assert_mu(M,H,F,A).
asserta_mu(MH):- fix_mp(clause(assert,asserta_u),MH,M,H),asserta_mu(M,H).
assertz_mu(MH):- fix_mp(clause(assert,assertz_u),MH,M,H),assertz_mu(M,H).


% :- kb_shared(baseKB:singleValuedInArg/2).
:- thread_local(t_l:assert_to/1).

%% assert_mu(+Module, +Pred, ?Functor, ?Arity) is semidet.
%
% Assert For User Code.
%
assert_mu(M,M2:Pred,F,A):- M == M2,!, assert_mu(M,Pred,F,A).
% maYBE assert_mu(M,(M2:Pred :- B),F,A):- M == M2,!, assert_mu(M,(Pred :- B),F,A).
assert_mu(M,_:Pred,F,A):- dtrace,sanity(\+ is_ftVar(Pred)),!, assert_mu(M,Pred,F,A).
assert_mu(M,(Pred:- (AWC,More)),_,_):- AWC == awc,!,asserta_mu(M,(Pred:- (AWC,More))).
assert_mu(M,(Pred:- (ZWC,More)),_,_):- ZWC == zwc,!,assertz_mu(M,(Pred:- (ZWC,More))).
%assert_mu(M,Pred,F,_):- clause_b(singleValuedInArg(F,SV)),!,must(update_single_valued_arg(M,Pred,SV)),!.
%assert_mu(M,Pred,F,A):- a(prologSingleValued,F),!,must(update_single_valued_arg(M,Pred,A)),!.
assert_mu(M,Pred,F,_):- a(prologOrdered,F),!,assertz_mu(M,Pred).
assert_mu(M,Pred,_,_):- t_l:assert_to(Where),!, (Where = a -> asserta_mu(M,Pred); assertz_mu(M,Pred)).
%assert_mu(M,Pred,_,1):- !, assertz_mu(M,Pred),!.
assert_mu(M,Pred,_,_):- assertz_mu(M,Pred).


:-thread_local(t_l:side_effect_ok/0).


%% assertz_mu(+M, ?X) is semidet.
%
% Assertz Module Unit.
%
%assertz_mu(abox,X):-!,defaultAssertMt(M),!,assertz_mu(M,X).
%assertz_mu(M,X):- check_never_assert(M:X), clause_asserted_u(M:X),!.
% assertz_mu(M,X):- correct_module(M,X,T),T\==M,!,assertz_mu(T,X).
% assertz_mu(_,X):- must(defaultAssertMt(M)),!,must((expire_tabled_list(M:X),show_call(attvar_op(db_op_call(assertz,assertz_i),M:X)))).


assertz_mu(_,X):- check_never_assert(X),fail.
%assertz_mu(M,M2:Pred,F,A):- M == M2,!, assertz_mu(M,Pred,F,A).
%assertz_mu(M,spft(P,mfl4(VarNameZ,KB,F,L),T)):-M\==KB,!,assertz_mu(KB,spft(P,mfl4(VarNameZ,KB,F,L),T)).
assertz_mu(M,X):- strip_module(X,_,P), %sanity(check_never_assert(M:P)), 
    must((expire_tabled_list(M:P),show_failure(attvar_op(db_op_call(assertz,assertz_i),M:P)))).
   %(clause_asserted_u(M:P)-> true; must((expire_tabled_list(M:P),show_failure(attvar_op(db_op_call(assertz,assertz_i),M:P))))).

%% asserta_mu(+M, ?X) is semidet.
%
% Asserta Module Unit.
%
%asserta_mu(abox,X):-!,defaultAssertMt(M),!,asserta_mu(M,X).
% asserta_mu(M,X):- correct_module(M,X,T),T\==M,!,asserta_mu(T,X).
% asserta_mu(_,X):- must(defaultAssertMt(M)),!,must((expire_tabled_list(M:X),show_failure(attvar_op(db_op_call(assertz,assertz_i),M:X)))).

asserta_mu(_,X):- check_never_assert(X),fail.
asserta_mu(M,X):- strip_module(X,_,P),!, %sanity(check_never_assert(M:P)), 
    must((expire_tabled_list(M:P),show_failure(attvar_op(db_op_call(asserta,asserta_i),M:P)))).
   %(clause_asserted_u(M:P)-> true; must((expire_tabled_list(M:P),show_failure(attvar_op(db_op_call(asserta,asserta_i),M:P))))).


%% retract_mu( :TermX) is semidet.
%
% Retract For User Code.
%
% retract_mu(que(X,Y)):-!,show_failure(why,retract_eq_quitely_f(que(X,Y))),must((expire_tabled_list(~(X)))),must((expire_tabled_list((X)))).
retract_mu(H0):- throw_depricated, strip_module(H0,_,H),defaultAssertMt(M),show_if_debug(attvar_op(db_op_call(retract,retract_i),M:H)),!,must((expire_tabled_list(H))).
retract_mu(X):- check_never_retract(X),fail.
retract_mu(~(X)):-!,show_success(why,retract_eq_quitely_f(~(X))),must((expire_tabled_list(~(X)))),must((expire_tabled_list((X)))).
retract_mu((X)):-!,show_success(why,retract_eq_quitely_f((X))),must((expire_tabled_list(~(X)))),must((expire_tabled_list((X)))).
retract_mu(M:(H:-B)):- atom(M),!, clause_u(H,B,R),erase(R).
retract_mu((H:-B)):-!, clause_u(H,B,R),erase(R).
%retract_mu(~(X)):-must(is_ftNonvar(X)),!,retract_eq_quitely_f(~(X)),must((expire_tabled_list(~(X)))),must((expire_tabled_list((X)))).
%retract_mu(hs(X)):-!,retract_eq_quitely_f(hs(X)),must((expire_tabled_list(~(X)))),must((expire_tabled_list((X)))).





:- retractall(t_l:pfc_debug_local).
:- thread_local(t_l:in_rescan_pfc_hook/0).

:- module_transparent(pfc_call_0/1).

 :- meta_predicate update_single_valued_arg(+,+,*).
 :- meta_predicate assert_mu(*,+,*,*).
 :- meta_predicate mpred_facts_and_universe(*).
 :- meta_predicate {*}.
 :- meta_predicate neg_in_code0(*).
 :- meta_predicate repropagate_2(*).
 :- meta_predicate pfc_get_support_via_sentence(*,*).

:- dynamic(infoF/1).



pfc_kb_ops_file.

:- fixup_exports.




/*  
% ===================================================================
% File 'dbase_c_term_expansion'
% Purpose: Emulation of OpenCyc for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface' 1.0.0
% Revision:  $Revision: 1.9 $
% Revised At:   $Date: 2002/06/27 14:13:20 $
% ===================================================================
% File used as storage place for all predicates which change as
% the world is run.
%
% props(Obj,height(ObjHt))  == holds(height,Obj,ObjHt) == rdf(Obj,height,ObjHt) == height(Obj,ObjHt)
% padd(Obj,height(ObjHt))  == padd(height,Obj,ObjHt,...) == add(QueryForm)
% kretract[all](Obj,height(ObjHt))  == kretract[all](Obj,height,ObjHt) == pretract[all](height,Obj,ObjHt) == del[all](QueryForm)
% keraseall(AnyTerm).
%
% when deciding the setting for a pred in file foof.pl
%
%  foom:foo(1):-bar(2).
%
%      we search in this order:  SOURCE:LOADTYPE:PRED
%
% SOURCETYPE
%                  source_file('/dir/foof.pl')
%                  source_module(foom)
%                  source_user(ax)
%                  source_filetype(pl)
%                  source_caller(user)   % module it's being loaded for
%                  (missing)*
% LOADTYPE
%                  consult
%                  assert
%                  (missing)*
%                  
% CLAUSETYPE
%                  rule
%                  fact
%                  directive
%                  (missing)*
%                  
% PRED INDICATOR
%                  
%                  foo(int),
%                  foo/1
%                  foo,
%                  (:-)/2  % neck used
%                  (missing)*
%
%
%
% clause types: (:-)/1, (:-)/2, (=>)/1,  (=>)/2,  (==>)/1,  (==>)/2, (<-)/1,  (<-)/2, (<==>)/2, fact/1
%
*/
% :- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
module_pfc_expansion:- fail, nop(module(pfc_expansion,
          [ a/2,
            acceptable_xform/2,
            additiveOp/1,
            alt_calls/1,
            any_op_to_call_op/2,
            as_is_term/1,as_is_term/1,
            as_list/2,
            cheaply_u/1,
            cheaply_u/1,
            maybe_prepend_mt/3,
            compare_op/4,
            comparitiveOp/1,
            compound_all_open/1,
            conjoin_l/3,
            try_expand_head/3,
            db_expand_0/3,
            db_expand_chain/3,
            db_expand_final/3,
            db_expand_maplist/5,
            db_op_sentence/4,
            db_op_simpler/3,
            db_quf/4,
            db_quf_l/5,
            db_quf_l_0/5,
            default_te/3,
            demodulize/3,
            remodulize/3,
            replaced_module/3,
            fully_expand_into_cache/3,
            do_expand_args/3,
            do_expand_args_l/3,
            do_expand_args_pa/4,
            ex_argIsa/3,
            exact_args/1,
            exact_args0/1,
            expand_isEach_or_fail/2,
            expand_goal_correct_argIsa/2,
            expand_props/3,
            expand_props/4,
            expanded_different/2,
            expanded_different_1/2,
            expanded_different_ic/2,
            %expands_on/2,
            fix_negations/2,
            fixed_negations/2,
            fixed_syntax/2,
            foreach_arg/7,
            from_univ/4,
            fully_expand/2,            
            fully_expand/3,
            fully_expand_clause/3,
            fully_expand_goal/3,
            fully_expand_head/3,
            fully_expand_into_cache/3,
            fully_expand_real/3,
            fully_expand_into_cache/3,
            %full_transform_warn_if_changed_UNUSED/3,
            functor_declares_collectiontype/2,
            functor_declares_instance/2,
            functor_declares_instance_0/2,
            holds_args/2,
            %if_expands_on/3,
            infix_op/2,
            instTypePropsToType/2,
            into_functor_form/3,
            into_functor_form/5,
            into_mpred_form/2,
            into_mpred_form6/6,
            into_mpred_form_ilc/2,
            is_arity_pred/1,
            is_meta_functor/3,
            is_pred_declarer/1,
            is_relation_type/1,
            is_stripped_module/1,
            is_unit/1,
			is_unit_like/1,
                        post_expansion/3,
            is_unit_functor/1,
            listToE/2,
            map_f/2,
            pfc_expand_rule/2,
            should_expand/1,
            must_remodulize/3,
            recommify/2,
            recommify/3,
            reduce_clause/3,
            reduce_clause_from_fwd/3,
            show_doall/1,
            string_to_mws/2,
            simply_functors/3,
            to_reduced_hb/4,
            transform_functor_holds/5,
            transform_holds/3,
            transform_holds_3/3,
            transitive_lc_nr/3,
            translate_args/9,
            translateListOps/8,
            translateOneArg/8,
            was_isa_ex/3,

          pfc_expansion_file/0,
          expand_kif_string/2,
         temp_comp/4,
         get_ruleRewrite/2,
         expand_kif_string_or_fail/3,
         to_predicate_isas/2,
         append_as_first_arg/3,
         try_expand_head/3,
         expand_isEach_or_fail/2,
         % expand_kif_string/3,
         is_elist_functor/1
          
          ])).

:- include('pfc_header.pi').

% :- endif.


:- meta_predicate 
   % pfc_expansion
   cheaply_u(+),
   cheaply_u(+),
   db_expand_maplist(2,*,*,*,*),
   % pfc_expansion
   transitive_lc_nr(2,*,*),
   simply_functors(2,*,*).
          

:- thread_local(t_l:disable_px/0).


:- use_module(library(apply)).
:- use_module(library(logicmoo/attvar_serializer)).

%= :- kb_shared(was_chain_rule/1).
%= :- kb_shared(baseKB:rtReformulatorDirectivePredicate/1).
%= :- kb_shared(props/2).

:- dynamic(baseKB:col_as_isa/1).
:- dynamic(baseKB:col_as_unary/1).

:- kb_shared(baseKB:wid/3).

:- style_check(+singleton).

%% default_te( ?IF, ?VAR, ?VAL) is semidet.
%
% Default Te.
%
default_te(IF,VAR,VAL):-assertz(te_setting(IF,VAR,VAL)).

:- default_te([source_filetype(pl) ],use_te,file_prolog).
:- default_te([source_filetype(pfc) ],use_te,file_pfc).
:- default_te([source_filetype(console) ],use_te,file_prolog).

:- default_te(file_prolog,proccess_directive, proccess_directive).
:- default_te(file_prolog,compile_clause, compile_clause).
:- default_te(file_prolog,rule_neck, (head :- body)).
:- default_te(file_prolog,fact_neck, (head :- true)).

:- default_te(file_pfc, compile_clause, ain).
:- default_te(file_pfc, expand_clause, fully_expand_clause).
:- default_te(file_pfc, proccess_directive, proccess_directive).
:- default_te(file_pfc, fact_neck, (clause <- true)).
:- default_te(file_pfc, rule_neck, (head :- body)).

:- default_te(file_syspreds,isa_detector, always_fail(i,c)).
:- default_te(file_syspreds,isa_holder, c(i)).
:- default_te(file_syspreds,isa_varholder, (t(c,i))).  % was isa(i,c).
:- default_te(file_syspreds,pred_holder, head).  % was isa(i,c).
:- default_te(file_syspreds,pred_varholder,  univ_safe(newhead , [t,pred|args])).
:- default_te(file_syspreds,proccess_directive, proccess_directive).
:- default_te(file_syspreds,compile_clause, compile_clause).
:- default_te(file_syspreds,rule_neck, (head :- body)).
:- default_te(file_syspreds,fact_neck, (clause :- true)).
:- default_te(file_syspreds, expand_clause, (=)).

:- default_te(file_syspreds:pred(*), neck_override, (cwc)).
:- default_te(file_pfc:pred(*), neck_override, (hybrid)).
:- default_te(file_prolog:pred(*), neck_override, (hybrid)).

:- default_te((:-)/1, compile_clause, proccess_directive).
:- default_te((:-)/2, rule_neck, clause).
:- default_te((=>),use_te, file_pfc).
:- default_te((<==>),use_te, file_pfc).
:- default_te((<-),use_te, file_pfc).

/*
% :- directive:  process_directive, call
% fact:  fwc(pfc), bwc(pfc), *cwc(prolog), bwc(pttp), implies(kif), other
% :- rule:  fwc(pfc), bwc(pfc), *cwc(prolog), bwc(pttp), implies(kif), other
% <- rule:   fwc(pfc), *bwc(pfc), cwc(prolog), bwc(pttp), implies(kif), other
% <= rule:   *fwc(pfc), bwc(pfc), cwc(prolog), bwc(pttp), implies(kif), other
% <- fact:   fwc(pfc), *bwc(pfc), cwc(prolog), bwc(pttp), implies(kif), other
% => fact:   *fwc(pfc), bwc(pfc), cwc(prolog), bwc(pttp), implies(kif), other
% loading:  compile_clause, process_directive, assertz, 
% head types: code, *hybrid, safe_functor(outer), holds(outer)
% body types: code, *hybrid, safe_functor(outer), holds(outer)
% isa holder:   isa(i,c), t(c,i),  *c(i).
% isa holder is_ftVar c:   isa(i,c), *t(c,i).
% varpred_head:  *t(P,A,B).
% varpred_body:  *t(P,A,B).
% body types: code, *hybrid, safe_functor(outer), holds(outer)

Interestingly there are three main components I have finally admit to needing despite the fact that using Prolog was to provide these exact components.  
First of all a defaulting system using to shadow (hidden) behind assertions
Axiomatic semantics define the meaning of a command in a program by describing its effect on assertions about the program state.
The assertions are logical statements - predicates with variables, where the variables define the state of the program.
Predicate transformer semantics to combine programming concepts in a compact way, before logic is realized.   
This simplicity makes proving the correctness of programs easier, using Hoare logic.

Axiomatic semantics
Writing in Prolog is actually really easy for a MUD is when X is chosen

%
% Dec 13, 2035
% Douglas Miles
*/

%:-use_module(pfc_lib).
%:-use_module(pfc_type_wff).


% ============================================
% inital a/2 database
% ============================================

% baseKB:hasInstance_dyn(W,SS):-nonvar(W),nonvar(SS),SS=isKappaFn(_,S),nonvar(S),!.


/*
disabled a(T,I):- not(current_predicate(deduce_M/1)),!,baseKB:hasInstance_dyn(T,I).
disabled a(T,I):- !, (mudIsa_motel(I,T) *-> true ; (((atom(I),must(not(baseKB:hasInstance_dyn(T,I)))),fail))).
disabled a(T,I):- rdf_x(I,rdf:type,T).
*/
:- system:op(700,xfx,('univ_safe')).
%% a( ?C, ?I) is nondet.
%
% A.
%

:- meta_predicate a(+,?).
% WANT (but will loop) a(C,I):- !, quietly((atom(C),G  univ_safe  [C,I], no_repeats(call_u(G)))).
a(C,I):- quietly((atom(C),current_predicate(C/1), G  univ_safe  [C,I], no_repeats(lookup_u(G)))).


%=  :- was_export(alt_calls/1).

%= 	 	 

%% alt_calls( +Op) is semidet.
%
% Alt Calls.
%
alt_calls(call).
alt_calls(call_u).
alt_calls(clause_u).
alt_calls(lookup_u).
alt_calls(clause_asserted_i).
alt_calls(t).
alt_calls(is_entailed_u).
alt_calls(call_u).
alt_calls(ireq).



:- meta_predicate compare_op(*,2,?,?).


:- meta_predicate show_doall(0).

%= 	 	 

%% show_doall( :Goal) is semidet.
%
% Show Doall.
%
show_doall(Call):- doall(show_call(why,Call)).


/*
Name               Meaning                            

speed              speed of the runtime code
safety             run-time error checking            

correct         run-time error correction            

compilation-speed  speed of the compilation process   
debug              ease of debugging     


cheaply_u(G):- quickly(quietly(Goal)).

*/

% lookup_u/cheaply_u/call_u/clause_b

cheaply_u(rtArgsVerbatum(G)):- !, clause_b(rtArgsVerbatum(G)).
cheaply_u(functorDeclares(F)):-!, clause_b(functorDeclares(F)).
cheaply_u(prologBuiltin(G)):- !,clause_b(prologBuiltin(G)).
cheaply_u(call(ereq,G)):- !,sanity(callable(G)),cheaply_u(G).
% cheaply_u(G):-!,call(G).
cheaply_u(G):- quietly(lookup_u(G)).

%cheaply_u(G):- need_speed,!, (ground(G)->(quietly(baseKB:G),!);quietly(lookup_u(G))).
%cheaply_u(G):- loop_check(cheaply_u(G),loop_check_term(cheaply_u(G),ilc2(G),fail)).
%cheaply_u(G):- predicate_property(G,number_of_rules(N)),N=0,!,lookup_u(G).
%cheaply_u(G):- strip_module(G,_,C),G\==C,!,cheaply_u(C).


was_isa_ex(ISA,I,C):- if_defined(was_isa(ISA,I,C),fail).
%= 	 	 

%% is_pred_declarer( ?P) is semidet.
%
% If Is A Predicate Declarer.
%
is_pred_declarer(P):-functor_declares_instance(P,tPred).

%= 	 	 

%% is_relation_type( ?P) is semidet.
%
% If Is A Relation Type.
%
is_relation_type(tRelation).
is_relation_type(tFunction).
is_relation_type(tPred).
is_relation_type(P):-is_pred_declarer(P).


%= 	 	 

%% functor_declares_instance( ?F, ?C) is semidet.
%
% Functor Declares Instance.
%
functor_declares_instance(F,C):- fail, functor_declares_instance_0(F,C0),!,C=C0. % , nop(sanity(F\=C0)).

%= 	 	 

%% functor_declares_instance_0( ?P, ?P) is semidet.
%
% safe_functor declares instance  Primary Helper.
%


functor_declares_instance_0(isa,_):-!,fail.
functor_declares_instance_0(props,_):-!,fail.
functor_declares_instance_0(F,F):- cheaply_u(functorDeclares(F)).
functor_declares_instance_0(F,F):- a(ttRelationType,F).

:- if(false).
functor_declares_instance_0(P,P):- arg(_,s(ttExpressionType,ttModuleType,tSet,ttTypeType,tFunction),P).

functor_declares_instance_0(P,P):- arg(_,s(tCol,ftSpec),P).
functor_declares_instance_0(P,P):- 
  arg(_,s(tPred,prologMultiValued, prologOrdered,prologNegByFailure,prologHybrid,prologPTTP,prologSideEffects,
       predIsFlag,prologBuiltin,prologKIF,prologDynamic,prologListValued,prologSingleValued),P).
functor_declares_instance_0(P,P):- arg(_,s(predCanHaveSingletons,functorIsMacro),P).
% functor_declares_instance_0(P,P):- arg(_,s(pfc_isa),P),!,fail.
functor_declares_instance_0(col_as_isa,col_as_isa).

functor_declares_instance_0(F,F):- between(2,5,A),arity_no_bc(F,A),!,fail.
functor_declares_instance_0(F,F):- arity_no_bc(F,A),A>5,!,fail.

% functor_declares_instance_0(F,F):- arity_no_bc(F,1).

functor_declares_instance_0(_,_):- !, fail.  % @TODO COMMENT THIS OUT

% functor_declares_instance_0(COL,COL):- call_u(isa(COL,ttTypeType)).
functor_declares_instance_0(COL,COL):- call_u(isa(COL,tSet)).
functor_declares_instance_0(P,P):- isa_asserted(P,ttRelationType),!.

functor_declares_instance_0(_,_):- !, fail.  % @TODO COMMENT THIS OUT

% @TODO CONFIRM THIS IS WRONG functor_declares_instance_0(functorIsMacro,tRelation).
functor_declares_instance_0(P,ttRelationType):-isa_from_morphology(P,ttRelationType).
functor_declares_instance_0(P,tFunction):-isa_from_morphology(P,ftFunctional).
functor_declares_instance_0(P,tFunction):-isa_from_morphology(P,O)->O=tFunction.
%functor_declares_instance_0(COL,COL):- call_u(isa(COL,tCol)).
%functor_declares_instance_0(P,tCol):-isa_asserted(P,functorDeclares),\+functor_declares_instance_0(P,tPred).



functor_adds_instance_0(decl_mpred,tPred).
functor_adds_instance_0(kb_shared,prologHybrid).
functor_adds_instance_0(kb_shared,prologHybrid).
functor_adds_instance_0(decl_pfc_prolog,prologBuiltin).
functor_adds_instance_0(decl_pfc_prolog,prologDynamic).

% functor_adds_instance_0(meta_argtypes,tRelation).

:- endif.


% ========================================
% Logic Preds Shared
% ========================================

%= %= :- was_export(is_svo_functor/1).



%% is_svo_functor( ?Prop) is semidet.
%
% If Is A Svo Functor.
%
is_svo_functor(Prop):- quietly((atom(Prop),arg(_,svo(svo,prop,valueOf,rdf),Prop))).

%= %= :- was_export(hilog_functor/1).



%% hilog_functor( ?VALUE1) is semidet.
%
% Hilog Functor.
%
hilog_functor(true_t).

%= %= :- was_export(is_holds_true_not_hilog/1).



%% is_holds_true_not_hilog( ?HOFDS) is semidet.
%
% If Is A Holds True Not Hilog.
%
is_holds_true_not_hilog(HOFDS):-is_holds_true(HOFDS),\+ hilog_functor(HOFDS).

%= %= :- was_export(is_holds_true/1).



%% is_holds_true( ?Prop) is semidet.
%
% If Is A Holds True.
%
is_holds_true(Prop):- quietly((atom(Prop),is_holds_true0(Prop))),!.

% k,p,..


is_holds_functor(F):- atom(F),is_holds_functor0(F),!, \+ isBodyConnective(F).
is_holds_functor0(F):- atom_concat('proven_',_,F).
is_holds_functor0(F):- atom_concat('ex_',_,F).
is_holds_functor0(F):- atom_concat(_,'_t',F).
is_holds_functor0(F):- is_2nd_order_holds(F).

must_be_unqualified(_):-!.
must_be_unqualified(Var):- \+ compound(Var),!.
must_be_unqualified(Var):-strip_module(Var,_,O),Var\==O,!,break_ex.
must_be_unqualified(Var):-forall(arg(_,Var,E),must_be_unqualified(E)).


:- dynamic(isBodyConnective/1).


%% isBodyConnective( ?Funct) is semidet.
%
% If Is A Body Connective.
%
isBodyConnective(Funct):-atom_concat(_,'_',Funct),!.
isBodyConnective(Funct):-atom_concat('t~',_,Funct),!.
isBodyConnective(Funct):-atom_concat('f~',_,Funct),!.
isBodyConnective(Funct):-member(Funct,[and,or,until,',',';',':-',unless,xor,holdsDuring]). % Other Propositional Wrhtml_appers




%% is_holds_true0( ?Prop) is semidet.
%
% If Is A Holds True Primary Helper.
%
is_holds_true0(Prop):-arg(_,vvv(holds,holds_t,t,t,asserted_pfc_t,assertion_t,true_t,assertion,secondOrder,firstOrder),Prop).


% is_holds_true0(Prop):-atom_concat(_,'_t',Prop).

%= %= :- was_export(is_2nd_order_holds/1).



%% is_2nd_order_holds( ?Prop) is semidet.
%
% If Is A 2nd Order Holds.
%
is_2nd_order_holds(Prop):- is_holds_true(Prop) ; is_holds_false(Prop).

%= %= :- was_export(is_holds_false/1).



%% is_holds_false( ?Prop) is semidet.
%
% If Is A Holds False.
%
is_holds_false(Prop):-quietly((atom(Prop),is_holds_false0(Prop))).




%% is_holds_false0( ?Prop) is semidet.
%
% If Is A Holds False Primary Helper.
%
is_holds_false0(Prop):-member(Prop,[not,nholds,holds_f,mpred_f,aint,assertion_f,not_true_t,asserted_mpred_f,retraction,not_secondOrder,not_firstOrder]).
%is_holds_false0(Prop,Stem):-atom_concat('not_',Stem,Prop).
%is_holds_false0(Prop,Stem):-atom_concat('int_not_',Stem,Prop).
%is_holds_false0(Prop,Stem):-atom_concat(Stem,'_f',Prop).
%is_holds_false0(Prop):-is_holds_false0(Prop,Stem),is_holds_true0(Stem).
%is_holds_false0(Prop,Stem):-atom_concat(Stem,'_not',Prop).
%is_holds_false0(Prop,Stem):-atom_concat(Stem,'_false',Prop).


%= 	 	 

%% with_assert_op_override( ?Op, ?Call) is semidet.
%
% Using Assert Oper. Override.
%
with_assert_op_override(Op,Call):-locally_tl(assert_op_override(Op),Call).



%= 	 	 

%% functor_declares_collectiontype( +Op, ?VALUE2) is semidet.
%
% Functor Declares Collectiontype.
%
functor_declares_collectiontype(typeProps,ttTemporalType).


%= 	 	 

%% instTypePropsToType( +Op, ?VALUE2) is semidet.
%
% Inst Type Props Converted To Type.
%
instTypePropsToType(instTypeProps,ttSpatialType222).


:- thread_local(t_l:into_goal_code/0).


%= 	 	 

%% reduce_clause( ?Op, ?C, ?HB) is semidet.
%
% Reduce Clause.
%
reduce_clause(Op,C,HB):-must(nonvar(C)),quietly_must(demodulize(Op,C,CB)),CB\=@=C,!,reduce_clause(Op,CB,HB).
reduce_clause(_,C,C):- t_l:into_goal_code,!.
reduce_clause(Op,clause(C, B),HB):-!,reduce_clause(Op,(C :- B),HB).
reduce_clause(Op,(C:- B),HB):- is_true(B),!,reduce_clause(Op,C,HB).
reduce_clause(_,C,C).


%% demodulize( ?Op, ?H, ?HH) is semidet.
%
% Demodulize.
%

demodulize(_Op,H,H):-!.
demodulize(_Op,H,HH):- not_ftCompound(H),!,HH=H.
demodulize(Op,H,HHH):- strip_module(H,M,HH),H\==HH,old_is_stripped_module(M),!,demodulize(Op,HH,HHH).
demodulize(Op,[I|HL],[O|HHL]):- \+ is_list(HL), !, demodulize(Op,I,O),demodulize(Op,HL,HHL).
demodulize(Op,H,HH):- is_list(H),must_maplist(demodulize(Op),H,HH),!.
demodulize(Op,H,HH):- H  univ_safe  [F|HL],must_maplist(demodulize(Op),HL,HHL),HH  univ_safe  [F|HHL],!.
% lmcache:completely_expanded



old_is_stripped_module(user).
old_is_stripped_module(baseKB).
%= 	 	 

%% to_reduced_hb( ?Op, ?HB, ?HH, ?BB) is semidet.
%
% Converted To Reduced Head+body.
%
to_reduced_hb(Op,HB,HH,BB):-reduce_clause(Op,HB,HHBB),expand_to_hb(HHBB,HH,BB).


/*
dbase_head_expansion(_,V,V ):-is_ftVar(V),!.
dbase_head_expansion(Op,H,GG):-correct_negations(Op,H,GG),!.
dbase_head_expansion(_,V,V).
*/

% ================================================
% db_expand_maplist/3
% ================================================


%= 	 	 

%% any_op_to_call_op( +Op, ?VALUE2) is semidet.
%
% Any Oper. Converted To Call Oper..
%
any_op_to_call_op(_,call(conjecture)).


%= 	 	 

%% db_expand_maplist( :PRED2FE, ?List, ?T, ?G, ?O) is semidet.
%
% Database Expand Maplist.
%
db_expand_maplist(FE,[E],E,G,O):- !,call(FE,G,O).
db_expand_maplist(FE,[E|List],T,G,O):- copy_term(T+G,CT+CG),E=CT,!,call(FE,CG,O1),db_expand_maplist(FE,List,T,G,O2),conjoin_l(O1,O2,O).
db_expand_maplist(FE,List,T,G,O):-bagof(M, (member(T,List),call(FE,G,M)), ML),list_to_conjuncts(ML,O).


% ================================================
% fully_expand/3
%   SIMPLISTIC REWRITE (this is not the PRECANONICALIZER)
% ================================================


%= 	 	 

%% should_expand( :TermG) is semidet.
%
% Must Be Successfull Expand.
%
%TODO Maybe later? should_expand(G):- \+ skip_expand(G), arg(_,G,E),compound(E).
should_expand(G):- \+ compound(G),!,fail.
should_expand(_:G):- !,should_expand(G).
should_expand((G:-_)):- !,should_expand(G).
should_expand(G):- safe_functor(G,F,_),should_expand_f(F),!.
should_expand(G):- safe_functor(G,F,_),exact_args_f(F),!,fail.  % Will expand these only after evaluation
should_expand(G):- arg(A,G,C),(string(C);(compound(C),A==2)),!.


should_expand_f(kif).
should_expand_f(pkif).
should_expand_f('==>').
should_expand_f('~').

should_expand_f(props).
should_expand_f(iprops).
should_expand_f(upprop).
should_expand_f(typeProps).
should_expand_f(mudLabelTypeProps).
should_expand_f(iprops).
should_expand_f(isa).
should_expand_f(t).
should_expand_f(isEach).

% Collecton Hooks
should_expand_f(tPred).
should_expand_f(tFunction).
should_expand_f(tRelation).
should_expand_f(tCol).
should_expand_f(tSet).
should_expand_f(F):-atom_concat('tt',_,F).
should_expand_f(F):-atom_concat('rt',_,F).

% Pred Impl Hooks
should_expand_f(singleValuedHybrid).
%should_expand_f(prologHybrid).
%should_expand_f(prologBuiltin).
%should_expand_f(prologDynamic).
should_expand_f(F):-atom_concat('prolog',_,F).
should_expand_f(F):-atom_concat('pddl',_,F).
should_expand_f(F):-atom_concat('pfc',_,F).
should_expand_f(F):-atom_concat('pfc_',_,F).


%= 	 	 

%% full_transform_warn_if_changed_UNUSED( ?A, ?B, ?O) is semidet.
%
% Fully Expand Warn.
%
full_transform_warn_if_changed_UNUSED(A,B,O):-
  must(fully_expand_real(A,B,C)),!,
  sanity(ignore(show_failure(why,same_terms(B,C)))),(O=C;must(sanity(ignore(show_failure(why,same_terms(O,C)))))),!.




:- export(fully_expand/3).


:- export(fully_expand/2).

%= 	 	 

%% fully_expand( ^X, --Y) is det.
%
% Fully Expand.
%
fully_expand(X,Y):- must((fully_expand(clause(unknown,cuz),X,Y))).

%:- pfc_trace_nochilds(fully_expand/3).



%% fully_expand( ++Op, ^Sent, --SentO) is det.
%
% Fully Expand.
%
%  Op = the type of operation we are expanding for.. currently there are
%  change(_,_) - for inclusion and testing of present in plain prolog
%  query(_,_) - for call/ask that is dirrectly runnable
%  pfc(_,_) - for salient language based analysis at a human level
%


%fully_expand(_,Var,Var):- \+ compound(Var),!.
%fully_expand(Op,Sent,SentO):- safe_functor(Sent,F,A),should_fully_expand(F,A),!,must(fully_expand_real(Op,Sent,SentO)),!.
fully_expand(Op,Sent,SentO):- quietly(fully_expand_real(Op,==>Sent,SentO)),!.
% fully_expand(Op,Sent,Sent):- sanity((ignore((fully_expand_real(Op,Sent,SentO)->sanity((Sent=@=SentO)))))).

/*
fully_expand(Op,Sent,SentO):- must(fully_expand_real(Op,Sent,SentO)),!,
   fully_expand_check(Op,Sent,SentO).

fully_expand_check(_Op,Sent,SentO):- Sent=@=SentO.
fully_expand_check(Op,Sent,SentO):- break,throw(fully_expand_real(Op,Sent,SentO)).

*/
/*
should_fully_expand(~,1).
should_fully_expand(==>,_).
should_fully_expand(props,2).
should_fully_expand(t,_).
should_fully_expand(ereq,_).
should_fully_expand(arity,2).
should_fully_expand(F,_):-clause_b(functorIsMacro(F)).
should_fully_expand(F,_):-clause_b(functorDeclares(F)).
*/

:- meta_predicate memoize_on_local(*,*,0).
memoize_on_local(_Why,_,Goal):- call(Goal),!.
% memoize_on_local(_Why,Sent->SentO,Goal):- memoize_on(fully_expand_real,Sent->SentO,Goal).

has_skolem_attrvars(Sent):- quietly((term_attvars(Sent,Attvars),member(Var,Attvars),get_attr(Var,skk,_))),!.


% for trace testing
fully_expand_real(X,Y):- must((fully_expand_real(clause(unknown,cuz),X,Y))).



fully_expand_real(_Op,Sent,SentO):- \+ compound(Sent),!,Sent=SentO.
fully_expand_real(Op,isa(I,C),SentO):- !,fully_expand_real_2(Op,isa(I,C),SentO).
fully_expand_real(Op,==>(Sent),SentO):- !,fully_expand_real_2(Op,Sent,SentO).
fully_expand_real(Op,==>(SentA,SentB),SentOO):- !,fully_expand_real_2(Op,==>(SentA,SentB),SentOO).
fully_expand_real(Op,mudKeyword(SentA,SentB),SentOO):- !,fully_expand_real_2(Op,mudKeyword(SentA,SentB),SentOO).
fully_expand_real(Op,<==>(SentA,SentB),SentOO):- !,fully_expand_real_2(Op,<==>(SentA,SentB),SentOO).
fully_expand_real(Op,(Sent/I),(SentO/O)):- !,fully_expand_real_2(Op,Sent,SentO),fully_expand_goal(Op,I,O).
fully_expand_real(_Op,{}(IC),{}(IC)):- !.
fully_expand_real(Op,Sent,SentO):- safe_functor(Sent,F,A),always_quite_expand_fa(F,A),!,fully_expand_real_2(Op,Sent,SentO).
fully_expand_real(Op,(SentA,SentB),(SentAA,SentBB)):- !,
  fully_expand_real(Op,SentA,SentAA),fully_expand_real(Op,SentB,SentBB).
fully_expand_real(Op,SentI,SentO):- maybe_expand_reduce(Op,SentI,Sent),!,
   fully_expand_real_2(Op,Sent,SentO),!,
   (Sent=@=SentO-> true ;            
     (SentI \=@= Sent -> true ; 
       show_expansion("~N-----++",Op,Sent,SentO))).
fully_expand_real(_Op,Sent,Sent):- current_prolog_flag(runtime_speed,3),!.
fully_expand_real(_Op,Sent,Sent):- current_prolog_flag(runtime_safety,0),!.
fully_expand_real(_Op,(H:-B),(H:-B)):-!.

fully_expand_real(Op,Sent,SentO):- !, fully_expand_real_2(Op,Sent,SentO),!.
fully_expand_real(Op,Sent,SentO):-
  fully_expand_real_2(Op,Sent,SentO),!,
  (Sent=@=SentO-> true ; 
    (dumpST,show_expansion("~N<!--BREAK-ERROR--->",Op,Sent,SentO),nop(break))).

show_expansion(Prefix,Op,Sent,SentO):-dmsg_pretty(Prefix),dmsg_pretty(-->(Op)),dmsg_pretty(Sent),dmsg_pretty(-->),dmsg_pretty(SentO),!.

fully_expand_real_2(Op,Sent,SentO):- has_skolem_attrvars(Sent),!,
   gripe_time(0.2,
    (must_det(quietly(serialize_attvars(Sent,SentI))),
      sanity(\+ has_skolem_attrvars(SentI)),
     must_det(fully_expand_real_3(Op,SentI,SentO)),!)),!.
fully_expand_real_2(Op,Sent,SentO):- fully_expand_real_3(Op,Sent,SentO).

fully_expand_real_3(Op,Sent,SentO):-
   gripe_time(0.2,
    must_det(locally_tl(disable_px,
       (locally(local_override(no_kif_var_coroutines,true),
       (must_det(fully_expand_into_cache(Op,Sent,SentIO)),
                   must_det(quietly(maybe_deserialize_attvars(SentIO,SentO))))))))).


maybe_expand(_Op,C,_):- \+ compound(C),!,fail.
maybe_expand(Op,M:P,M:PP):-!,maybe_expand(Op,P,PP).
maybe_expand(_Op,C,_):- compound_name_arity(C,_,0),!,fail.
maybe_expand(_Op,P,_):- var(P),!,fail.
maybe_expand(Op,P,P):-maybe_expand_p(Op,P),!.


maybe_expand_reduce(_Op,==>(P),P).
maybe_expand_reduce(_Op,expand(P),P).
maybe_expand_reduce(_Op,Sent,Sent):- safe_functor(Sent,F,_), clause_b(rtSymmetricBinaryPredicate(F)).


maybe_expand_p( Op, H:-_ ):- !, maybe_expand_p(Op,H).
maybe_expand_p(_Op,==>(_,_)).
maybe_expand_p(_Op,mudKeyword(_,_)).
maybe_expand_p(_Op,isa(_,_)).
maybe_expand_p(_Op,(_/_)).
maybe_expand_p(_Op,(_,_)).
maybe_expand_p(_Op,P):- safe_functor(P,F,A),!,always_quite_expand_fa(F,A).

always_quite_expand_fa(F,1):- maybe_expand_f(F).
always_quite_expand_fa(F,2):- clause_b(rtSymmetricBinaryPredicate(F)).
always_quite_expand_fa(t,_).
%always_quite_expand_fa(F,2):- should_expand_f(F).

maybe_expand_f(meta_argtypes).
maybe_expand_f(functorIsMacro).
maybe_expand_f(tPred).
maybe_expand_f(t).
maybe_expand_f(ttExpressionType).
maybe_expand_f(prologHybrid).
maybe_expand_f(prologBuiltin).
maybe_expand_f(prologSingleValued).
maybe_expand_f(prologHybrid).
maybe_expand_f(singleValuedHybrid).
maybe_expand_f(prologSideEffects).
maybe_expand_f(prologMultiValued).
%maybe_expand_f(F):- should_expand_f(F).


maybe_deserialize_attvars(X,Y):- current_prolog_flag(expand_attvars,true) 
  -> deserialize_attvars(X,Y) ; X=Y.
%maybe_deserialize_attvars(X,X):-!.


/*
fully_expand_real(Op,Sent,SentO):-
   gripe_time(0.2,
    (quietly(maybe_deserialize_attvars(Sent,SentI)),
     locally_tl(disable_px,
       locally(local_override(no_kif_var_coroutines,true),
       fully_expand_into_cache(Op,SentI,SentO))))),!.
*/    

%% is_stripped_module( +Op) is semidet.
%
%  Is a stripped Module (Meaning it will be found via inheritance)
%
is_stripped_module(A):-var(A),!,fail.
is_stripped_module(Mt):- call_u(mtExact(Mt)),!,fail.
%is_stripped_module(Inherited):-'$current_source_module'(E), default_module(E,Inherited).
%is_stripped_module(Inherited):-'$current_typein_module'(E), default_module(E,Inherited).
is_stripped_module(abox).
% is_stripped_module(_):-!,fail.
% is_stripped_module(baseKB).
% is_stripped_module(A):- defaultAssertMt(AB),!,AB=A.



%% expand_isEach_or_fail(^Sent, --SentO) is semidet.
%
% Expand isEach/Ns.

expand_isEach_or_fail(==>(Sent),SentO):- expand_isEach_or_fail_real(Sent,SentO),!.
expand_isEach_or_fail(Sent,SentO):- expand_isEach_or_fail_real(Sent,SentO),!,throw(expand_isEach_or_fail(Sent)).

expand_isEach_or_fail_real(Sent,SentO):- compound(Sent),
    \+ (Sent  univ_safe  [_,I],atomic(I)), bagof(O,do_expand_args(isEach,Sent,O),L),!,L\=@=[Sent],SentO=L,!.
expand_isEach_or_fail_conj(Sent,SentO):- expand_isEach_or_fail_real(Sent,SentM),list_to_conj(SentM,SentO).

%% expand_kif_string_or_fail( ++Op, ++Sent, --SentO) is semidet.
%
% Expand if String of KIF.
expand_kif_string_or_fail(_Why,I,O):- string(I), 
   locally(t_l:sreader_options(logicmoo_read_kif,true),
     ((input_to_forms(string(I),Wff,Vs)->
   put_variable_names(Vs) ->
   if_defined(sexpr_sterm_to_pterm(Wff,PTerm),Wff=PTerm)->
   PTerm\=@=I -> 
   O=PTerm))).


expand_kif_string(I,O):- any_to_string(I,S), string(S),
  locally(t_l:sreader_options(logicmoo_read_kif,true),input_to_forms(string(S),O,Vs))->
  put_variable_names(Vs).
  

%% fully_expand_clause( ++Op, :TermSent, -- SentO) is det.
%
% Fully Expand Clause.
%

:- dynamic(lmcache:completely_expanded/2).

%% fully_expand_into_cache( ++Op, ^Sent, --SentO) is det.
%
% Fully Expand Now.
fully_expand_into_cache(Op,Sent,SentO):- \+ ground(Sent),!,fully_expand_clause_catch_each(Op,Sent,SentO),!.
fully_expand_into_cache(_,Sent,SentO):- lmcache:completely_expanded(_,Sent),!,SentO=Sent.
fully_expand_into_cache(_,Sent,SentO):- lmcache:completely_expanded(Sent,SentO),!.
fully_expand_into_cache(Op,Sent,SentO):- 
 fully_expand_clause_catch_each(Op,Sent,SentO),!,
         asserta(lmcache:completely_expanded(Sent,SentO)),!.
fully_expand_into_cache(Op,Sent,SentO):- 
 trace,break,
  (fully_expand_clause_catch_each(Op,Sent,SentO)),
         asserta(lmcache:completely_expanded(Sent,SentO)),!.
% fully_expand_clause_catch_each(change(assert, ain), arity(functorDeclares, 1), _32410)


fully_expand_clause_catch_each(Op,Sent,SentO):-
  catch(fully_expand_clause(Op,Sent,SentO),
       hasEach,
      (must(expand_isEach_or_fail_conj(Sent,SentM)),
       must(fully_expand_real(Op,SentM,SentO)))),!.
/*

fully_expand_into_cache(Op,Sent,SentO):- term_variables(Sent,SentV),copy_term(Sent-SentV,SentI-SentIV),
                             numbervars(SentI,311,_),fully_expand_clause_now1a(Op,SentI,SentV-SentIV,Sent,SentO),!.

:- dynamic(completely_expanded_v/3).
subst_All(B,[],_R,B):-!.
subst_All(B,[F|L],R,A):-subst(B,F,R,M),subst_All(M,L,R,A).

fully_expand_clause_now1a(_Op,SentI,_,Sent,SentO):- completely_expanded_v(_,SentI),!,SentO=Sent.

%  p(A,B).  p(1,2).   ==>  q(2,1).   q(B,A)      SentV-SentIV,   [1,2],[A,B]  % substAll(p(1,2),[1,2],[A,B],O).
fully_expand_clause_now1a(Op,SentI,SentV-SentIV,_Sent,SentO):- lmcache:completely_expanded(SentI,SentOM),!,subst_All(SentOM,SentIV,SentV,SentO).
fully_expand_clause_now1a(Op,SentI,_,_Sent,SentO):- fully_expand_into_cache(Op,SentI,SentO),
         asserta(lmcache:completely_expanded(SentI,SentO)).

% fully_expand_into_cache(Op,Sent,SentO):- expand_isEach_or_fail(Sent,SentM)->SentM\=@=Sent,!,must(fully_expand_clause(Op,SentM,SentO)).
% fully_expand_into_cache(Op,Sent,SentO):- fully_expand_clause(Op,Sent,SentO),!.
fully_expand_into_cache(Op,Sent,SentO):- memoize_on_local(fully_expand_clause,Sent->SentO,(fully_expand_clause(Op,Sent,SentM),
  % post_expansion(Op,SentM,SentO)
  SentM=SentO
  )),!.
*/


post_expansion(Op,Sent,SentO):- 
   do_renames_expansion(Sent,SentM),!,
   maybe_correctArgsIsa(Op,SentM,SentO),!.

% 
do_renames_expansion(Sent,Sent):- \+ current_prolog_flag(do_renames,pfc_expansion),!.
do_renames_expansion(Sent,SentM):- if_defined(do_renames(Sent,SentM),=(Sent,SentM)).

maybe_correctArgsIsa(_ ,SentO,SentO):-!.
maybe_correctArgsIsa(Op,SentM,SentO):- locally_tl(infMustArgIsa,correctArgsIsa(Op,SentM,SentO)),!.

fully_expand_clause(Op,Sent,SentO):- sanity(is_ftNonvar(Op)),sanity(var(SentO)),var(Sent),!,Sent=SentO.
fully_expand_clause(Op,'==>'(Sent),(SentO)):-!,fully_expand_clause(Op,Sent,SentO),!.
fully_expand_clause(Op,'=>'(Sent),(SentO)):-!,fully_expand_clause(Op,Sent,SentO),!.
fully_expand_clause(Op,(B,H),Out):- !,must((fully_expand_clause(Op,H,HH),fully_expand_clause(Op,B,BB))),!,must(Out=(BB,HH)).
fully_expand_clause(Op,Sent,SentO):- is_list(Sent),!,must_maplist(fully_expand_clause(Op),Sent,SentO).
% fully_expand_clause(_,(:-(Sent)),(:-(Sent))):-!.
fully_expand_clause(Op,':-'(Sent),Out):-!,fully_expand_goal(Op,Sent,SentO),!,must(Out=':-'(SentO)).

fully_expand_clause(_,Sent,SentO):- t_l:infSkipFullExpand,!,must(Sent=SentO).

% fully_expand_clause(Op,Sent,SentO):- \+ compound(Sent),!,must(fully_expand_head(Op,Sent,SentO)).
fully_expand_clause(_,aNoExpansionFn(Sent),Sent):- !.
fully_expand_clause(Op,aExpansionFn(Sent),SentO):- fully_expand_clause(Op,Sent,SentO).
fully_expand_clause(Op,M:Sent,SentO):- is_stripped_module(M),!,fully_expand_clause(Op,Sent,SentO).

fully_expand_clause(Op,(B/H),Out):- !,fully_expand_head(Op,H,HH),fully_expand_goal(Op,B,BB),!,must(Out=(BB/HH)).

% prolog_clause fully_expand_clause
fully_expand_clause(Op, H :- B, HH :- B):- is_ftVar(B),!,fully_expand_head(Op,H,HH).

fully_expand_clause(Op,Sent,SentO):- string(Sent),expand_kif_string_or_fail(Op,Sent,SentO),!.
%covered fully_expand_clause(Op ,NC,NCO):- db_expand_final(Op,NC,NCO),!.
fully_expand_clause(Op, HB, OUT):- 
  to_reduced_hb(Op,HB,H,B) ->
  (fully_expand_head(Op,H,HH) ->
  (is_true(B) -> HH = OUT ;
    ( must(fully_expand_goal(Op,B,BB)),
      ((HH \= (_,_)) -> reduce_clause(Op,(HH:-BB),OUT) ;
         reduce_clause(Op,(H:-BB),OUT))))).


:- thread_local(t_l:into_form_code/0).

%% fully_expand_goal( ?Op, ^ Sent, -- SentO) is det.
%
% Fully Expand Goal.
%
fully_expand_goal(change(assert,_),Sent,SentO):- var(Sent),!,SentO=call_u(Sent).
fully_expand_goal(Op,Sent,SentO):- 
 must((
  locally_tl(into_goal_code,locally(t_l:into_form_code,fully_expand_head(Op,Sent,SentM))),
    recommify(SentM,SentO))).

/*

?- recommify((a,{((b,c),d)},e),O).
O =  (a, {b, c, d}, e).

?- recommify((a,{((b,c),d)},e),O).
O =  (a, {b, c, d}, e).

?- recommify((a,(b,c,d),e),O).
O =  (a, b, c, d, e).

?- recommify((a,(b,c),(d,e)),O).
O =  (a, b, c, d, e).

?- recommify((a,(b,c),(true,e)),O).
O =  (a, b, c, e).

?- recommify((((a0,a),(b,c)),(true,d,e)),O),portray_clause((h:-O)).
O =  (a0, a, b, c, d, e).

?- recommify((a,(b,c),call((true,e)),true),O).
O =  (a, b, c, call(e)).

*/

recommify(A,AA):- \+ compound(A),!,AA=A.
% recommify(A,A):-!.
recommify(A,B):- recommify(true,A,B),!.

recommify(A,B,C):- \+ compound(B),!,conjoin(A,B,C).
recommify(A,(B,C),D):- \+ compound(B),!, conjoin(A,B,AB), recommify(AB,C,D).
recommify(A,((X,B),C),D):- !, recommify(A,X,AX),recommify(AX,(B,C),D).
recommify(A,(B,C),D):- !, conjoin(A,B,AB), recommify(AB,C,D).
recommify(A,PredArgs,C):- PredArgs  univ_safe  [P|Args],maplist(recommify,Args,AArgs),B  univ_safe  [P|AArgs],conjoin(A,B,C),!.

list_to_conj([], true).
list_to_conj([C], C) :- !.
list_to_conj([H|T], (H,C)) :-
    list_to_conj(T, C).

const_or_var(I):- \+ atom(I), (var(I);I='$VAR'(_);(atomic(I),\+ string(I))),!.

:- export(as_is_term/1).

%% as_is_term( :TermNC) is semidet.
%
% Converted To If Is A Term Primary Helper.
%
as_is_term(NC):- cyclic_break(NC), const_or_var(NC),!.
as_is_term(PARSE):-is_parse_type(PARSE),!,fail.
as_is_term(NC):- compound(NC),!,NC  univ_safe  [F,A|R],as_is_term(F,A,R),!.

as_is_term(F,_,_):- exact_args_f(F).
as_is_term(F,I,[]):- !, (F==I;const_or_var(I)).
% as_is_term(_,I,[C]):- C==I. % const_or_var(I),const_or_var(C),!.
% covered  above as_is_term(CI):- CI  univ_safe  [C,I],C==I,!.

% covered  as_is_term(P):-safe_functor(P,F,A),safe_functor(C,F,A),C=@=P,!. % all vars
% covered  as_is_term(meta_argtypes(_)):-!.
% covered  as_is_term(meta_argtypes_guessed(_)):-!.
% covered  as_is_term(rtArgsVerbatum(Atom)):- !, \+ compound(Atom).
as_is_term(ftListFn,_,[]):-!.
as_is_term(arity,F,_):- atom(F).
% covered  as_is_term(functorIsMacro(Atom)):- !, \+ compound(Atom).
% covered  as_is_term(functorDeclares(Atom)):- !, \+ compound(Atom).
% covered  above as_is_term('$VAR'(_)).
% covered  above as_is_term(NC):-exact_args(NC),!.
% covered  above as_is_term(NC):-loop_check(is_unit(NC)),!.
% as_is_term(isa(I,C)):- \+ compound(I),atom(C), clause_asserted(baseKB:col_as_isa(C)),!.

/*
as_is_term((:),_,[NC]):-!,as_is_term(NC). 
as_is_term(Op,_,[_]):- infix_op(Op,_).
*/

:- pfc_trace_none(as_is_term(_)).
:- '$set_predicate_attribute'(as_is_term(_), hide_childs, 1).
:- lock_predicate(as_is_term(_)).

%=  :- was_export(infix_op/2).

%= 	 	 

%% infix_op( ?Op, ?VALUE2) is semidet.
%
% Infix Oper..
%
infix_op(Op,_):-comparitiveOp(Op).
infix_op(Op,_):-additiveOp(Op).

%=  :- was_export(comparitiveOp/1).

%= 	 	 

%% comparitiveOp( +Op) is semidet.
%
% Comparitive Oper..
%
comparitiveOp((\=)).
comparitiveOp((\==)).
% comparitiveOp((=)).
comparitiveOp((=:=)).
comparitiveOp((==)).
comparitiveOp((<)).
comparitiveOp((>)).
comparitiveOp((=<)).
comparitiveOp((>=)).

%=  :- was_export(additiveOp/1).

%= 	 	 

%% additiveOp( +Op) is semidet.
%
% Additive Oper..
%
additiveOp((is)).
additiveOp((*)).
additiveOp(+).
additiveOp(-).
additiveOp((/)).



%= 	 	 

%% is_unit( ?C) is semidet.
%
% If Is A Unit.
%
is_unit(A):-quietly(is_unit_like(A)).

is_unit_like(A):- atomic(A),!.
is_unit_like(C):-is_unit_like0(C).

is_unit_like0(C):- var(C),!, dictoo:oo_get_attr(C,skk,_),!.
is_unit_like0(C):- \+ compound(C),!.
is_unit_like0(C):- C\='VAR'(_),C\='$VAR'(_),C\=(_:-_),C\=ftRest(_),C\=ftListFn(_),get_functor(C,F),is_unit_functor(F).



%= 	 	 

%% is_unit_functor( ?F) is semidet.
%
% If Is A Unit Functor.
%
is_unit_functor(F):- (\+ atom(F)),!,fail.
is_unit_functor(F):-atom_concat('sk',_,F).
is_unit_functor(F):-atom_concat(_,'Fn',F).


%= 	 	 

%% get_ruleRewrite( ^ Sent, ?SentM) is semidet.
%
% Get Rule Rewrite.
%
% TODO - remove the fail (added just to speed up testing and initial debugging)
get_ruleRewrite(Sent,SentM):- fail, cheaply_u(ruleRewrite(Sent,SentM)).



transitive_lc_nr(P,A,B):- call(P,A,B),!.
transitive_lc_nr(_,A,A).
%= 	 	 

renamed_atom(F,FO):-atom(F),if_defined(best_rename(F,FO),fail),!.

%% pfc_expand_rule( ?PfcRule, ?Out) is det.
%
% Managed Predicate Expand.
%
pfc_expand_rule(PfcRule,Out):- 
   is_ftCompound(PfcRule),
   safe_functor(PfcRule,F,A),
   clause_b(pfc_database_term(F,A,_)),
   PfcRule  univ_safe  [F|Args],maplist(fully_expand_goal(assert),Args,ArgsO),!,Out  univ_safe  [F|ArgsO].

is_parse_type(Var):- \+ compound(Var),!,fail.
is_parse_type('kif'(NV)):-nonvar(NV).
is_parse_type('pkif'(NV)):-nonvar(NV).

%% db_expand_final( +Op, +TermNC, ?NC) is semidet.
%
% Database Expand Final.
%


string_to_mws_2(NC,NG):- \+ ground(NC),!, NG=NC.
string_to_mws_2([String,A|B],OUT):- is_list(B),!,OUT  univ_safe  [s,String,A|B].
string_to_mws_2([String],String):-!.
string_to_mws_2(String,String).


string_to_mws(NC,NCO):- string(NC),!,convert_to_cycString(NC,NCM),string_to_mws_2(NCM,NCO).
string_to_mws(NC,_):- \+ compound(NC),!,fail.
string_to_mws(NC,NO):- safe_functor(NC,s,_),!,NO=NC.
string_to_mws([String],NCO):-string(String),!,must((convert_to_cycString(String,NCM),string_to_mws_2(NCM,NCO))).

string_to_mws([String,A|B],OUT):- (string(String);string(A)),!,must((string_to_mws_2([String,A|B],OUT))).
%MAYBE string_to_mws([String|Rest],O):-string(String),!,(Rest==[]->O=String;O=[String|Rest]).


db_expand_final(_ ,NC,NC):-  is_ftVar(NC),!.
%db_expand_final(Op,t(EL),O):- !, db_expand_final(Op,EL,O).
db_expand_final(change(assert,_),props(_Obj,List),true):-  List==[],dumpST,!.
db_expand_final(_,props(Obj,List),{nonvar(Obj)}):- (List==[] ; List==true).
db_expand_final(_ ,sumo_rule(NC),sumo_rule(NC)):- !.

db_expand_final(Op, CMP,    O  ):- compound(CMP),meta_argtypes(Args)=CMP,
  is_ftCompound(Args),safe_functor(Args,Pred,A),
    (Pred=t->  (fully_expand_head(Op, Args,ArgsO),O=meta_argtypes(ArgsO)) ; 
      (assert_arity(Pred,A),O=meta_argtypes(Args))).

% db_expand_final(_,NC,NCO):- string_to_mws(NC,NCO),!.

%db_expand_final(_ ,NC,NCO):- atom(NC),do_renames_expansion(NC,NCO),!.
db_expand_final(_ ,NC,NC):- atomic(NC),!.
db_expand_final(_,PARSE,_):- is_parse_type(PARSE),!,fail.
db_expand_final(Op,M:Sent,SentO):- atom(M),is_stripped_module(M),!,db_expand_final(Op,Sent,SentO).
db_expand_final(_,Sent,_):- arg(_,Sent,E),compound(E),safe_functor(E,isEach,_),throw(hasEach).
db_expand_final(_,[_|_],_):- !,fail.
db_expand_final(_,Arg,Arg):- safe_functor(Arg,s,_),!.
db_expand_final(_,Sent,Sent):- Sent  univ_safe  [_,A],(atom(A);var(A);number(A);is_ftVar(A)),!.

db_expand_final(_ ,isa(Args,Meta_argtypes),  meta_argtypes(Args)):-Meta_argtypes==meta_argtypes,!,is_ftCompound(Args),!,safe_functor(Args,Pred,A),assert_arity(Pred,A).
% covered db_expand_final(Op,Sent,Sent):- Sent  univ_safe  [_,A],atom(A),!.
%db_expand_final(_,PARSE,ISA):- PARSE  univ_safe  [t,C,I],atom(C),atom(I),ISA  univ_safe  [C,I],!.
% covered db_expand_final(_ ,NC,NC):-safe_functor(NC,_,1),arg(1,NC,T),(not_ftCompound(T)),!.
db_expand_final(_, Sent,Sent):-is_true(Sent).
% covered db_expand_final(_,Term,Term):- is_ftCompound(Term),safe_functor(Term,F,_),(cheaply_u(prologBuiltin(F));cheaply_u(rtArgsVerbatum(F))).
% covered db_expand_final(_, arity(F,A),arity(F,A)):- not_ftCompound(F),not_ftCompound(A),!, (maybe_ain_arity(F,A)).
%unused db_expand_final(_, tPred(V),tPred(V)):-!,fail, not_ftCompound(V),!.
%db_expand_final(_ ,NC,NC):-safe_functor(NC,_,1),arg(1,NC,T),db_expand_final(_,T,_),!.

db_expand_final(_ ,IN,OUT):- IN  univ_safe  [F,A,B], \+ is_ftVar(A), \+ is_ftVar(B), clause_b(rtSymmetricBinaryPredicate(F)), (A@<B -> OUT=IN ; OUT  univ_safe  [F,B,A]).

db_expand_final(_ ,isa(Atom,PredArgTypes), tRelation(Atom)):-PredArgTypes==meta_argtypes,atom(Atom),!.
db_expand_final(_ ,meta_argtypes(F,Args),    meta_argtypes(Args)):-atom(F),!,safe_functor(Args,Pred,A),assert_arity(Pred,A).
%covered db_expand_final(_ ,meta_argtypes(Args),      meta_argtypes(Args)):-!.
%covered db_expand_final(_ ,meta_argtypes_guessed(Args),      meta_argtypes_guessed(Args)):-!.
%covered db_expand_final(Op,(A,B),(AA,BB)):-  !,db_expand_final(Op,A,AA),db_expand_final(Op,B,BB).
%db_expand_final(Op,props(A,B),PROPS):- (is_ftNonvar(A);is_ftNonvar(B)),!,expand_props(_,Op,props(A,B),Props),!,Props\=props(_,_),fully_expand_head(Op,Props,PROPS).
db_expand_final(_ ,NCO,NCO):- NCO   univ_safe  [F,A|R],as_is_term(F,A,R),!.
/*
db_expand_final(_, MArg1User, NewMArg1User):- is_ftCompound(MArg1User), fail,
   MArg1User  univ_safe  [M,Arg1,Arg2|User],
   compound_all_open(Arg1),
   get_functor(Arg1,F,A),F\==(t),F\==(/),
   member(F,[arity,predicateConventionMt]),
   NewMArg1User  univ_safe  [M,F/A,Arg2|User],!.
*/



%= 	 	 

%% is_elist_functor( +Op) is semidet.
%
% If Is A Elist Functor.
%
is_elist_functor(isList).
is_elist_functor(ftListfn).
is_elist_functor(isEach).
is_elist_functor(isAnd).


%= 	 	 

%% as_list( ?EC, ?AL) is det.
%
% Converted To List.
%
as_list(ftListFn(Atom),[Atom]):- atom(Atom),!.
as_list(Atom,[]):-is_elist_functor(Atom),!.
as_list(_,Atom):- \+ var(Atom), \+ is_list(Atom),!,fail.
as_list(EC,AL):-compound(EC),EC  univ_safe  [IsEach,A|List],is_elist_functor(IsEach),!,((List==[],is_list(A))->AL=A;AL=[A|List]).
as_list(List,AL):-sanity(is_list(List)),AL=List.



%= 	 	 

%% listToE( ?EL, ?E) is det.
%
% List Converted To E.
%
listToE(EL,E):-nonvar(EL),!,must(as_list(EL,List)),sanity(is_list(List)),E  univ_safe  [isEach|List].



%= 	 	 

%% db_expand_chain( +Op, ?M, ?PO) is det.
%
% Database Expand Chain.
%
db_expand_chain(_,V,_):-var(V),!,fail.
db_expand_chain(_,M:PO,PO) :- atom(M),!.
db_expand_chain(_,isa(I,Not),INot):-Not==not,!,INot   univ_safe   [Not,I].
db_expand_chain(_,_,_):- t_l:into_goal_code,!,fail.
db_expand_chain(_,(P:-B),P) :-is_true(B),!.
db_expand_chain(_,B=>P,P) :-is_true(B),!.
db_expand_chain(_,<=(P,B),P) :-is_true(B),!.
db_expand_chain(_,P<==>B,P) :-is_true(B),!.
db_expand_chain(_,B<==>P,P) :-is_true(B),!.
db_expand_chain(_,P<-B,P) :-is_true(B),!.
%db_expand_chain(_,P,PE):-fail,cyc_to_clif_entry(P,PE).
%db_expand_chain(_,('nesc'(P)),P) :- !.




%% fully_expand_head( ?A, ?B, ?C) is semidet.
%
% Database Expand A Noloop.
%

% covered fully_expand_head(_,Sent,SentO):- as_is_term(Sent),!,SentO=Sent,!.

fully_expand_head(Why,Before,After):-
  % quietly(subst(Before,pfc_isa,isa,Before1)),
  into_mpred_form(Before,Before2),
  must(try_expand_head(Why,Before2,After1)),
  must(post_expansion(Why,After1,After)).


try_expand_head(_,A,B):- t_l:infSkipFullExpand,!,A=B.
% try_expand_head(Op,Sent,SentO):- transitive_lc(db_expand_0(Op),Sent,OO),!,SentO=OO.


try_expand_head(Op,~Sent,~SentO):- nonvar(Sent),!,try_expand_head(Op,Sent,SentO).
try_expand_head(Op,Sent,SentO):- db_expand_0(Op,Sent,M)->( M==Sent->SentO=M;db_expand_0(Op,M,SentO)),!.


:- meta_predicate temp_comp(*,*,2,?).

% prolog_clause fully_expand_clause
temp_comp(H,B,PRED,OUT):- nonvar(H),term_variables(B,Vs1),Vs1\==[], term_attvars(B,AVs1), AVs1==[],   
   quietly((asserta(('$temp_comp123'(H,B):- B),Ref),clause('$temp_comp123'(H,_),BO,Ref),erase(Ref))),
   B\=@=BO,!,
   must((term_variables(BO,Vs2),!,must_maplist(=,Vs1,Vs2),call(PRED,(H:-BO),OUT))).


:- discontiguous db_expand_0/3.

%% db_expand_0( ?Op, ^ Sent, -- SentO) is semidet.
%
% Database expand  Primary Helper.
%
% :- meta_predicate(term_expansion(':'(:-),(:-))).
% :- mode(term_expansion(+,--)).

db_expand_0(_Op,Sent,Sent):- var(Sent),!.
db_expand_0(Op,not(Sent),not(SentO)):- !, db_expand_0(Op,Sent,SentO).
db_expand_0(Op,\+(Sent),\+(SentO)):- !, db_expand_0(Op,Sent,SentO).
db_expand_0(Op,~(Sent),~(SentO)):- !, db_expand_0(Op,Sent,SentO).
db_expand_0(Op,poss(Sent),poss(SentO)):- !, db_expand_0(Op,Sent,SentO).
db_expand_0(Op,nesc(Sent),nesc(SentO)):- !, db_expand_0(Op,Sent,SentO).
db_expand_0(Op,Sent,SentO):- cyclic_break(Sent),db_expand_final(Op ,Sent,SentO),!.

db_expand_0(_,Sent,Sent):- \+ compound(Sent),!.

db_expand_0(_Op,GG,SentO):-ground(GG),GG  univ_safe  [_,G],(G= -kif(_);G= -pkif(_)),!,SentO=G.
db_expand_0(Op,pkif(SentI),SentO):- nonvar(SentI),!,must((any_to_string(SentI,Sent),must(expand_kif_string_or_fail(Op,Sent,SentM)),SentM\=@=Sent,!,db_expand_0(Op,SentM,SentO))).
db_expand_0(_Op,kif(Sent),SentO):- nonvar(Sent),!, must(expand_kif_string(Sent,SentM)),if_defined(sexpr_sterm_to_pterm(SentM,SentO),SentM=SentO).

%TODO DONT RUIN 
db_expand_0(Op,==>(EL),O):- !, db_expand_0(Op,EL,O).
db_expand_0(_,t(Sent),t(Sent)):- ftVar(Sent),!.
%TODO DONT RUIN   
db_expand_0(Op,t(EL),O):- !, db_expand_0(Op,EL,O).

db_expand_0(Op,[G|B],[GG|BB]):-!,db_expand_0(Op,G,GG),db_expand_0(Op,B,BB).
db_expand_0(_Op,=>(G,B),=>(G,B)):-!.
db_expand_0(Op,(G,B),(GG,BB)):-!,db_expand_0(Op,G,GG),db_expand_0(Op,B,BB).
db_expand_0(Op,G:B,GG:BB):-!,db_expand_0(Op,G,GG),db_expand_0(Op,B,BB).

db_expand_0(Op,{Sent},{SentO}):- !,fully_expand_goal(Op,Sent,SentO),!.

db_expand_0(Op,SentI,SentO):- SentI  univ_safe  [NOT,Sent],arg(_,v( ( \+ ), '{}' , (~) , ( :- )  ),NOT),
  db_expand_0(Op,Sent,SentM)-> 
  (Sent\=@=SentM -> (SentMM  univ_safe  [NOT,SentM],fully_expand_goal(Op,SentMM,SentO)) ; SentO   univ_safe  [NOT,SentM]),!.


db_expand_0(_,Sent,SentO):- copy_term(Sent,NoVary),get_ruleRewrite(Sent,SentO),must(Sent\=@=NoVary),SentO \=@= Sent.
db_expand_0(call(Op),Sent,SentO):-  mreq(quasiQuote(QQuote)),subst(Sent,QQuote,isEach,MID),Sent\=@=MID,!,must(db_expand_0(call(Op),MID,SentO)).

db_expand_0(Op,Sent,SentO):- transitive_lc(db_expand_chain(Op),Sent,SentO)-> SentO \=@= Sent.


db_expand_0(_Op,P,PO):-db_expand_argIsa(P,PO),!.

db_expand_0(_Op,P,PO):- fail,
  compound(P),
  P  univ_safe  [_TYPE,UNIT],
  is_unit(UNIT),!,
  PO=P.

%:- kb_shared(is_svo_functor/1).

% prolog_clause db_expand_0
% db_expand_0(_Op,(H:-B),(H:-B)):- !.
db_expand_0(Op,(H:-B),OUT):- fully_expand_clause(Op,(H:-B),OUT),!,  
                         (((H:-B)=@=OUT)->true;dmsg_pretty(warn(db_expand_0(Op,(H:-B),OUT)))).
% prolog_clause db_expand_0
% db_expand_0(Op,(H:-B),OUT):- temp_comp(H,B,db_expand_0(Op),OUT),!.
db_expand_0(Op,(:-(CALL)),(:-(CALLO))):-with_assert_op_override(Op,db_expand_0(Op,CALL,CALLO)).
db_expand_0(Op,isa(I,O),INot):-Not==not,!,INot   univ_safe   [Not,I],!,db_expand_0(Op,INot,O).
db_expand_0(Op,isa(I,O),INot):-Not== ( \+ ) ,!,INot   univ_safe   [Not,I],!,db_expand_0(Op,INot,O).

db_expand_0(Op,THOLDS,OUT):- THOLDS  univ_safe  [t,P|ARGS],atom(P),!,HOLDS  univ_safe  [P|ARGS],db_expand_0(Op,HOLDS,OUT).
db_expand_0(Op,RDF,OUT):- RDF  univ_safe  [SVO,S,V,O],if_defined(is_svo_functor(SVO)),!,must_det(from_univ(_,Op,[V,S,O],OUT)).
db_expand_0(Op,G,OUT):- G  univ_safe  [Pred,InstFn,VO],compound(InstFn),InstFn=isInstFn(Type),is_ftNonvar(Type),from_univ(relationMostInstance,Op,[Pred,Type,VO],OUT).
db_expand_0(Op,G,OUT):- G  univ_safe  [Pred,InstFn|VO],compound(InstFn),InstFn=isInstFn(Type),is_ftNonvar(Type),GO  univ_safe  [Pred,Type|VO],db_expand_0(Op,GO,OUT).

db_expand_0(Op,props(A,F),OO):-!,expand_props(_Prefix,Op,props(A,F),OO),!.
db_expand_0(Op,iprops(A,F),OO):-!,expand_props(_Prefix,Op,props(A,F),OO),!.
db_expand_0(Op,upprop(A,F),ain(OO)):-!,expand_props(_Prefix,Op,props(A,F),OO),!.
db_expand_0(Op,padd(A,F),ain(OO)):-!,expand_props(_Prefix,Op,props(A,F),OO),!.


db_expand_0(Op,(call_u(CALL)),(call_u(CALLO))):-with_assert_op_override(Op,db_expand_0(Op,CALL,CALLO)).
db_expand_0(_ ,include(CALL),(load_data_file_now(CALL))):- dtrace, !.

db_expand_0(Op,=>(G),(GG)):-!,db_expand_0(Op,(G),(GG)).
db_expand_0(Op,(G,B),(GGBB)):-!,db_expand_0(Op,G,GG),db_expand_0(Op,B,BB),conjoin_l(GG,BB,GGBB).

db_expand_0(Op,(G==>B),(GG==>BB)):-!,db_expand_0(Op,G,GG),db_expand_0(Op,B,BB).


db_expand_0(Op,(G;B),(GG;BB)):-!,db_expand_0(Op,G,GG),db_expand_0(Op,B,BB).
db_expand_0(Op,(G:-B),(GG:-BB)):-!,db_expand_0(Op,G,GG),fully_expand_goal(Op,B,BB).

db_expand_0(Op,M:Sent,SentO):- atom(M),is_stripped_module(M),!,db_expand_0(Op,Sent,SentO).
db_expand_0(Op,M:Sent,R:SentO):- replaced_module(Op,M,R),!,db_expand_0(Op,Sent,SentO).

:- if(false).
db_expand_0(_Op,pddlSomethingIsa(I,EL),(isa(I,IC),O)):- icn_tcn(I,IC), listToE(EL,E),expand_isEach_or_fail(==>genls(IC,E),O),!.
:- endif.

db_expand_0(_Op,pddlSomethingIsa(I,EL),O):- listToE(EL,E),expand_isEach_or_fail(==>isa(I,E),O).
db_expand_0(_Op,pddlDescription(I,EL),O):- listToE(EL,E),expand_isEach_or_fail(==>mudDescription(I,E),O).
db_expand_0(_Op,pddlObjects(I,EL),O):- listToE(EL,E),expand_isEach_or_fail(==>isa(E,I),O).
db_expand_0(_Op,pddlSorts(I,EL),O):- listToE(EL,E),expand_isEach_or_fail(==>genls(E,I),O).
db_expand_0(_Op,pddlTypes(EL),O):- listToE(EL,E),expand_isEach_or_fail(==>isa(E,tCol),O).
db_expand_0(_Op,pddlPredicates(EL),O):- listToE(EL,E),expand_isEach_or_fail(==>prologHybrid(E),O).

db_expand_0(_,prop_mpred(M,RT,F,A),pfc_prop(M,F,A,RT)).

db_expand_0(Op,DECL,OUT):- 
    is_ftCompound(DECL)->
    DECL  univ_safe  [D,FA|Args0] ->
    functor_declares_instance_not_ft(D,DT)->
    flat_list(Args0,Args)->   
    maplist(nonvar,[FA|Args]) ->
    db_expand_set(Op,[DT,FA|Args],OUT).

db_expand_0(_,Sent,pfc_prop(M,F,A,RT)):- Sent  univ_safe  [RT,MFA],a(ttRelationType,RT),nonvar(MFA),get_mfa(MFA,M,F,A),atom(F),!.

get_mfa(M:FA,M,F,A):- !, get_fa(FA,F,A).
get_mfa(FA,M,F,A):- get_fa(FA,F,A),must(current_assertion_module(M)).


flat_list([Args],Args):-is_list(Args),!.
flat_list(Args,Args).

functor_declares_instance_not_ft(F,C):- functor_declares_instance_0(F,C0),!,C=C0. % , nop(sanity(F\=C0)).

% tSet(tMySet,comment("this was my set"))
db_expand_set(Op,[TPRED,F,A|Args],OUT):- atom(F),number(A),!,db_expand_set(Op,[TPRED,F/A|Args],OUT),!, (maybe_ain_arity(F,A)).
db_expand_set(Op,[TPRED,F/A|Args],OUT):- is_ftNameArity(F,A),
   db_expand_set(Op,[TPRED,F| Args],OUT),!,
    (maybe_ain_arity(F,A)).
db_expand_set(Op,[TPRED,F|Args],OUT):- atom(F),!,db_expand_0(Op,props(F,[TPRED|Args]),OUT).
db_expand_set(Op,[TPRED,FARGS|Args],(meta_argtypes(FARGS),OUT)):- 
   compound(FARGS), \+ ((arg(_,FARGS,E),is_ftVar(E))),safe_functor(FARGS,F,A),!,
   db_expand_set(Op,[TPRED,F/A|Args],OUT).


:- thread_local(t_l:no_db_expand_props/0).

% @TODO uncomment IMMEDIATELY
db_expand_0(Op,ClassTemplate,OUT):- \+ t_l:no_db_expand_props, db_expand_props(Op,ClassTemplate,OUT),!.

db_expand_props(Op,DECL,O):- fail, arg(_,DECL,S),string(S),DECL  univ_safe  [F|Args],maplist(destringify,Args,ArgsO),
  ArgsO\=@=Args,!,DECLM  univ_safe  [F|ArgsO],db_expand_0(Op,DECLM,O).


db_expand_props(Op,DECL,((isa(F,TPRED),O))):-DECL  univ_safe  [D,FA|Args],compound(FA),FA= (F/A),
  is_ftNameArity(F,A),functor_declares_instance(D,TPRED),
  is_ftNonvar(TPRED),is_relation_type(TPRED),expand_props(_Prefix,Op,props(F,[D|Args]),O),!,
   (maybe_ain_arity(F,A)).

db_expand_props(Op,DECL,(isa(F,TPRED),O)):-DECL  univ_safe  [D,F,A|Args],is_ftNameArity(F,A),functor_declares_instance(D,TPRED),
  arity_zor(D,1),
  is_ftNonvar(TPRED),is_relation_type(TPRED),expand_props(_Prefix,Op,props(F,[D|Args]),O),!,
   (maybe_ain_arity(F,A)).

:- if(false).
db_expand_props(Op,DECL,(isa(F,TPRED),O)):-DECL  univ_safe    [D,C|Args],is_ftCompound(C),functor_declares_instance(D,TPRED),
  \+ is_ftVar(C),
  \+ \+ is_non_unit(C),
  get_functor(C,F,A),  
  arity_zor(D,1),
  is_ftNonvar(TPRED),expand_props(_Prefix,Op,props(F,[D|Args]),M),!,
  (\+((arg(_,C,Arg),is_ftVar(Arg))) -> O = (meta_argtypes(C),M) ; (O= (M))),
   (maybe_ain_arity(F,A)).
:- endif.

db_expand_props(Op,DECL,O):-DECL  univ_safe  [D,F,A1|Args], functor_declares_instance(D,DType),
   arity_zor(D,1),
   %\+ is_relation_type(DType),
   expand_props(_Prefix,Op,props(F,[DType,D,A1|Args]),O),!.

db_expand_props(Op,DECL,O):-DECL  univ_safe  [D,F|Args],functor_declares_instance(D,DType),
   %\+ is_relation_type(DType),
   arity_zor(D,1)->
   expand_props(_Prefix,Op,props(F,[DType,D|Args]),O),!.


% shift/1 reset/3
%  room_template(iLivingRoom7,.....).
db_expand_props(Op,ClassTemplate,(tCol(PropsIsa),isa(Inst,PropsIsa),OUT)):- 
   ClassTemplate  univ_safe  [TypePropsFunctor,Inst|Props],
   functor_declares_instance(TypePropsFunctor,PropsIsa),
   arity_zor(TypePropsFunctor,1)->
   \+ compound_all_open(ClassTemplate),
   %ain(isa(PropsIsa,tCol)),
   %ain(isa(Inst,PropsIsa)),
   expand_props(t,Op,props(Inst,[PropsIsa|Props]),OUT),!.

% typeProps(tCrackers,.....).
db_expand_props(Op,ClassTemplate,(tCol(PropsIsa),isa(Type,PropsIsa),OUT)):-
   ClassTemplate  univ_safe  [TypeTypePropsFunctor,Type|Props],
   functor_declares_collectiontype(TypeTypePropsFunctor,PropsIsa),
   arity_zor(TypeTypePropsFunctor,1),
   \+ compound_all_open(ClassTemplate),
   %ain(isa(Type,tCol)),
   %ain(isa(Type,PropsIsa)),
   expand_props(relationMostInstance,Op,props(Type,Props),OUT),!.

% tRegion_inst_template(X, tLivingRoom,.....).
db_expand_props(Op,ClassTemplate,(isa(TypePropsIsa,Type),ONEPROP)):- isa_one_prop(NewInst,Type,OUT,ONEPROP),
  ClassTemplate  univ_safe  [FunctorTypePropsIsa,NewInst,Type|Props],
  instTypePropsToType(FunctorTypePropsIsa,TypePropsIsa),
  arity_zor(FunctorTypePropsIsa,2),
   \+ compound_all_open(ClassTemplate),
  expand_props(Op,props(NewInst,Props),OUT),!.

/*

% tRegion_template(tLivingRoom,.....).
db_expand_props(Op,typeProps(C,Props),(isa(I,C)==>mdefault(OOUT))):- (is_ftNonvar(C);is_ftNonvar(Props)), expand_props(Prefix,Op,props(I,Props),OUT),dtrace,list_to_conjuncts(OUT,OUTC),conjuncts_to_list(OUTC,OUTL),
   ISEACH  univ_safe  [isEach|OUTL],
  db_expand_0(Op,mdefault(ISEACH),OOUT).

*/

% db_expand_0(Op,C,F/A):-compound_all_open(C),get_functor(C,F,A).
db_expand_props(Op,ClassTemplate,OUT):- ClassTemplate  univ_safe  [props,Inst,Second,Third|Props],!,
   must(expand_props(_Prefix,Op,props(Inst,[Second,Third|Props]),OUT)),!.
db_expand_props(Op,arity(F,A),O):-expand_props(_Prefix,Op,props(F,arity(A)),O),!.

maybe_ain_arity(F,A):- ignore((atom(F),integer(A),ain(arity(F,A)))).

db_expand_0(Op,IN,OUT):- IN  univ_safe  [F|Args],F==t,!,must(from_univ(_,Op,Args,OUT)).
db_expand_0(Op,isa(A,F),OO):-atom(F),O  univ_safe  [F,A],!,db_expand_0(Op,O,OO).
db_expand_0(Op,isa(A,F),OO):-is_ftNonvar(A),is_ftNonvar(F),expand_props(_Prefix,Op,props(A,F),OO),!.
db_expand_0(_Op,isa(A,F),isa(A,F)):-!.
db_expand_0(Op,props(A,F),OO):-expand_props(_Prefix,Op,props(A,F),OO),!.
db_expand_0(Op,typeProps(A,F),EXP):-expand_props(_Prefix,Op,props(I,F),OO),!,fully_expand(Op,(isa(I,A)==>OO),EXP).

% covered db_expand_0(_,arity(F,A),arity(F,A)):-atom(F),!.
db_expand_0(Op,IN,OUT):- 
   cnas(IN,F,Args),
   % wdmsg_pretty(db_expand_0(Op,IN)),
   sanity(F \== isa),
   must_maplist(db_expand_0(Op),Args,ArgsO),
   map_f(F,FO),OUT  univ_safe  [FO|ArgsO].
   
isa_one_prop(NewInst,Type,OUT,ONEPROP):- ONEPROP = (isa(NewInst,Type)==>OUT).

%= 	 	 

%% is_arity_pred( +Op) is semidet.
%
% If Is A Arity Predicate.
%
is_arity_pred(argIsa).
is_arity_pred(arity).

arity_zor(D,ZOR) :- atom(D),D\==isa, \+ (arity_no_bc(D,N),!,N>ZOR).

%= 	 	 

%% map_f( ?F, ?F) is semidet.
%
% Map False.
%
map_f(M:F,M:FO):-atom(M),map_f(F,FO).
% map_f(pfc_isa,isa).
% map_f(props,isa).
map_f(F,F):-!.


%= 	 	 

%% ex_argIsa( ?P, ?N, ?C) is semidet.
%
% ex Argument  (isa/2).
%
ex_argIsa(P,N,C):- clause(_:argIsa(P,N,C),true).

db_expand_argIsa(P,_):- \+ compound(P),!,fail.
db_expand_argIsa(P,_):- is_dict(P),!,fail.
db_expand_argIsa(P,PO):- 
  P  univ_safe  [ARE,FF,AA],
   atom_concat('arg',REST,ARE),
   member(E,['Genl','Isa','SometimesIsa','Format','QuotedIsa']),atom_concat(N,E,REST),
   atom_number(N,NN),
   atom_concat('arg',E,AE),
  PO  univ_safe  [AE,FF,NN,AA],!.

db_expand_argIsa(P,PO):- 
  P  univ_safe  [ARE,FF,C1,C2],
   atom_concat('interArg',REST,ARE),
   member(E,['Isa','Genl','Format','QuotedIsa','GenlQuantity','NotIsa','SometimesIsa','NotQuotedIsa']),
   atom_concat(E,Nums,REST),
   (atomic_list_concat([A1,A2],'-',Nums);atomic_list_concat([A1,A2],'_',Nums)),!,
   atom_number(A1,N1),
   atom_number(A2,N2),
   atomic_list_concat(['interArg',E],AE),
  PO  univ_safe  [AE,FF,N1,C1,N2,C2],!.

db_expand_argIsa(P,PO):- 
  P  univ_safe  [ARE,FF,AA,RESULT],
   atom_concat('interArg',REST,ARE),
   member(E,['ResultGenl','ResultIsa','ResultNotIsa','ResultSometimesIsa','ResultFormat','ResultQuotedIsa','ResultNotQuotedIsa']),
   atom_concat(N,E,REST),
   atom_number(N,NN),
   atom_concat('interArg',E,AE),
  PO  univ_safe  [AE,FF,NN,AA,RESULT],!.


%= 	 	 

%% compound_all_open( ?C) is semidet.
%
% Compound All Open.
%
compound_all_open(C):-compound(C),safe_functor(C,_,A),A>1,\+((arg(_,C,Arg),is_ftNonvar(Arg))),!.

/*
db_expand_0(Op,Mt:Term,Mt:O):- is_kb_module(Mt),!,locally_tl(caller_module(baseKB,Mt),db_expand_0(Op,Term,O)).
db_expand_0(Op,DB:Term,DB:O):- defaultAssertMt(DB),!,locally_tl(caller_module(db,DB),db_expand_0(Op,Term,O)).
db_expand_0(Op,KB:Term,KB:O):- atom(KB),!,locally_tl(caller_module(prolog,KB),db_expand_0(Op,Term,O)).
*/

% db_expand_0(query(HLDS,Must),props(Obj,Props)):- is_ftNonvar(Obj),is_ftVar(Props),!,gather_props_for(query(HLDS,Must),Obj,Props).

replaced_module(_,V,_):- \+ atom(V),!,fail.
replaced_module(_,umt,ABox):-defaultAssertMt(ABox).
replaced_module(_,abox,ABox):-defaultAssertMt(ABox).
replaced_module(_,tbox,TBox):-get_current_default_tbox(TBox).

:- thread_local(t_l:current_defaultAssertMt/1).

maybe_prepend_mt(MT,I,O):- t_l:current_defaultAssertMt(ABOX)->ABOX==MT,!,maybe_prepend_mt(abox,I,O).
maybe_prepend_mt(abox,H,HH):-nonvar(HH),dtrace,maybe_prepend_mt(abox,H,HHH),must(HHH=HH),!.
maybe_prepend_mt(abox,H,HH):-var(H),must(HH=H),!.
maybe_prepend_mt(_,CL,CL):- compound(CL),CL=(_,_),!.
maybe_prepend_mt(_,H,HH):-predicateSystemCode(H,HH),!.
maybe_prepend_mt(abox,_:HH,HH):-!.
maybe_prepend_mt(abox,HH,HH):-!.
maybe_prepend_mt(Mt,Mt:HH,Mt:HH):-!.
maybe_prepend_mt(_,Mt:HH,Mt:HH):-!.
maybe_prepend_mt(Mt,HH,Mt:HH):-!.

predicateSystemCode(P,PP):-strip_module(P,_,PP),predicate_property(system:PP,defined),
  \+ predicate_property(system:PP,imported_from(baseKB)).

%% remodulize( ?Op, ?H, ?HH) is det.
%
% Re-Modulize.
%
remodulize(_, H,H):- is_ftVar(H),!.
remodulize(_, H,H):- \+ compound(H),!. % this disables the two next rules
remodulize(Op, H,HH):- atom(H),strip_module(H,FROM,_HHH),convention_to_symbolic_mt(FROM,Op,H,0,M),maybe_prepend_mt(M,H,HH).
remodulize(call(Op),M,R):-atom(M),replaced_module(Op,M,R),!.
remodulize(Op,M:H,M:HHH):-is_ftVar(M),!,must_remodulize(mvar(Op),H,HHH).
remodulize(Op,H,HH):-is_list(H),!,must_maplist(remodulize(Op),H,HH),!.
remodulize(Op,':-'(G),':-'(GG)):-!,must_remodulize(call(Op),G,GG).
remodulize(Op,(H:-G),(HH:-GG)):-!,must_remodulize(clause(Op,(':-')),H,HH),must_remodulize(call(Op),G,GG).
remodulize(Op,(H,G),(HH,GG)):-!,must_remodulize(call(Op),H,HH),must_remodulize(call(Op),G,GG).
remodulize(Op,(H;G),(HH;GG)):-!,must_remodulize(call(Op),H,HH),must_remodulize(call(Op),G,GG).

remodulize(Op,M:H,R:HHH):- replaced_module(Op,M,R),!,must_remodulize(Op,H,HHH).
remodulize(Op,M:H,HHH):- is_stripped_module(M),!,must_remodulize(Op,H,HHH).

remodulize(Op,Mt:H,HHHH):- is_ftCompound(H),H  univ_safe  [F|HL],!,must_maplist(remodulize(Op),HL,HHL),HH  univ_safe  [F|HHL],!,
  must((remodulize_pass2(Op,HH,HHH),maybe_prepend_mt(Mt,HHH,HHHH))).

remodulize(Op,H,HHH):-is_ftCompound(H),H  univ_safe  [F|HL],!,must_maplist(remodulize(Op),HL,HHL),HH  univ_safe  [F|HHL],!,
  must(remodulize_pass2(Op,HH,HHH)).

remodulize_pass2(Op,MHH,HHH):- strip_module(MHH,FROM,HH),safe_functor(HH,F,A),convention_to_symbolic_mt(FROM,Op,F,A,Mt),maybe_prepend_mt(Mt,HH,HHH).
% remodulize_pass2(Op,HH,HHH):- fix_mp(Op,HH,HHH),!. % this is overzealous
remodulize_pass2(_Why,HH,HH):- !.

%:- kb_shared(is_sentence_functor/1).

must_remodulize(Op,H,HHH):-must(demodulize(Op,H,HHH)),!.
%= 	 	 

%% is_meta_functor( ^ Sent, ?F, ?List) is semidet.
%
% If Is A Meta Functor.
%
is_meta_functor(Sent,F,List):-is_ftCompound(Sent),Sent  univ_safe  [F|List],
 (predicate_property(Sent,meta_predicate(_));
   is_sentence_functor(F);F==pfcDefault),!.






%% is_sentence_functor( ?And) is semidet.
%
% If Is A Sentence Functor.
%
is_sentence_functor(And):-quietly(is_logical_functor0(And)).



%% is_logical_functor0( ?X) is semidet.
%
% If Is A Logical Functor Primary Helper.
%
is_logical_functor0(&).
is_logical_functor0(v).
is_logical_functor0(exists).
is_logical_functor0(all).
is_logical_functor0(X):-atom(X),member(X,[',',';',xor,'\\+',~]).
is_logical_functor0(X):- a(logical_functor_pttp,X).
is_logical_functor0(X):- a(is_quantifier,X).
is_logical_functor0(And):-member(And,[(,),(;),('<-'),('=>'),('<=>'),(':-'),(and),nop]).



%= 	 	 

%% from_univ( ?Prefix, ?Op, :TermMORE, ?Out) is semidet.
%
% Converted From Univ.
%
from_univ(Prefix,Op,[T|MORE],Out):-T==t,!,from_univ(Prefix,Op,MORE,Out).
% MAYBE from_univ(Prefix,Op,[C,I],Out):- is_tspec(C),!,to_isa_form(I,C,Out).

from_univ(Prefix,Op,[PROP,Obj|MORE],Out):-PROP==props,!,expand_props(Prefix,Op,props(Obj,MORE),Out).
% from_univ(Prefix,Op,MORE,Out):-atom(Prefix),!,from_univ(_,Op,[Prefix|MORE],Out).
from_univ(_Prefix,_Op,[PROP|MORE],Out):-atom(PROP),!,Out  univ_safe  [PROP|MORE]. % ,db_expand_up(Prefix,Op,Mid,Out).
from_univ(_Prefix,_Op,In,Out):- Out  univ_safe  [t|In],!.


%= 	 	 

%% db_expand_up( ?Prefix, ?Op, ?Mid, ?OOUT) is semidet.
%
% Database Expand Up.
%
db_expand_up(Prefix,Op,Mid,OOUT):- fully_expand_head(Op,Mid,Out), 
  is_ftCompound(Prefix),subst(Prefix,value,Out,OOUT).
db_expand_up(_,Op,Mid,Out):- fully_expand_head(Op,Mid,Out).



%% expand_props( ?Op, ?Term, ?OUT) is semidet.
%
% Expand Props.
%

expand_props(Op,Term,OUT):-expand_props(_,Op,Term,OUT).


%= 	 	 

%% expand_props( ?Prefix, ?VALUE2, ^ Sent, ^ Sent) is semidet.
%
% Expand Props.
%
expand_props(_Prefix,_,Sent,OUT):- t_l:no_db_expand_props, (not_ftCompound(Sent)),!,OUT=Sent.
%expand_props(Prefix,Op,Term,OUT):- stack_check,(is_ftVar(OpeR);is_ftVar(Term)),!,trace_or_throw_ex(var_expand_units(OpeR,Term,OUT)).
expand_props(Prefix,Op,Sent,OUT):-  Sent  univ_safe  [And|C12],is_sentence_functor(And),!,maplist(expand_props(Prefix,Op),C12,O12),OUT  univ_safe  [And|O12].
expand_props(_Prefix,_ ,props(Obj,Open),props(Obj,Open)):- is_ftVar(Open),!. % ,trace_or_throw_ex(expand_props(Prefix,Op,props(Obj,Open))->OUT).
expand_props(_Prefix,change(assert,_),props(_Obj,List),true):- List==[],!.
expand_props(_Prefix,_,props(Obj,List),{nonvar(Obj)}):- List==[],!.
% expand_props(_Prefix,_ ,props(_Obj,List),true):- List==[],!.
expand_props(Prefix,Op,props(Obj,[P|List]),OUT):- List==[],expand_props(Prefix,Op,props(Obj,P),OUT),!.
% expand_props(Prefix,Op,props(Obj,[P]),OUT):- is_ftNonvar(P),!,expand_props(Prefix,Op,props(Obj,P),OUT).
expand_props(Prefix,Op,props(Obj,[P|ROPS]),OUT):- !,expand_props(Prefix,Op,props(Obj,P),OUT1),
   expand_props(Prefix,Op,props(Obj,ROPS),OUT2),
   conjoin_l(OUT1,OUT2,OUT).
expand_props(Prefix,Op,props(Obj,PropVal),OUT):- atom(PropVal),!,from_univ(Prefix,Op,[PropVal,Obj],OUT).

expand_props(_Prefix,_Op,props(Obj,PropVal),(PropVal2,{OPVAL})):- PropVal  univ_safe  [OpeR,Pred|Val],comparitiveOp(OpeR),
   not(comparitiveOp(Pred)),!,OPVAL  univ_safe  [OpeR,NewVar|Val],PropVal2  univ_safe  [Pred,Obj,NewVar],!.    

expand_props(_,_,props(Obj,PropVal),OUT):- var(Obj),atomic(PropVal), \+ atom(PropVal),OUT=[PropVal],!.
expand_props(_,_,props(Obj,PropValS),OUT):- var(Obj),member(PropVal,PropValS),atomic(PropVal), \+ atom(PropVal),OUT=PropValS,!.
expand_props(Prefix,Op,props(Obj,PropVal),OUT):- safe_univ(PropVal,[Prop,NonVar|Val]),Obj==NonVar,!,from_univ(Prefix,Op,[Prop,Obj|Val],OUT).
expand_props(Prefix,Op,props(Obj,PropVal),OUT):- 
   PropVal  univ_safe  [OpeR,Pred|Val],comparitiveOp(OpeR),
   not(comparitiveOp(Pred)),!,OPVAL  univ_safe  [OpeR|Val],PropVal2  univ_safe  [Pred,OPVAL],
    expand_props(Prefix,Op,props(Obj,PropVal2),OUT),!.
expand_props(Prefix,Op,props(Obj,PropVal),OUT):- PropVal  univ_safe  [Prop|Val], \+ (infix_op(Prop,_)),!,from_univ(Prefix,Op,[Prop,Obj|Val],OUT).
expand_props(Prefix,Op,props(Obj,PropVal),OUT):- PropVal  univ_safe  [Prop|Val],!,dtrace(from_univ(Prefix,Op,[Prop,Obj|Val],OUT)).
expand_props(Prefix,Op,props(Obj,Open),props(Obj,Open)):- trace_or_throw_ex(unk_expand_props(Prefix,Op,props(Obj,Open))).

expand_props(Prefix,OpeR,ClassTemplate,OUT):- ClassTemplate  univ_safe  [props,Inst,Second,Third|Props],!,
   expand_props(Prefix,OpeR,props(Inst,[Second,Third|Props]),OUT),!.

expand_props(_Prefix,_,Sent,Sent).


%= 	 	 

%% conjoin_l( ?A, :TermAA, ?C) is semidet.
%
% Conjoin (list Version).
%
conjoin_l(A,AA,C):-A==AA,!,C=A.
conjoin_l(A,AAB,C):- compound(AAB),AAB=(B,AA), A==AA,!,conjoin_l(A,B,C).
conjoin_l(A,AAB,C):- compound(AAB),AAB=(AA,B), A==AA,!,conjoin_l(A,B,C).
conjoin_l(A,B,C):-conjoin(A,B,C).



% ========================================
% into_mpred_form/2 (removes a second order functors until the common mpred form is left)
% ========================================
%=  :- was_export(into_mpred_form/2).

%= 	 	 

%% into_mpred_form( :TermV, ?VO) is semidet.
%
% Converted To Managed Predicate Form.
%

% into_mpred_form(Var,MPRED):- is_ftVar(Var), trace_or_throw_ex(var_into_mpred_form(Var,MPRED)).
into_mpred_form(V,VO):- (not_ftCompound(V)),!,VO=V.
into_mpred_form(M:X,M:O):- atom(M),!,into_mpred_form(X,O),!.
% convered into_mpred_form(Sent,SentO):-is_ftNonvar(Sent),get_ruleRewrite(Sent,SentM),!,into_mpred_form(SentM,SentO).
into_mpred_form((H:-B),(HH:-BB)):-!,into_mpred_form(H,HH),into_mpred_form(B,BB).
into_mpred_form((H:-B),(HH:-BB)):-!,into_mpred_form(H,HH),into_mpred_form(B,BB).
into_mpred_form((H,B),(HH,BB)):-!,into_mpred_form(H,HH),into_mpred_form(B,BB).
into_mpred_form((H;B),(HH;BB)):-!,into_mpred_form(H,HH),into_mpred_form(B,BB).
into_mpred_form((H/B),(HH/BB)):-!,into_mpred_form(H,HH),into_mpred_form(B,BB).
into_mpred_form(WAS,isa(I,C)):- was_isa_ex(WAS,I,C),!.
into_mpred_form(t(P),O):-is_ftNonvar(P),!,into_mpred_form(P,O).
into_mpred_form(t(P,A),O):-atom(P),!,O  univ_safe  [P,A].
into_mpred_form(t(P,A,B),O):-atom(P),!,O  univ_safe  [P,A,B].
into_mpred_form(t(P,A,B,C),O):-atom(P),!,O  univ_safe  [P,A,B,C].
into_mpred_form(IN,OUT):- 
   cnas(IN,F,Args),
   must_maplist(into_mpred_form,Args,ArgsO),!,
   map_f(F,FO),
   cnas(OUT,FO,ArgsO).


% into_mpred_form(I,O):- /*quietly*/(loop_check(into_mpred_form_ilc(I,O),O=I)). % trace_or_throw_ex(into_mpred_form(I,O).

%:- pfc_trace_nochilds(into_mpred_form/2).


%= 	 	 

%% into_mpred_form_ilc( ?G, ?O) is semidet.
%
% Converted To Managed Predicate Form Inside Of Loop Checking.
%
into_mpred_form_ilc([F|Fist],O):- is_list([F|Fist]),!,G  univ_safe  [t|[F|Fist]], into_mpred_form(G,O).
into_mpred_form_ilc(G,O):- safe_functor(G,F,A),G  univ_safe  [F,P|ARGS],!,into_mpred_form6(G,F,P,A,ARGS,O),!.

% TODO confirm negations

:- expire_tabled_list(all).


%% into_mpred_form6( ?X, ?H, ?P, ?N, ?A, ?O) is semidet.
%
% Converted To Managed Predicate Form6.
%
into_mpred_form6(C,_,_,2,_,C):-!.
% into_mpred_form6(H,_,_,_,_,G0):- once(locally(t_l:into_form_code,(expand_term( (H :- true) , C ), reduce_clause(assert,C,G)))),expanded_different(H,G),!,into_mpred_form(G,G0),!.
into_mpred_form6(_,F,_,1,[C],O):-alt_calls(F),!,into_mpred_form(C,O),!.
into_mpred_form6(_,':-',C,1,_,':-'(O)):-!,into_mpred_form_ilc(C,O).
into_mpred_form6(_,not,C,1,_,not(O)):-into_mpred_form(C,O),!.
into_mpred_form6(C,isa,_,2,_,C):-!.
into_mpred_form6(C,_,_,_,_,isa(I,T)):-was_isa_ex(C,I,T),!.
into_mpred_form6(_X,t,P,_N,A,O):-!,(atom(P)->O  univ_safe  [P|A];O  univ_safe  [t,P|A]).
into_mpred_form6(G,_,_,1,_,G):-predicate_property(G,number_of_rules(N)),N >0, !.
into_mpred_form6(G,F,C,1,_,O):-real_builtin_predicate(G),!,into_mpred_form(C,OO),O  univ_safe  [F,OO].
into_mpred_form6(_X,H,P,_N,A,O):-a(is_holds_false,H),(atom(P)->(G  univ_safe  [P|A],O=not(G));O  univ_safe  [holds_f,P|A]).
into_mpred_form6(_X,H,P,_N,A,O):-a(is_holds_true,H),(atom(P)->O  univ_safe  [P|A];O  univ_safe  [t,P|A]).
into_mpred_form6(G,F,_,_,_,G):-a(prologHybrid,F),!.
into_mpred_form6(G,F,_,_,_,G):-a(prologDynamic,F),!.
into_mpred_form6(G,F,_,_,_,G):-nop(dmsg_pretty(warn(unknown_pfc_type(F,G)))).

% ========================================
% acceptable_xform/2 (when the form is a isa/2, do a validity check)
% ========================================

%= 	 	 

%% acceptable_xform( ?From, ?To) is semidet.
%
% Acceptable Xform.
%
acceptable_xform(From,To):- From \=@= To,  (To = isa(I,C) -> was_isa_ex(From,I,C); true).

% ========================================
% transform_holds(Functor,In,Out)
% ========================================

%= 	 	 

%% transform_holds( ?H, ?In, ?Out) is semidet.
%
% Transform Holds.
%
transform_holds(H,In,Out):- once(transform_holds_3(H,In,Out)),!,ignore((In\=Out,fail,dmsg_pretty(transform_holds(H,In,Out)))).


% foreach_arg/7 
%  is a maping predicate

%= 	 	 

%% foreach_arg( :TermARGS, ?N, ?ArgIn, ?ArgN, ?ArgOut, ?Call, :TermARGS) is semidet.
%
% Foreach Argument.
%
foreach_arg(ARGS,_N,_ArgIn,_ArgN,_ArgOut,_Call,ARGS):- (not_ftCompound(ARGS)),!.
foreach_arg([ArgIn1|ARGS],ArgN1,ArgIn,ArgN,ArgOut,Call1,[ArgOut1|ARGSO]):-
     copy_term( a(ArgIn1,ArgOut1,ArgN1,Call1), a(ArgIn,ArgOut,ArgN,Call) ),
      call(Call),
      ArgN2 is ArgN + 1,
      foreach_arg(ARGS,ArgN2,ArgIn,ArgN,ArgOut,Call,ARGSO).


%= 	 	 

%% transform_functor_holds( +Op, ?F, ?ArgInOut, ?N, ?ArgInOut) is semidet.
%
% Transform Functor Holds.
%
transform_functor_holds(_,F,ArgInOut,N,ArgInOut):- once(call_u(argQuotedIsa(F,N,FT))),FT=ftTerm,!.
transform_functor_holds(Op,_,ArgIn,_,ArgOut):- transform_holds(Op,ArgIn,ArgOut),!.


%= 	 	 

%% transform_holds_3( +Op, :TermA, ?A) is semidet.
%
% Transform Holds Helper Number 3..
%
transform_holds_3(_,A,A):- (not_ftCompound(A)),!.
transform_holds_3(_,props(Obj,Props),props(Obj,Props)):-!.
%transform_holds_3(Op,Sent,OUT):-Sent  univ_safe  [And|C12],is_sentence_functor(And),!,maplist(transform_holds_3(Op),C12,O12),OUT  univ_safe  [And|O12].
transform_holds_3(_,A,A):-compound(A),safe_functor(A,F,N), predicate_property(A,_),arity_no_bc(F,N),!.
transform_holds_3(HFDS,M:Term,M:OUT):-atom(M),!,transform_holds_3(HFDS,Term,OUT).
transform_holds_3(HFDS,[P,A|ARGS],DBASE):- is_ftVar(P),!,DBASE  univ_safe  [HFDS,P,A|ARGS].
transform_holds_3(HFDS, ['[|]'|ARGS],DBASE):- trace_or_throw_ex(list_transform_holds_3(HFDS,['[|]'|ARGS],DBASE)).
transform_holds_3(Op,[SVOFunctor,Obj,Prop|ARGS],OUT):- if_defined(is_svo_functor(SVOFunctor)),!,transform_holds_3(Op,[Prop,Obj|ARGS],OUT).
transform_holds_3(Op,[P|ARGS],[P|ARGS]):- not(atom(P)),!,dmsg_pretty(transform_holds_3),trace_or_throw_ex(transform_holds_3(Op,[P|ARGS],[P|ARGS])).
transform_holds_3(HFDS,[HOFDS,P,A|ARGS],OUT):- a(is_holds_true,HOFDS),!,transform_holds_3(HFDS,[P,A|ARGS],OUT).
transform_holds_3(HFDS,[HOFDS,P,A|ARGS],OUT):- HFDS==HOFDS, !, transform_holds_3(HFDS,[P,A|ARGS],OUT).
transform_holds_3(_,HOFDS,isa(I,C)) :- was_isa_ex(HOFDS,I,C),!.
transform_holds_3(_,[Type,Inst],isa(Inst,Type)):-is_ftNonvar(Type),a(tCol,Type),!.
transform_holds_3(_,HOFDS,isa(I,C)):- holds_args(HOFDS,[ISA,I,C]),ISA==isa,!.

transform_holds_3(Op,[Fogical|ARGS],OUT):-  
         call(call,is_sentence_functor(Fogical)),!,sanity( \+ (a(is_svo_functor,Fogical))),
         must_det(foreach_arg(ARGS,1,ArgIn,ArgN,ArgOut,transform_functor_holds(Op,Fogical,ArgIn,ArgN,ArgOut),FARGS)),
         OUT  univ_safe  [Fogical|FARGS].

transform_holds_3(_,[props,Obj,Props],props(Obj,Props)).
transform_holds_3(_,[Type,Inst|PROPS],props(Inst,[isa(Type)|PROPS])):- 
                  is_ftNonvar(Inst), not(Type=props), (cheaply_u(tCol(Type));a(functorDeclares,Type)), 
                  must_det(\+(if_defined(is_never_type(Type)))),!.

transform_holds_3(_,[P,A|ARGS],DBASE):- atom(P),!,DBASE  univ_safe  [P,A|ARGS].
transform_holds_3(Op,[P,A|ARGS],DBASE):- !, is_ftNonvar(P),dumpST,trace_or_throw_ex(transform_holds_3(Op,[P,A|ARGS],DBASE)), DBASE  univ_safe  [P,A|ARGS].
transform_holds_3(Op,DBASE_T,OUT):- DBASE_T  univ_safe  [P,A|ARGS],!,transform_holds_3(Op,[P,A|ARGS],OUT).



%= 	 	 

%% holds_args( ?HOFDS, ?FIST) is semidet.
%
% Holds Arguments.
%
holds_args([H|FIST],FISTO):- !, a(is_holds_true,H),!,FIST=FISTO.
holds_args(HOFDS,FIST):- is_ftCompound(HOFDS),HOFDS  univ_safe  [H|FIST],a(is_holds_true,H),!.


%% do_expand_args( ?Op, ?Term, ?Term) is semidet.
%
% Do Expand Arguments.
%
do_expand_args(_,Term,TermO):- \+ compound(Term),!,must(Term=TermO).
do_expand_args(Exp,M:Sent,M:SentO):- atom(M),!,do_expand_args(Exp,Sent,SentO).
do_expand_args(_,Term,Term):- safe_functor(Term,F,_),cheaply_u(rtArgsVerbatum(F)),!.
do_expand_args(Exp,[L|IST],Out):- !,must(do_expand_args_l(Exp,[L|IST],Out)).
do_expand_args(Exp,Term,Out):- Term  univ_safe  [P|ARGS],do_expand_args_pa(Exp,P,ARGS,Out).


%= 	 	 

%% do_expand_args_pa( ?Exp, ?P, ?ARGS, ?Out) is semidet.
%
% Do Expand Arguments Pa.
%

% allows ?- fully_expand(arity(isEach([X,TY,OO]),4),O).
do_expand_args_pa(Exp,Exp,[ARGS|Some],Out):- (Some==[]),is_list(ARGS),!,member(Out,ARGS).
% allows ?- fully_expand(arity(isEach(X,TY,OO),4),O).
do_expand_args_pa(Exp,Exp,ARGS,Out):- !,member(Out,ARGS).
do_expand_args_pa(Exp,P,ARGS,Out):- do_expand_args_l(Exp,ARGS,EARGS), Out  univ_safe  [P|EARGS].


%= 	 	 

%% do_expand_args_l( +Op, :TermA, :TermA) is semidet.
%
% Do Expand Arguments (list Version).
%

% do_expand_args_l(Exp,ARGS,EARGS):- do_expand_args(Exp,A,E),do_expand_args_l(Exp,RGS,ARGS).

do_expand_args_l(_,A,A):- is_ftVar(A),!.
do_expand_args_l(Exp,[A|RGS],[E|ARGS]):- is_list(RGS),!,do_expand_args(Exp,A,E),do_expand_args_l(Exp,RGS,ARGS).
do_expand_args_l(_,A,A).



% :- pfc_trace_nochilds(functor_safe/2).
% :- pfc_trace_nochilds(functor_safe/3).


% ================================================
%  expand_goal_correct_argIsa/2
% ================================================

%= 	 	 

%% expands_on( ?EachOf, ?Term) is semidet.
%
% Expands Whenever.
%
%expands_on(EachOf,Term):-subst(Term,EachOf,foooz,Term2),!,Term2\=Term, \+ ((do_expand_args(EachOf,Term,O),O = Term)).

%= 	 	 

%% if_expands_on( ?EachOf, ?Term, ?Call) is semidet.
%
% If Expands Whenever.
%
%if_expands_on(EachOf,Term,Call):- expands_on(EachOf,Term),subst(Call,Term,O,OCall),!, forall(do_expand_args(EachOf,Term,O),OCall).

/*
%db_reop(WhatNot,Call) :- into_mpred_form(Call,NewCall),NewCall\=@=Call,!,db_reop(WhatNot,NewCall).
db_reop(Op,Term):- expands_on(isEach,Term), !,forall(do_expand_args(isEach,Term,O),db_reop_l(Op,O)).
db_reop(Op,Term):-db_reop_l(Op,Term).

db_reop_l(query(_HLDS,Must),Call) :- !,preq(Must,Call).
db_reop_l(Op,DATA):-no_loop_check(db_op0(Op,DATA)).

 dm sg_hook(transform_holds(t,_What,props(ttSpatialType,[isa(isa),isa]))):-trace_or_throw_ex(dtrace).

*/


% expand_goal_correct_argIsa(A,A):-simple_code,!.

%= 	 	 

%% expand_goal_correct_argIsa( ?A, ?B) is semidet.
%
% expand goal correct Argument  (isa/2).
%
expand_goal_correct_argIsa(A,B):- expand_goal(A,B).

% db_op_simpler(query(HLDS,_),MODULE:C0,call_u(call,MODULE:C0)):- atom(MODULE), is_ftNonvar(C0),not(not(predicate_property(C0,_PP))),!. % , functor_catch(C0,F,A), dmsg_pretty(todo(unmodulize(F/A))), %trace_or_throw_ex(module_form(MODULE:C0)), %   db_op(Op,C0).

%= 	 	 

%% db_op_simpler( +Op, ?VALUE2, :TermARG3) is semidet.
%
% Database Oper. Simpler.
%
db_op_simpler(Op,Sent,SentO):- call_last_is_var(db_op_simpler(Op,Sent,SentO)).

db_op_simpler(_,TypeTerm,props(Inst,[isa(Type)|PROPS])):- TypeTerm  univ_safe  [Type,Inst|PROPS],is_ftNonvar(Inst),a(functorDeclares,Type),!.



%= 	 	 

%% db_op_sentence( ?Op, ?Prop, ?ARGS, ?C0) is semidet.
%
% Database Oper. Sentence.
%
db_op_sentence(_Op,Prop,ARGS,C0):- atom(Prop),!, C0  univ_safe  [Prop|ARGS].
db_op_sentence(_Op,Prop,ARGS,C0):- C0  univ_safe  [t,Prop|ARGS].


%=  :- was_export(simply_functors/3).

%= 	 	 

%% simply_functors( :PRED2Db_pred, ?Op, ?Wild) is semidet.
%
% Simply Functors.
%
simply_functors(Db_pred,query(HLDS,Must),Wild):- once(into_mpred_form(Wild,Simpler)),Wild\=@=Simpler,!,call(Db_pred,query(HLDS,Must),Simpler).
simply_functors(Db_pred,Op,Wild):- once(into_mpred_form(Wild,Simpler)),Wild\=@=Simpler,!,call(Db_pred,Op,Simpler).


% -  dmsg_hook(db_op(query(HLDS,call),holds_t(ft_info,tCol,'$VAR'(_)))):-trace_or_throw_ex(dtrace).

lin_visits(P,Visits):-attvar(P),get_attr(P,linv,num(Visits)),!.
lin_visits(_,0).

set_lin_visits(P,Visits):-attvar(P),get_attr(P,linv,NumVisits),!,setarg(1,NumVisits,Visits).
set_lin_visits(P,Visits):-put_attr(P,linv,num(Visits)).

linearize_headvar_dupes(In,Out,How):- 
  term_variables(In,Vs),
  linearize_headvar_dupes((=),In,Out,How),
  maplist(del_attr_rl(linv),Vs).

del_attr_rl(Attr,Vs):- del_attr(Vs,Attr).

linearize_headvar_dupes(Equ,In,Out,How):- linearize_headvar_dupes(Equ,In,Out,true,How).
linearize_headvar_dupes(_Equ,P,PO,Left,Connector):- 
  (var(P),lin_visits(P,Visits)->Visits==0),!,
  set_lin_visits(P,1),PO=P,Left=Connector.
linearize_headvar_dupes(Equ,P,PO,Left,Connector):- var(P),!,PO=_,conjoin(Left,call(Equ,P,PO),Connector),!.
linearize_headvar_dupes(_Equ,P,PO,Left,Connector):- \+ compound(P),PO=P,Connector=Left,!.
linearize_headvar_dupes(Equ,[P1|M],[PO1|PL2],Left,Connector):-!, 
  linearize_headvar_dupes(Equ,P1,PO1,Left,MID),
  linearize_headvar_dupes(Equ,M,PL2,MID,Connector).
linearize_headvar_dupes(Equ,P,PO,Left,Connector):-P  univ_safe  [F|M],
 linearize_headvar_dupes(Equ,M,POL,Left,Connector),PO  univ_safe  [F|POL].


fixed_syntax(I,O):- compound(I), with_vars_locked(I,fix_syntax(I,O))->I\=@=O.

fix_syntax(P0,P0):- \+ compound(P0),!.
fix_syntax(I,O):-sub_compound_of(I,~(P/Cond)), !,O= preventedWhen(P,{Cond}).
fix_syntax(I,O):- sub_compound_of(I, (~P/Cond)), !,fix_syntax(~(P/Cond),O).
fix_syntax(~I,O):- compound(I),linearize_headvar_dupes(I,M,Cond)->Cond\==true,!,O= preventedWhen(M,{Cond}).
%fix_syntax(~I,O):- compound(I),linearize_headvar_dupes(I,M,Cond),!,O= preventedWhen(M,{Cond}).
fix_syntax(I,O):- fixed_negations(I,M),fix_syntax(M,O).
%fix_syntax(~P/Cond,O):-  !,O=(((P/Cond)==> ~P)).
%fix_syntax((~P)/Cond,O):- !,O=((~P <- {Cond} )).
%fix_syntax((~P)/Cond,O):- !,O=(((P/Cond)==> ~P)).
%fix_syntax((~P)/Cond,O):- !,O=(((P/Cond)==> ~P)).
%fix_syntax((~P)/Cond,O):- !,O=(((P/ (\+Cond)) ==> \+ ~P)).
%fix_syntax(P/Cond,O):- pfcLiteral_nonvar(P),!,O=((P <- { Cond } )).
fix_syntax(P/Cond,O):- !,O=((P <- {Cond} )).
fix_syntax(I, O):- sub_compound_of(I,((P/Cond):-B)),!,O=(P :- (B, Cond)).
fix_syntax(P:-B,PP:-B):-!, fix_syntax(P,PP).
% fix_syntax(I,O):- compound(I),linearize_headvar_dupes(I,PL,Cond)->Cond\==true,!,O= enabledWhen(PL,{Cond}).
fix_syntax(P,P).

sub_compound_of(I,Of):- compound(I),compound(Of),compound_name_arity(I,IN,IA),compound_name_arity(Of,ON,OA),
   (IA\==OA ; IN\==ON),!,fail.  
sub_compound_of(I,Of):- \+ \+ (numbervars(I,99,_,[attvar(bind)]),I=Of ), I = Of.

fixed_negations(I,O):- compound(I), with_some_vars_locked(I,fix_negations(I,O))->I\=@=O.

fix_negations(P0,P0):- not_ftCompound(P0),!.
fix_negations(~(P0),~(P0)):- not_ftCompound(P0),!.
fix_negations(\+(P0),\+(P0)):- not_ftCompound(P0),!.
fix_negations(\+ \+ (P0), (P0)):- not_ftCompound(P0),!.

fix_negations(\+ \+ (I), (O)):- !, fix_negations((I), (O)).

fix_negations(P==>Q, PP==>QQ):-!,
  fix_negations(P,PP),
  fix_negations(Q,QQ),!.

fix_negations(~(~I),O):- !, fix_negations(\+(~I),O).
fix_negations(~not(I),O):- !, fix_negations(\+(~I),O).
fix_negations(~~(I),O):- safe_functor(~~(I),~~,1),!, fix_negations(\+(~I),O).
fix_negations(not(I),O):- !, fix_negations(\+(I),O).
fix_negations(~(I),~(O)):- !, fix_negations(I,O).
fix_negations(\+(I),\+(O)):- !, fix_negations(I,O).
fix_negations(C,C):- if_defined(exact_args(C),fail),!.
fix_negations([H|T],[HH|TT]):-!,fix_negations(H,HH),fix_negations(T,TT),!.
fix_negations(C,CO):-C  univ_safe  [F|CL],must_maplist(fix_negations,CL,CLO),!,CO  univ_safe  [F|CLO].


%% reduce_clause_from_fwd(Op, +H, ?H) is semidet.
%
% Reduce Clause Converted From Forward Repropigated.
%
reduce_clause_from_fwd(_Op,H,H):- quietly(\+is_ftCompound(H)),!.
reduce_clause_from_fwd(Op,(H:-B),HH):-B==true,reduce_clause_from_fwd(Op,H,HH).
reduce_clause_from_fwd(Op,(B==>H),HH):-B==true,reduce_clause_from_fwd(Op,H,HH).
reduce_clause_from_fwd(Op,I,O):- quietly(fixed_negations(I,M)),!,reduce_clause_from_fwd(Op,M,O).
reduce_clause_from_fwd(Op,(==>H),HH):-!,reduce_clause_from_fwd(Op,H,HH).
reduce_clause_from_fwd(Op,(H<- B),HH):-B==true,reduce_clause_from_fwd(Op,H,HH).
reduce_clause_from_fwd(Op,(B<==> H),HH):-B==true,reduce_clause_from_fwd(Op,'==>'(H),HH).
reduce_clause_from_fwd(Op,(H<==> B),HH):-B==true,reduce_clause_from_fwd(Op,H,HH).
reduce_clause_from_fwd(Op,(H,B),(HH,BB)):-!,reduce_clause_from_fwd(Op,H,HH),reduce_clause_from_fwd(Op,B,BB).
reduce_clause_from_fwd(_Op,H,H).
        


%% append_as_first_arg( +C, ?I, ?V) is semidet.
%
% Append Converted To First Argument.
%
append_as_first_arg(C,I,V):-C  univ_safe  [F|ARGS],V  univ_safe  [F,I|ARGS].



%% to_predicate_isas( :TermV, :TermV) is semidet.
%
% Converted To Predicate Isas.
%
to_predicate_isas(V,V):- (\+is_ftCompound(V)),!.
to_predicate_isas({V},{V}):-!.
% to_predicate_isas(eXact(V),V):-!.
to_predicate_isas([H|T],[HH|TT]):-!,to_predicate_isas(H,HH),to_predicate_isas(T,TT),!.
to_predicate_isas((H,T),(HH,TT)):-!,to_predicate_isas(H,HH),to_predicate_isas(T,TT),!.
%to_predicate_isas(I,I):-contains_term(S,I),is_ftNonvar(S),exact_args(S),!.
to_predicate_isas(t(C,I),V):-atom(C)->V  univ_safe  [C,I];(is_ftVar(C)->V=t(C,I);append_as_first_arg(C,I,V)).
to_predicate_isas(isa(I,C),V):-!,(atom(C)->V  univ_safe  [C,I];(is_ftVar(C)->V=isa(I,C);append_as_first_arg(C,I,V))).
to_predicate_isas(C,C):- exact_args(C),!.
to_predicate_isas(C,CO):-C  univ_safe  [F|CL],must_maplist(to_predicate_isas,CL,CLO),!,CO  univ_safe  [F|CLO].


%% exact_args( +Q) is semidet.
%
% Exact Arguments.
%
exact_args(Q):- is_ftVar(Q),!,fail.
exact_args(Q):- \+ compound(Q), !.
exact_args(isEach):-!,fail.
%exact_args(_:Q):- !,(exact_args0(Q),fail).
exact_args(_:Q):- !,(exact_args0(Q)).
exact_args(Q):- exact_args0(Q),!.



exact_args0(Q):- \+ compound(Q), !.
exact_args0((A/B)):- (is_ftVar(A);(number(B);is_ftVar(B))),!.
exact_args0(==>(_,_)):-!,fail.
% exact_args0(Q):- Q  univ_safe  [_,A],atomic(A),!.
exact_args0(Q):- compound_name_arity(Q,F,A),A>0,!,exact_args_f(F),!.

exact_args_f(-->).
exact_args_f(if_defined).
exact_args_f(txtConcatFn).
exact_args_f(dif).

exact_args_f(maplist).
exact_args_f(action_info).
exact_args_f(never_retract_u).
exact_args_f(install_converter).
exact_args_f(installed_converter).
exact_args_f(pfcAction).
exact_args_f(wid).
exact_args_f(wdmsg_pretty).
exact_args_f(fol_to_pkif).
exact_args_f(ftListFn).
exact_args_f(vtActionTemplate).
exact_args_f(txtConcatFn).
exact_args_f(spft).
exact_args_f(skip_expand_fa).
exact_args_f(sformat).
exact_args_f(second_order).
exact_args_f(retract_eq_quitely).
exact_args_f(not_undoable).
exact_args_f(mtExact).
exact_args_f(vQuotientFn).
exact_args_f(uSubLQuoteFn).
exact_args_f(pfc_prop).
exact_args_f(pfc_ain).
exact_args_f(meta_argtypes_guessed).
exact_args_f(meta_argtypes).
exact_args_f(ignore).
exact_args_f(format).
exact_args_f(dynamic).
exact_args_f(dmsg_pretty).
exact_args_f(call_u).
exact_args_f(say).
exact_args_f(call).
exact_args_f(assertz_if_new).
exact_args_f(asserts_eq_quitely).
exact_args_f(asserted).
exact_args_f(rtArgsVerbatum).
exact_args_f((  univ_safe  )).
exact_args_f((=)).
exact_args_f('$was_imported_kb_content$'):-!. %dtrace.
exact_args_f(F):-clause_b(rtArgsVerbatum(F)),!.
exact_args_f(F):-cheaply_u(prologBuiltin(F)),!.

:- source_location(F,_),asserta(absolute_source_location_pfc(F)).
% exact_args((_:-_)).
% exact_args((:-( _))).
% exact_args(C):-source_file(C,I),absolute_source_location_pfc(I).


:- module_transparent(is_stripped_module/1).


%= 	 	 

%% db_quf_l( ?Op, ?And, ?C12, ?Pre2, ?Templ2) is semidet.
%
% Database Quf (list Version).
%
db_quf_l(Op,And,[C],D2,D4):- !, db_quf(Op,C,D2,D3),!,D4  univ_safe  [And,D3].
db_quf_l(Op,And,C12,Pre2,Templ2):-db_quf_l_0(Op,And,C12,Pre2,Templ2).


%= 	 	 

%% db_quf_l_0( ?Op, ?And, :TermC, ?D2, ?D3) is semidet.
%
% Database quf (List version)  Primary Helper.
%
db_quf_l_0(Op,_And,[C],D2,D3):- db_quf(Op,C,D2,D3),!.
db_quf_l_0(Op, And,[C|C12],PreO,TemplO):-
  db_quf(Op,C,Pre,Next),
  db_quf_l_0(Op,And,C12,Pre2,Templ2),
  conjoin_l(Pre,Pre2,PreO),
  conjoin_op(And,Next,Templ2,TemplO).

%=  :- was_export(db_quf/4).

%= 	 	 

%% db_quf( +Op, ?C, ?Pretest, ?Template) is semidet.
%
% Database Quf.
%

db_quf(Op,C,Template):- db_quf(Op,C,true,Template),!.

db_quf(_ ,C,Pretest,Template):- (not_ftCompound(C)),!,must(Pretest=true),must(Template=C).
db_quf(Op,C,Pretest,Template):-is_ftVar(C),!,trace_or_throw_ex(var_db_quf(Op,C,Pretest,Template)).
db_quf(_ ,C,Pretest,Template):-as_is_term(C),!,must(Pretest=true),must(Template=C),!.

db_quf(Op,M:C,Pretest,M:Template):-atom(M),!,must(db_quf(Op,C,Pretest,Template)).

db_quf(Op,C,Pretest,Template):- C  univ_safe  [Holds,OBJ|ARGS],a(is_holds_true,Holds),atom(OBJ),!,C1  univ_safe  [OBJ|ARGS],must(db_quf(Op,C1,Pretest,Template)).
db_quf(_Op,C,true,C):- C  univ_safe  [Holds,OBJ|_],a(is_holds_true,Holds),is_ftVar(OBJ),!.
db_quf(Op,Sent,D2,D3):- Sent  univ_safe  [And|C12],C12=[_|_],is_sentence_functor(And),!, db_quf_l(Op,And,C12,D2,D3).
db_quf(Op,C,Pretest,Template):- C  univ_safe  [Prop,OBJ|ARGS],
      safe_functor(C,Prop,A),
      show_failure(why,translate_args(Op,Prop,A,OBJ,2,ARGS,NEWARGS,true,Pretest)),
      Template   univ_safe   [Prop,OBJ|NEWARGS],!.
db_quf(_Op,C,true,C).


%= 	 	 

%% translate_args( ?O, ?Prop, ?A, ?OBJ, ?N, :TermARG6, :TermARG7, ?GIN, ?GIN) is semidet.
%
% Translate Arguments.
%
translate_args(_O,_Prop,_A,_OBJ,_N,[],[],GIN,GIN).
translate_args(Op,Prop,A,OBJ,N1,[ARG|S],[NEW|ARGS],GIN,GOALS):-
   Type = argIsaFn(Prop,N1),
   translateOneArg(Op,Prop,OBJ,Type,ARG,NEW,GIN,GMID),
   N2 is N1 +1,
   translate_args(Op,Prop,A,OBJ,N2,S,ARGS,GMID,GOALS).


% ftVar

%= 	 	 

%% translateOneArg( ?Op, ?Prop, ?Obj, ?Type, ?VAR, ?VAR, ?G, ?G) is semidet.
%
% Translate One Argument.
%
translateOneArg(_Op,_Prop,_Obj,_Type,VAR,VAR,G,G):-is_ftVar(VAR),!.

% not an expression
translateOneArg(_O,_Prop,_Obj,_Type,ATOMIC,ATOMIC,G,G):-atomic(ATOMIC),!.
% translateOneArg(_O,_Prop,_Obj,Type,ATOMIC,ATOMICUSE,G,(G,same_arg(tCol(Type),ATOMIC,ATOMICUSE))):-atomic(ATOMIC),!.

% translateOneArg(_O,_Prop,_Obj,Type,VAR,VAR,G,G):-ignore(isa(VAR,Type)),!.

% props(Obj,size < 2).
translateOneArg(_O,Prop,Obj,Type,ARG,OLD,G,(GETTER,COMPARE,G)):-
       safe_functor(ARG,F,2), comparitiveOp(F),!,
       ARG  univ_safe  [F,Prop,VAL],
       GETTER  univ_safe  [Prop,Obj,OLD],
       COMPARE= compare_op(Type,F,OLD,VAL),!.

% props(Obj,isOneOf(Sz,[size+1,2])).
translateOneArg(Op,Prop,O,Type,isOneOf(VAL,LIST),VAL,G,(G0,G)):-
   translateListOps(Op,Prop,O,Type,VAL,LIST,G,G0).

% db_op(Op, Obj,size + 2).
translateOneArg(_O,Prop,Obj,_Type,ARG,NEW,G,(GETTER,STORE,G)):-
       ground(ARG),
       safe_functor(ARG,F,2), additiveOp(F),!,
       ARG  univ_safe  [F,Prop,VAL],
       GETTER  univ_safe  [Prop,Obj,OLD],
       STORE= update_value(OLD,VAL,NEW),!.

translateOneArg(_O,_Prop,_Obj,_Type,NART,NART,G,G):-!. % <- makes us skip the next bit of code
translateOneArg(_O,_Prop,_Obj,Type,ATOMIC,ATOMICUSE,G,(G,ignore(same_arg(tCol(Type),ATOMIC,ATOMICUSE)))).


%= 	 	 

%% translateListOps( ?O, ?Prop, ?Obj, ?Type, ?VAL, :TermARG6, ?G, ?G) is semidet.
%
% Translate List Oper.s.
%
translateListOps(_O,_Prop,_Obj,_Type,_VAL,[],G,G).
translateListOps(Op,Prop,Obj,Type,VAL,[L|LIST],G,GO2):-
   translateOneArg(Op,Prop,Obj,Type,L,VAL,G,G0),
   translateListOps(Op,Prop,Obj,Type,VAL,LIST,G0,GO2).


%= 	 	 

%% compare_op( ?Type, :PRED2F, ?OLD, ?VAL) is semidet.
%
% Compare Oper..
%
compare_op(Type,F,OLD,VAL):-nop(Type),show_call(why,(call(F,OLD,VAL))),!.


% load_motel:- defrole([],time_state,restr(time,period)).
% :-load_motel.

% ========================================
% expanded_different compares fact terms to see if they are different
% ========================================

:- '$hide'(expanded_different/2).
%=  :- was_export(expanded_different/2).


%= 	 	 

%% expanded_different( ?G0, ?G1) is semidet.
%
% Expanded Different.
%
expanded_different(G0,G1):-call(expanded_different_ic(G0,G1)).


%= 	 	 

%% expanded_different_ic( ?G0, ?G1) is semidet.
%
% Expanded Different Ic.
%
expanded_different_ic(G0,G1):-G0==G1,!,fail.
expanded_different_ic(G0,G1):-expanded_different_1(G0,G1),!.
expanded_different_ic(G0,G1):- G0\==G1.


%= 	 	 

%% expanded_different_1( ?G0, :TermG1) is semidet.
%
% expanded different  Secondary Helper.
%
expanded_different_1(NV:G0,G1):-is_ftNonvar(NV),!,expanded_different_1(G0,G1).
expanded_different_1(G0,NV:G1):-is_ftNonvar(NV),!,expanded_different_1(G0,G1).
expanded_different_1(G0,G1):- (is_ftVar(G0);is_ftVar(G1)),!,trace_or_throw_ex(expanded_different(G0,G1)).
expanded_different_1(G0,G1):- G0 \= G1,!.


% ========================================
% into_functor_form/3 (adds a second order safe_functor onto most predicates)
% ========================================
%=  :- was_export(into_functor_form/3).

%= 	 	 

%% into_functor_form( ?HFDS, ?X, ?O) is semidet.
%
% Converted To Functor Form.
%
into_functor_form(HFDS,M:X,M:O):- atom(M),! ,into_functor_form(HFDS,X,O),!.
into_functor_form(HFDS,X,O):-call((( X  univ_safe  [F|A],into_functor_form(HFDS,X,F,A,O)))),!.

% TODO finish negations

%= 	 	 

%% into_functor_form( ?Dbase_t, ?X, ?Dbase_t, ?A, ?X) is semidet.
%
% Converted To Functor Form.
%
into_functor_form(Dbase_t,X,Dbase_t,_A,X):-!.
into_functor_form(Dbase_t,_X,holds_t,A,Call):-Call  univ_safe  [Dbase_t|A].
into_functor_form(Dbase_t,_X,t,A,Call):-Call  univ_safe  [Dbase_t|A].
% into_functor_form(Dbase_t,_X,HFDS,A,Call):- a(is_holds_true,HFDS), Call  univ_safe  [Dbase_t|A].
into_functor_form(Dbase_t,_X,F,A,Call):-Call  univ_safe  [Dbase_t,F|A].


% these do not get defined!?%= :- kb_shared user_db:assert_user/2, user_db:grant_openid_server/2, user_db:retractall_grant_openid_server/2, user_db:retractall_user/2, user_db:assert_grant_openid_server/2.


:- fixup_exports.

:- export(pfc_expansion_file/0).
pfc_expansion_file.

:- module(pfc_gvars, []).

%:- use_module(library(must_trace)).
%:- use_module(library(dictoo_declarations)).
%:- use_module(library(dictoo)).



%$current_file.value = X :- prolog_load_context(file,X).

/*
:- listing(dot_cfg:dictoo_decl).
:- (debug(gvar(_)),debug(dictoo(_)),debug(mpred(_))).
:- rtrace((dot_eval($current_file, value, Out),writeln(Out))).
:- (nodebug(gvar(_)),nodebug(dictoo(_)),nodebug(mpred(_))).
*/

%:- rtrace.
%:- writeln($current_file.value).
%:- nortrace.

%:- break.
:- fixup_exports.
% All modules are declared here so that this next lines dont have to be pasted into every file.
% Since this list will need at least 160 entries to cover the obj classes rooms and commands, 
% we add the modules here to not waste 160^2 lines of text and having to not 
% update 160+ files whenever a new module is used
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%

:- include('pfc_header.pro').

% All modules are declared here so that this next lines dont have to be pasted into every file.
% Since this list will need at least 160 entries to cover the obj classes rooms and commands, 
% we add the modules here to not waste 160^2 lines of text and having to not 
% update 160+ files whenever a new module is used
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%

:-
 op(1199,fx,('==>')), 
 op(1190,xfx,('::::')),
 op(1180,xfx,('==>')),
 op(1170,xfx,'<==>'),  
 op(1160,xfx,('<-')),
 op(1150,xfx,'=>'),
 op(1140,xfx,'<='),
 op(1130,xfx,'<=>'), 
 op(600,yfx,'&'), 
 op(600,yfx,'v'),
 op(350,xfx,'xor'),
 op(300,fx,'~'),
 op(300,fx,'-').


:- thread_local(t_l:infSkipFullExpand/0).
:- thread_local(t_l:deduceArgTypes/1).
:- thread_local(t_l:noDBaseMODs/1).
:- thread_local(t_l:side_effect_buffer/3).
:- thread_local(t_l:loading_mpred_file/2).
:- thread_local(t_l:consulting_sources/0).
% HOOKS

:- forall(member(M:F/A,[
el_assertions:el_holds/10, %el_assertions
el_assertions:el_holds/11, %el_assertions
el_assertions:el_holds/12, %el_assertions
el_assertions:el_holds/13, %el_assertions
el_assertions:el_holds/14, %el_assertions
el_assertions:el_holds/4, %el_assertions
el_assertions:el_holds/5, %el_assertions
el_assertions:el_holds/6, %el_assertions
el_assertions:el_holds/7, %el_assertions
el_assertions:el_holds/8, %el_assertions
el_assertions:el_holds/9, %el_assertions
el_assertions:el_holds_pred_impl/1, %el_assertions
% el_assertions:is_cyckb_t_pred/2, %el_assertions
lmcache:has_pfc_database_preds/1,
lmcache:after_pfc_load/0,
lmcache:loaded_external_kbs/1,
% baseKB:agent_call_command/2,
baseKB:decl_coerce/3,
baseKB:coerce_hook/3, 
baseKB:hook_pfc_listing/1,
baseKB:hook_one_minute_timer_tick/0,
baseKB:hook_one_second_timer_tick/0, 
baseKB:isa_pred_now_locked/0,
baseKB:loaded_file_world_time/3, 
baseKB:loaded_mpred_file/2,
baseKB:module_local_init/0,
baseKB:pfc_hook_rescan_files/0, 
baseKB:pfc_provide_read_attributes/3, 
baseKB:pfc_provide_setup/4, 
baseKB:pfc_provide_storage_clauses/3, 
baseKB:pfc_provide_storage_op/2, 
baseKB:pfc_provide_write_attributes/2, 
baseKB:pfc_skipped_module/1, 
baseKB:mud_test/2,
baseKB:never_reload_file/1, 
baseKB:pfcManageHybrids/0, 
baseKB:regression_test/0,
baseKB:feature_test/0,
baseKB:sanity_test/0,
baseKB:regression_test/1,
baseKB:feature_test/1,
baseKB:sanity_test/1,
baseKB:type_action_info/3,
% pfc_online:semweb_startup/0,
baseKB:use_ideep_swi/0,
baseKB:cycPred/2,
baseKB:isa/2,
baseKB:cycPlus2/2,

user:portray/1,
user:prolog_load_file/2, 
%user:prolog_clause_name/2,
%user:prolog_list_goal/1,
%user:prolog_predicate_name/2,
user:term_expansion/2,user:goal_expansion/2,system:term_expansion/2,system:goal_expansion/2]),
  (multifile(M:F/A),M:module_transparent(M:F/A),dynamic(M:F/A),discontiguous(M:F/A))). 

:- discontiguous(module_local_init/2).
% ================================================
% Thread Locals
% ================================================
% DYN KB
:- thread_local(t_l:repl_to_string/2).
:- thread_local(t_l:repl_writer/2).

:- thread_local(t_l:agenda_slow_op_do_prereqs/0).
:- thread_local(t_l:agenda_suspend_scans/0).
:- thread_local(t_l:agent_current_action/2).
:- thread_local(t_l:already_in_file_term_expansion/0).
:- thread_local(t_l:assert_op_override/1).
:- thread_local(t_l:caller_module/2).
:- thread_local(t_l:consulting_sources/0).
:- thread_local(t_l:current_pttp_db_oper/1).
:- thread_local(t_l:deduceArgTypes/1).
:- thread_local(t_l:disable_px /0).
:- thread_local(t_l:enable_src_loop_checking/0).
:- thread_local(t_l:in_dynamic_reader/1).
:- thread_local(t_l:in_prolog_source_code/0).
:- thread_local(t_l:infAssertedOnly/1).
:- thread_local(t_l:infForward).
:- thread_local(t_l:infInstanceOnly/1).
:- thread_local(t_l:infMustArgIsa/0).
:- thread_local(t_l:infSecondOrder/0).
:- thread_local(t_l:infSkipArgIsa/0).
:- thread_local(t_l:infSkipFullExpand/0).
:- thread_local(t_l:infSupertypeName/0).
:- thread_local(t_l:infThirdOrder/0).
:- thread_local(t_l:into_form_code/0).
:- thread_local(t_l:inVoProp/0).
:- thread_local(t_l:is_calling/0).
:- thread_local(t_l:loading_mpred_file/2).
:- thread_local(t_l:pfc_ain_loaded/0).
:- thread_local(t_l:pfc_loads_file/0).
:- thread_local(t_l:pfc_opcall/2).
:- thread_local(t_l:pfc_run_paused/0).
:- thread_local(t_l:no_arg_type_error_checking/0).
:- thread_local(t_l:no_kif_var_coroutines/1).
:- thread_local(t_l:noDBaseHOOKS/1).
:- thread_local(t_l:noDBaseMODs/1).
:- thread_local(t_l:noRandomValues/1).
:- thread_local(t_l:print_mode/1).
:- thread_local(t_l:side_effect_buffer/3).
:- thread_local(t_l:side_effect_ok/0).
:- thread_local(t_l:tracing80/0).
:- thread_local(t_l:use_side_effect_buffer/0).
:- thread_local(t_l:useAltPOS/0).
:- thread_local(t_l:useOnlyExternalDBs/0).
:- thread_local(t_l:usePlTalk/0).
:- thread_local(t_l:verify_side_effect_buffer/0).
:- thread_local(t_l:with_callMPred/1).

end_of_file.



:- multifile(baseKB:'$exported_op'/3). 
:- discontiguous baseKB:'$exported_op'/3. 
:- dynamic baseKB:'$exported_op'/3. 
%:- multifile(system:term_expansion/2).
%:- multifile(user:term_expansion/2).
:- multifile(system:goal_expansion/2).
:- multifile(user:goal_expansion/2).
:- multifile '$si$':'$was_imported_kb_content$'/2.
:- dynamic '$si$':'$was_imported_kb_content$'/2.
:- discontiguous('$si$':'$was_imported_kb_content$'/2).

:- multifile(baseKB:module_local_init/2).
:- dynamic(baseKB:module_local_init/2).
:- discontiguous(baseKB:module_local_init/2).
/*
:- ensure_loaded(library(error)).
:- ensure_loaded(library(backcomp)).
:- ensure_loaded(library(occurs)).
:- ensure_loaded(library(gensym)).
:- ensure_loaded(library(apply)).
:- ensure_loaded(library(memfile)).
:- ensure_loaded(library(terms)).
:- ensure_loaded(library(listing)).
:- ensure_loaded(library(codesio)).
*/


:- op(1100,fx,(shared_multifile)).

                   
/*        
assert_if_new_hh(G):- (catch(G,_,fail)->true;assert(G)).
:- prolog_load_context(module,M),
 once((M==baseKB ;
   ((assert_if_new_hh(baseKB:mtProlog(M)),on_x_log_cont(nop(add_import_module(baseKB,M,end))))))).
*/
%:- multifile(user_db:grant_openid_server/2).

:- multifile(baseKB:coerce_hook/3).
:- dynamic(baseKB:coerce_hook/3).

:- dynamic(lmcache:loaded_external_kbs/1).
:- volatile(lmcache:loaded_external_kbs/1).

:- multifile(system:goal_expansion/2).
:- multifile(user:goal_expansion/2).
:- multifile '$si$':'$was_imported_kb_content$'/2.
:- dynamic '$si$':'$was_imported_kb_content$'/2.
:- discontiguous('$si$':'$was_imported_kb_content$'/2).


:- multifile '$si$':'$was_imported_kb_content$'/2.
:- dynamic '$si$':'$was_imported_kb_content$'/2.
:- discontiguous('$si$':'$was_imported_kb_content$'/2).

:- multifile baseKB:startup_option/2. 
:- dynamic baseKB:startup_option/2. 
:- multifile baseKB:pfc_system_status/2.
:- dynamic baseKB:pfc_system_status/2.
:- multifile(t_l:disable_px/0).
:- thread_local(t_l:disable_px/0).

:- multifile(baseKB:module_local_init/2).
:- dynamic(baseKB:module_local_init/2).
:- discontiguous(baseKB:module_local_init/2).
:- multifile(baseKB:coerce_hook/3).
:- dynamic(baseKB:coerce_hook/3).
:- dynamic(lmcache:loaded_external_kbs/1).
:- volatile(lmcache:loaded_external_kbs/1).
:- multifile(baseKB:argsQuoted/1).
:- dynamic(baseKB:argsQuoted/1).
:- dynamic(baseKB:resolveConflict/1).
:- dynamic(baseKB:agent_call_command/2).
:- export(baseKB:agent_call_command/2).
:- system:import(baseKB:agent_call_command/2).
:- dynamic(baseKB:pfc_skipped_module/1).

:- multifile( baseKB:predicateConventionMt/2).
:- dynamic( baseKB:predicateConventionMt/2).



% :- ensure_loaded(library(logicmoo/util/logicmoo_util_catch)).
% :- ensure_loaded(library(logicmoo/util/logicmoo_util_first)).

:- multifile(baseKB:ignore_file_mpreds/1).
:- dynamic(baseKB:ignore_file_mpreds/1).


:- multifile(baseKB:pfc_is_impl_file/1).
:- dynamic(baseKB:pfc_is_impl_file/1).

/*
:- prolog_load_context(source,O),
   (baseKB:pfc_is_impl_file(O)->(debug,dmsg(throw(baseKB:pfc_is_impl_file(O))),dumpsT,break);
     asserta(baseKB:pfc_is_impl_file(O))).
*/

:- if(\+ current_predicate(lm_util:register_pfc_impl_file/1)).
lm_util:register_pfc_impl_file(F):- (current_prolog_flag(xref,true)->true;
   must((((
    (baseKB:ignore_file_mpreds(F)->true;assertz(baseKB:ignore_file_mpreds(F))))),
   initialization((
   (if_defined(baseKB:ignore_file_mpreds(F),fail)->true;assertz(baseKB:ignore_file_mpreds(F))),
   ((baseKB:pfc_is_impl_file(F))->true;assertz(baseKB:pfc_is_impl_file(F)))),restore)))).
:- endif.

:- prolog_load_context(source,F),lm_util:register_pfc_impl_file(F).
:- prolog_load_context(file,F),lm_util:register_pfc_impl_file(F).



:- style_check(-singleton).
:- set_prolog_flag(generate_debug_info, true).


:-        op(1150,fx,(was_dynamic)),
          op(1150,fx,(was_multifile)),
          op(1150,fx,(was_module_transparent)),
          op(1150,fx,(was_export)),
          op(1150,fx,(shared_multifile)).




:- prolog_load_context(module,M),
 once((M==baseKB;
   ((assert_if_new(baseKB:mtProlog(M)),
   nop(on_x_log_cont(add_import_module(baseKB,M,end))))))).

:-((current_prolog_flag(xref,true)->true;
    (   (prolog_load_context(source,F),
   initialization((
   (if_defined(baseKB:ignore_file_mpreds(F),fail)->true;assertz(baseKB:ignore_file_mpreds(F))),
   ((baseKB:pfc_is_impl_file(F))->true;assertz(baseKB:pfc_is_impl_file(F)))),now))))).


:- virtualize_source_file.

/* Part of LogicMOO Base Logicmoo Debug Tools
% ===================================================================
%   File   : pfcWhy.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Updated:
%   Purpose: predicates for interactively exploring Pfc justifications.

% ***** predicates for brousing justifications *****
% ===================================================================
*/

%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).

%:- throw(module(pfcumt,[umt/1])).

%:- module(pfc_justify, []).

%:- use_module(pfc_kb_ops).
%:- use_module(library(util_varnames)).
%:- use_module(library(no_repeats)).

:- include('pfc_header.pi').

%:- endif.

%   File   : pfcjust.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Author :  Dave Matuszek, dave@prc.unisys.com
%   Updated:
%   Purpose: predicates for accessing Pfc justifications.
%   Status: more or less working.
%   Bugs:

%  *** predicates for exploring supports of a fact *****

justification(F,J):- supporters_list(F,J).

justifications(F,Js):- bagof_nr(J,justification(F,J),Js).

:- set_prolog_flag(expect_mpred_file,never).

pfcWhy(M:Conseq,Ante):- atom(M),!,M:pfcWhy_2(Conseq,Ante).

pfcWhy(Conseq,Ante):- pfcWhy_2(Conseq,Ante).

pfcWhy_2(Conseq,Ante):- var(Conseq),!,pfc_children(Ante,Conseq).
pfcWhy_2(Conseq,Ante):- justifications(Conseq,Ante).



pfc_info(O):-
 with_output_to(user_error,
 ((dmsg_pretty("======================================================================="),
  listing(O),
  dmsg_pretty("======================================================================="),
  quietly(call_with_inference_limit(ignore(on_xf_cont(deterministically_must(pfcWhy_1(O)))),4000,_)),
  dmsg_pretty("======================================================================="),
  must_maplist(mp_printAll(O),
  [   pfc_db_type(O,v),  
      +(pfc_child(O,v)),
      % mpred_fact(O),
      pfc_axiom(O),
      well_founded(O),
      pfc_supported(local,O),
      pfc_supported(cycles,O),
      pfc_assumption(O),
      get_pfc_is_tracing(O)]),
 dmsg_pretty("=======================================================================")))).

mp_printAll(S,+(O)):- subst(O,v,V,CALL),CALL\==O,!,
  subst(O,S,s,NAME),safe_functor(O,F,_),!,
  nl,flush_output, fmt("=================="),wdmsg_pretty(NAME),wdmsg_pretty("---"),flush_output,!,
  doall(((flush_output,(CALL),flush_output)*->fmt9(V);(fail=F))),nl,fmt("=================="),nl,flush_output.
mp_printAll(S,call(O)):- !,
  subst(O,S,s,NAME),
  nl,flush_output,fmt("=================="),wdmsg_pretty(NAME),wdmsg_pretty("---"),flush_output,!,
  doall(((flush_output,deterministically_must(O),flush_output)*->true;wdmsg_pretty(false=NAME))),fmt("=================="),nl,flush_output.
mp_printAll(S,(O)):- subst(O,v,V,CALL),CALL\==O,!,
  subst(O,S,s,NAME),safe_functor(O,F,_),
  nl,flush_output, fmt("=================="),wdmsg_pretty(NAME),wdmsg_pretty("---"),flush_output,!,
  doall(((flush_output,deterministically_must(CALL),flush_output)*->fmt9(V);(fail=F))),nl,fmt("=================="),nl,flush_output.
mp_printAll(S,(O)):-  !,  safe_functor(O,F,A),mp_nnvv(S,O,F,A),flush_output.
mp_nnvv(_,(O),F,1):- !, doall(((flush_output,deterministically_must(O),flush_output)*->wdmsg_pretty(+F);wdmsg_pretty(-F))).
mp_nnvv(S,(O),_,_):- !, subst(O,S,s,NAME), !,
  doall(((flush_output,deterministically_must(O),flush_output)*->wdmsg_pretty(-NAME);wdmsg_pretty(+NAME))).






%%  pfc_basis_list(+P,-L)
%
%  is true iff L is a list of "base" facts which, taken
%  together, allows us to deduce P.  A mpred "based on" list fact is an axiom (a fact
%  added by the user or a raw Prolog fact (i.e. one w/o any support))
%  or an assumption.
%
pfc_basis_list(F,[F]):- (pfc_axiom(F) ; pfc_assumption(F)),!.

pfc_basis_list(F,L):-
  % i.e. (reduce 'append (map 'pfc_basis_list (justification f)))
  justification(F,Js),
  bases_union(Js,L).


%%  bases_union(+L1,+L2).
%
%  is true if list L2 represents the union of all of the
%  facts on which some conclusion in list L1 is based.
%
bases_union([],[]).
bases_union([X|Rest],L):-
  pfc_basis_list(X,Bx),
  bases_union(Rest,Br),
  pfc_union(Bx,Br,L).

%pfc_axiom(F):- !, % Like OLD TODO
%  pfc_get_support(F,(_,ax)).
pfc_axiom(F):-
  pfc_get_support(F,UU),
  is_user_reason(UU),!.

%% pfc_assumption(P)
%
%  an pfc_assumption is a failed goal, i.e. were assuming that our failure to
%  prove P is a proof of not(P)
%
pfc_assumption(P):- !, % Like OLD TODO
  nonvar(P), pfc_unnegate(P,_).
pfc_assumption(P):- nonvar(P), 
  pfc_unnegate(P,N), 
 % fail,
  % added prohibited_check
  (current_prolog_flag(explicitly_prohibited_check,false) -> true ; \+ pfc_axiom(~ N)).


:- set_prolog_flag(explicitly_prohibited_check,false).

%% pfc_assumptions( +X, +AsSet) is semidet.
%
% true if AsSet is a set of assumptions which underly X.
%
pfc_assumptions(X,[X]):- pfc_assumption(X).
pfc_assumptions(X,[]):- pfc_axiom(X).
pfc_assumptions(X,L):-
  justification(X,Js),
  do_assumpts(Js,L).


%% do_assumpts(+Set1,?Set2) is semidet.
%
% Assumptions Secondary Helper.
%
do_assumpts([],[]).
do_assumpts([X|Rest],L):-
  pfc_assumptions(X,Bx),
  do_assumpts(Rest,Br),
  pfc_union(Bx,Br,L).


%  pfc_proofTree(P,T) the proof tree for P is T where a proof tree is
%  of the form
%
%      [P , J1, J2, ;;; Jn]         each Ji is an independent P justifier.
%           ^                         and has the form of
%           [J11, J12,... J1n]      a list of proof trees.


%% pfc_child(+P,?Q) is semidet.
%
% is true iff P is an immediate justifier for Q.
%
pfc_child(P,Q):- is_list(P),!,maplist(pfc_child,P,Q).
pfc_child(P,Q):-
  pfc_get_support(Q,(P,_)).
pfc_child(P,Q):-
  pfc_get_support(Q,(_,Trig)),
  pfc_db_type(Trig,trigger(_TT)),
  pfc_child(P,Trig).


%% pfc_children(+P, ?L) is semidet.
%
% PFC Children.
%
pfc_children(P,L):- bagof_nr(C,pfc_child(P,C),L).



%% pfc_descendant(+P, ?Q) is semidet.
%
% pfc_descendant(P,Q) is true iff P is a justifier for Q.
%
pfc_descendant(P,Q):-
   pfc_descendant1(P,Q,[]).


%% pfc_descendant1(+P, ?Q, ?Seen) is semidet.
%
% PFC Descendant Secondary Helper.
%
pfc_descendant1(P,Q,Seen):-
  pfc_child(X,Q),
  (\+ member(X,Seen)),
  (P=X ; pfc_descendant1(P,X,[X|Seen])).


%% pfc_descendants(+P, ?L) is semidet.
%
% PFC Descendants.
%
pfc_descendants(P,L):-
  bagof_nr(Q,pfc_descendant1(P,Q,[]),L).

:- meta_predicate(bagof_nr(?,^,*)).
bagof_nr(T,G,B):- no_repeats(B,(bagof(T,G,B))).
:- meta_predicate(bagof_or_nil(?,^,-)).
bagof_or_nil(T,G,B):- (bagof_nr(T,G,B) *-> true; B=[]).


:- meta_predicate(sanity_check(0,0)).
sanity_check(When,Must):- When,Must,!.
sanity_check(When,Must):- must_ex((show_call(When),Must)),!.

%
%  predicates for manipulating support relationships
%

notify_if_neg_trigger(spft(P,Fact,Trigger)):- 
  (Trigger= nt(F,Condition,Action) ->
    (pfc_trace_msg('~N~n\tAdding NEG pfc_do_fcnt via support~n\t\ttrigger: ~p~n\t\tcond: ~p~n\t\taction: ~p~n\t from: ~p~N',
      [F,Condition,Action,pfc_add_support_fast(P,(Fact,Trigger))]));true).

%  pfc_add_support(+Fact,+Support)
pfc_add_support(P,(Fact,Trigger)):-
  MSPFT = spft(P,Fact,Trigger),
   fix_mp(pfc_add_support,MSPFT,M,SPFT),
   M:notify_if_neg_trigger(SPFT),
  M:(clause_asserted_u(SPFT)-> true; sanity_check(assertz_mu(SPFT),clause_asserted_u(SPFT))).

%  pfc_add_support_fast(+Fact,+Support)
pfc_add_support_fast(P,(Fact,Trigger)):-
      MSPFT = spft(P,Fact,Trigger),
       fix_mp(pfc_add_support,MSPFT,M,SPFT),
   M:notify_if_neg_trigger(SPFT),
   M:sanity_check(assertz_mu(SPFT),clause_asserted_u(SPFT)).


                                                                
:- meta_predicate(pfc_get_support(*,-)).

pfc_get_support((H:-B),(Fact,Trigger)):- 
   lookup_u(spft((H <- B),_,_),Ref),
   clause(spft(HH<-BB,Fact,Trigger),true,Ref),
   clause_ref_module(Ref),   
   H=@=HH,B=@=BB.
pfc_get_support(P,(Fact,Trigger)):-
  lookup_spft(P,Fact,Trigger).


pfc_get_support_why(P,FT):-
  (pfc_get_support_perfect(P,FT)*->true;
   (pfc_get_support_deeper(P,FT))).

pfc_get_support_perfect(P,(Fact,Trigger)):-
   lookup_spft_match_first(P,Fact,Trigger).

pfc_get_support_deeper((H:-B),(Fact,Trigger)):- (nonvar(H) -> ! ; true),
 lookup_u(spft((H <- B),_,_),Ref),
  clause(spft(HH<-BB,Fact,Trigger),true,Ref),
  H=@=HH,B=@=BB.

pfc_get_support_deeper(P,(Fact,Trigger)):-
    lookup_spft_match_deeper(P,Fact,Trigger).

lookup_spft_match(A,B,C):- copy_term(A,AA),lookup_spft(A,B,C),A=@=AA.

lookup_spft_match_deeper(H,Fact,Trigger):- 
  copy_term(H,HH),
  lookup_spft((H:- _B),Fact,Trigger),
  H=@=HH.

lookup_spft_match_first(A,B,C):- nonvar(A),!, 
  no_repeats(((lookup_spft_match(A,B,C);lookup_spft(A,B,C)))).

lookup_spft_match_first(A,B,C):- lookup_spft(A,B,C).


lookup_spft(A,B,C):- !, lookup_u(spft(A,B,C)).
% cutted above
/*
lookup_spft(A,B,C):- nonvar(A),!,lookup_spft_p(A,B,C).
lookup_spft(A,B,C):- var(B),!,lookup_spft_t(A,B,C).
lookup_spft(A,B,C):- lookup_spft_f(A,B,C).

lookup_spft_p(A,B,C):- with_some_vars_locked(A,lookup_u(spft(A,B,C))).
% TODO UNCOMMENT MAYBE IF NEEDED lookup_spft_p(A,B,C):- full_transform(lookup,A,AA),!,A\=@=AA,!,show_pfc_success(baseKB:spft(AA,B,C)).

lookup_spft_f(A,B,C):- with_some_vars_locked(B,lookup_u(spft(A,B,C))).
% TODO UNCOMMENT MAYBE IF NEEDED lookup_spft_f(A,B,C):- full_transform(lookup,B,BB),!,B\=@=BB,!,show_pfc_success(baseKB:spft(A,BB,C)).

lookup_spft_t(A,B,C):- lookup_u(spft(A,B,C)).
*/
/*
%  TODO MAYBE
pfc_get_support(F,J):-
  full_transform(pfc_get_support,F,FF),!,
  F\==FF,pfc_get_support(FF,J).
*/

pfc_rem_support_if_exists(P,(Fact,Trigger)):-
  lookup_spft(P,Fact,Trigger),
  pfc_retract_i_or_warn(spft(P,Fact,Trigger)).


pfc_rem_support(P,(Fact,Trigger)):-
  closest_u(spft(P,Fact,Trigger),spft(P,FactO,TriggerO)),
  pfc_retract_i_or_warn_1(spft(P,FactO,TriggerO)).
pfc_rem_support(P,S):-
  pfc_retract_i_or_warn(spft(P,Fact,Trigger)),
  ignore((Fact,Trigger)=S).



closest_u(Was,WasO):-clause_asserted_u(Was),!,Was=WasO.
closest_u(Was,WasO):-lookup_u(Was),!,Was=WasO,!.
closest_u(Was,WasO):-lookup_u(WasO),ignore(Was=WasO),!.
closest_u(H,HH):- ref(_) = Result,closest_uu(H,H,HH,Result),ref(Ref)= Result,
  (H==HH -> true ; nonvar(Ref)),!.

closest_uu(H,P,PP):- copy_term(H+P,HH+PP),
      ((lookup_u(HH)*-> (=@=(P,PP)->(!,HH=H);(fail));(!,fail));(true)).
closest_uu(H,P,PP,Result):-
      sanity(Result=@=ref(Ref)),
      (copy_term(H+P,HH+PP),
      ((lookup_u(HH,Ref)*-> (=@=(P,PP)->(!,HH=H);
          (nb_setarg(1,Result,Ref),fail));(!,fail));((clause(HH,B,Ref),must_ex(B))))).

/*
*/

pfc_collect_supports(Tripples):-
  bagof_or_nil(Tripple, pfc_support_relation(Tripple), Tripples).

pfc_support_relation((P,F,T)):- lookup_spft(P,F,T).

pfc_make_supports((P,S1,S2)):-
  pfc_add_support(P,(S1,S2)),
  (pfc_ain_object(P); true),
  !.


pp_why:-pfcWhy.

pfcWhy:-
  call(t_l:whybuffer(P,_)),
  pfcWhy_1(P).

pp_why(A):-pfcWhy_1(A).

clear_proofs:- retractall(t_l:whybuffer(_P,_Js)),color_line(cyan,1).


:- thread_local(t_l:shown_why/1).

% see pfcWhy

:- export(with_no_english/1).
:- meta_predicate(with_no_english(*)).
with_no_english(Goal):- setup_call_cleanup(flag('english', Was, 0),Goal,flag('english', _, Was )).

pfcWhy(P):- clear_proofs,!,with_no_english((must(pfcWhy_1(P)))).

pfcWhy_1(M:P):-  atom(M),!,call_from_module(M,pfcWhy_1(P)).
pfcWhy_1(NX):- number(NX),!, trace, pfcWhy0(NX),!.
pfcWhy_1(P):- is_list(P), !, maplist(pfcWhy_1, P).
pfcWhy_1(P):- ((callable(P), ((must_ex((pfcWhy_justs(P))))))) *-> true ; pfcWhy_1_fallback(P).

pfcWhy_1_fallback(NX):-  
  (number(NX)-> true ; clear_proofs),
  trace,
  pfcWhy0(NX),!.
pfcWhy_1_fallback(P):- pfcWhy_sub(P).

% pfcWhy_1(N):- number(N),!, call(t_l:whybuffer(P,Js)), pfc_handle_why_command(N,P,Js).

pfcWhy_justs(P):- pfcWhy_justs_1a(P)*->true;forall(pfcWhy_justs_1b(P),true).
  
pfcWhy_justs_1a(P) :-    
  color_line(green,2),!,
  findall(Js,((no_repeats(P-Js,(justifications(P,Js))),
    must((color_line(yellow,1),
      ignore(pfcShowJustifications(P,Js)))))),Count),
  (Count==[]-> format("~N No justifications for ~p. ~n~n",[P]) ; true),
  color_line(green,2).

pfcWhy_justs_1b(P) :- term_variables(P,VarsPC), 
  ((call_u_no_bc(P),pfcWhy_justs_1a(P))*-> 
  (term_variables(P,VarsAC),(VarsPC==VarsAC->!;true));
   pfcWhy_justs_1a(P)).

/*
pfcWhy_justs_2(P) :-    
  color_line(green,2),!,
  findall(Js,((no_repeats(P-Js,deterministically_must(justifications(P,Js))),
    must((color_line(yellow,1),
      ignore(pfcShowJustifications(P,Js)))))),Count),
  (Count==[]-> format("~N No justifications for ~p. ~n~n",[P]) ; true),
  color_line(green,2).
*/
/*

pfcWhy_1(P):- loop_check(quietly_ex((must_ex(pfcWhy_try_each(P)),color_line(green,2))),true).

% user:pfcWhy_1((user:prolog_exception_hook(A, B, C, D) :- exception_hook(A, B, C, D))).
% pfcWhy_1((prolog_exception_hook(A, B, C, D) :- exception_hook(A, B, C, D))).

pfcWhy_try_each(MN):- strip_module(MN,_,N),number(N),!,pfcWhy0(N),!.

pfcWhy_try_each(ain(H)):-!,pfcWhy_try_each(H).
pfcWhy_try_each(call_u(H)):-!,pfcWhy_try_each(H).
pfcWhy_try_each(clause(H,B)):-!,pfcWhy_try_each(H:-B).
pfcWhy_try_each(clause(H,B,_)):-!,pfcWhy_try_each(H:-B).
pfcWhy_try_each(clause_u(P)):-!,pfcWhy_try_each(P).
pfcWhy_try_each(clause_u(H,B)):-!,pfcWhy_try_each(H:-B).
pfcWhy_try_each(clause_u(H,B,_)):-!,pfcWhy_try_each(H:-B).

pfcWhy_try_each(P):- once((retractall(t_l:whybuffer(P,_)),color_line(green,2),
    show_current_source_location,format("~NJustifications for ~p:",[P]))),
    fail.

pfcWhy_try_each(P):- pfcWhy_try_each_0(P),!.
pfcWhy_try_each(P):- pfcWhy_sub(P),!.
pfcWhy_try_each(M:P :- B):- atom(M),call_from_module(M,pfcWhy_try_each_0(P:-B)),!.
pfcWhy_try_each(M:P):- atom(M),call_from_module(M,pfcWhy_try_each_0(P)),!.
pfcWhy_try_each(P :- B):- is_true(B),!,pfcWhy_try_each(P ).
pfcWhy_try_each(M:H):- strip_module(H,Ctx,P),P==H,Ctx==M,!,pfcWhy_try_each(H).
pfcWhy_try_each(_):- format("~N No justifications. ~n").

pfcWhy_try_each_0(P):- findall(Js,pfcWhy_try_each_1(P,Js),Count),Count\==[],!.
pfcWhy_try_each_0(\+ P):- pfcWhy_try_each_0(~P)*->true;(call_u(\+ P),wdmsgl(why:- \+ P)),!.

pfcWhy_try_each_1(P,Js):-
  ((no_repeats(P-Js,deterministically_must(justifications(P,Js))),
    ((color_line(yellow,1), pfcShowJustifications(P,Js))))).
pfcWhy_try_each_1(\+ P,[MFL]):- !, find_mfl(P,MFL),ansi_format([fg(cyan)],"~N    ~q",[MFL]),fail.
pfcWhy_try_each_1( P,[MFL]):-  find_mfl(P,MFL), \+ clause_asserted(t_l:shown_why(MFL)), ansi_format([fg(cyan)],"~N    ~q",[MFL]).

*/
pfcWhy0(N) :-
  number(N),
  !,
  t_l:whybuffer(P,Js),
  pfcWhyCommand0(N,P,Js).

pfcWhy0(P) :-
  justifications(P,Js),  
  assert(t_l:whybuffer(P,Js)),                     
  pfcWhyBrouse(P,Js).

pfcWhy1(P) :-
  justifications(P,Js),
  pfcWhyBrouse(P,Js).

pfcWhyBrouse(P,Js) :-    % non-interactive
  pfcShowJustifications(P,Js),source_file(_,_),!.

pfcWhyBrouse(P,Js) :- 
  pfcShowJustifications(P,Js),
  ttyflush,
  read_pending_chars(current_input,_,[]),!,
  ttyflush,
  % pfcAsk(' >> ',Answer),
  % read_pending_chars(current_input,[Answer|_],[]),!,  
  format('~N',[]),write('proof [q/h/u/?.?]: '),get_char(Answer),
  pfcWhyCommand0(Answer,P,Js).

pfcWhyCommand0(q,_,_) :- !.
pfcWhyCommand0(h,_,_) :- 
  !,
  format("~n
Justification Brouser Commands:
 q   quit.
 N   focus on Nth justification.
 N.M brouse step M of the Nth justification
 u   up a level
",
 []).

pfcWhyCommand0(N,_P,Js) :-
  float(N),
  !,
  pfcSelectJustificationNode(Js,N,Node),
  pfcWhy1(Node).

pfcWhyCommand0(u,_,_) :-
  % u=up
  !.

pfcWhyCommand0(N,_,_) :-
  integer(N),
  !,
  format("~n~w is a yet unimplemented command.",[N]),
  fail.

pfcWhyCommand0(X,_,_) :-
 format("~n~w is an unrecognized command, enter h. for help.",[X]),
 fail.

reset_shown_justs:- retractall(t_l:shown_why(_)),color_line(red,1).
  
pfcShowJustifications(P,Js) :-
  show_current_source_location,
  reset_shown_justs,
  color_line(yellow,1),
  format("~N~nJustifications for ~p:~n",[P]),  

  pfcShowJustification1(Js,1),!.

pfcShowJustification1([],_):-!.
pfcShowJustification1([J|Js],N) :- !,
  % show one justification and recurse.    
  reset_shown_justs,
  pfcShowSingleJust(N,step(1),J),!,
  N2 is N+1,  
  pfcShowJustification1(Js,N2).

pfcShowJustification1(J,N) :- 
  reset_shown_justs, % nl,
  pfcShowSingleJust(N,step(1),J),!.

incrStep(StepNo,Step):-arg(1,StepNo,Step),X is Step+1,nb_setarg(1,StepNo,X).

pfcShowSingleJust(JustNo,StepNo,C):- is_ftVar(C),!,incrStep(StepNo,Step),
  ansi_format([fg(cyan)],"~N    ~w.~w ~w ",[JustNo,Step,C]),!.
pfcShowSingleJust(_JustNo,_StepNo,[]):-!.
pfcShowSingleJust(JustNo,StepNo,(P,T)):-!, 
  pfcShowSingleJust(JustNo,StepNo,P),
  pfcShowSingleJust(JustNo,StepNo,T).
pfcShowSingleJust(JustNo,StepNo,(P,F,T)):-!, 
  pfcShowSingleJust1(JustNo,StepNo,P),
  pfcShowSingleJust(JustNo,StepNo,F),
  pfcShowSingleJust1(JustNo,StepNo,T).
pfcShowSingleJust(JustNo,StepNo,(P*->T)):-!, 
  pfcShowSingleJust1(JustNo,StepNo,P),format('      *-> ',[]),
  pfcShowSingleJust1(JustNo,StepNo,T).

pfcShowSingleJust(JustNo,StepNo,(P:-T)):-!, 
  pfcShowSingleJust1(JustNo,StepNo,P),format(':- ~p.',[T]).
 
pfcShowSingleJust(JustNo,StepNo,(P : -T)):-!, 
  pfcShowSingleJust1(JustNo,StepNo,P),format('      :- ',[]),
  pfcShowSingleJust(JustNo,StepNo,T).

pfcShowSingleJust(JustNo,StepNo,(P :- T) ):- !, 
  pfcShowSingleJust1(JustNo,StepNo,call(T)),  
  pfcShowSingleJust1(JustNo,StepNo,P).


pfcShowSingleJust(JustNo,StepNo,[P|T]):-!, 
  pfcShowSingleJust(JustNo,StepNo,P),
  pfcShowSingleJust(JustNo,StepNo,T).

pfcShowSingleJust(JustNo,StepNo,pt(P,Body)):- !, 
  pfcShowSingleJust1(JustNo,StepNo,pt(P)),  
  pfcShowSingleJust(JustNo,StepNo,Body).

pfcShowSingleJust(JustNo,StepNo,C):- 
 pfcShowSingleJust1(JustNo,StepNo,C).

fmt_cl(P):- \+ \+ (numbervars(P,126,_,[attvar(skip),singletons(true)]),write_term(P,[portray(true)])).

unwrap_litr(C,CCC+VS):- copy_term(C,CC,VS),
  numbervars(CC+VS,0,_),
  unwrap_litr0(CC,CCC),!.
unwrap_litr0(call(C),CC):-unwrap_litr0(C,CC).
unwrap_litr0(pt(C),CC):-unwrap_litr0(C,CC).
unwrap_litr0(body(C),CC):-unwrap_litr0(C,CC).
unwrap_litr0(head(C),CC):-unwrap_litr0(C,CC).
unwrap_litr0(C,C).

pfcShowSingleJust1(JustNo,StepNo,C):- unwrap_litr(C,CC),!,pfcShowSingleJust4(JustNo,StepNo,C,CC).
pfcShowSingleJust4(_,_,_,CC):- t_l:shown_why(C),C=@=CC,!.
pfcShowSingleJust4(JustNo,StepNo,C,CC):- assert(t_l:shown_why(CC)),!,
   incrStep(StepNo,Step),
   ansi_format([fg(cyan)],"~N    ~w.~w ~@ ",[JustNo,Step,fmt_cl(C)]),   
   pfcShowSingleJust_C(C),!.

pfcShowSingleJust_C(C):-is_file_ref(C),!.
pfcShowSingleJust_C(C):-find_mfl(C,MFL),assert(t_l:shown_why(MFL)),!,pfcShowSingleJust_MFL(MFL).
pfcShowSingleJust_C(_):-ansi_format([hfg(black)]," % [no_mfl] ",[]),!.

short_filename(F,FN):- atomic_list_concat([_,FN],'/pack/',F),!.
short_filename(F,FN):- atomic_list_concat([_,FN],swipl,F),!.
short_filename(F,FN):- F=FN,!.

pfcShowSingleJust_MFL(MFL):- MFL=mfl4(VarNameZ,_M,F,L),atom(F),short_filename(F,FN),!,varnames_load_context(VarNameZ),
   ansi_format([hfg(black)]," % [~w:~w] ",[FN,L]).
pfcShowSingleJust_MFL(MFL):- ansi_format([hfg(black)]," % [~w] ",[MFL]),!.

pfcAsk(Msg,Ans) :-
  format("~n~w",[Msg]),
  read(Ans).

pfcSelectJustificationNode(Js,Index,Step) :-
  JustNo is integer(Index),
  nth1(JustNo,Js,Justification),
  StepNo is 1+ integer(Index*10 - JustNo*10),
  nth1(StepNo,Justification,Step).







pfcWhy_maybe(_,(F:-P)):-!,wdmsgl(F:-P),!.
pfcWhy_maybe(F,P):-wdmsgl(F:-P),!.
pfcWhy_maybe(_,P):-ignore(pfcWhy_1(P)).

pfcWhy_sub(P):- trace, loop_check(pfcWhy_sub0(P),true).
pfcWhy_sub0(P):- pfcWhy_2(P,Why),!,wdmsg_pretty(:-pfcWhy_1(P)),wdmsgl(pfcWhy_maybe(P),Why).
pfcWhy_sub0(P):-loop_check(pfcWhy_sub_lc(P),trace_or_throw_ex(pfcWhy_sub_lc(P)))-> \+ \+ call(t_l:whybuffer(_,_)),!.
pfcWhy_sub_lc(P):- 
  justifications(P,Js),
  nb_setval('$last_printed',[]),
  clear_proofs,
  assertz(t_l:whybuffer(P,Js)),
  pfcWhyBrouse(P,Js).
  

pfcWhy_sub_sub(P):-
  justifications(P,Js),
  clear_proofs,
  % retractall_u(t_l:whybuffer(_,_)),
  (nb_hasval('$last_printed',P)-> dmsg_pretty(hasVal(P)) ;
   ((
  assertz(t_l:whybuffer(P,Js)),
   nb_getval('$last_printed',LP),
   ((pfc_pp_db_justification1(LP,Js,1),fmt('~N~n',[])))))).

nb_pushval(Name,Value):-nb_current(Name,Before)->nb_setval(Name,[Value|Before]);nb_setval(Name,[Value]).
nb_peekval(Name,Value):-nb_current(Name,[Value|_Before]).
nb_hasval(Name,Value):-nb_current(Name,List),member(Value,List).
nb_popval(Name,Value):-nb_current(Name,[Value|Before])->nb_setval(Name,Before).

pfcWhy1(P):-
  justifications(P,Js),
  pfcWhyBrouse(P,Js).

% non-interactive
pfcWhyBrouse(P,Js):-
   must_ex(quietly_ex(in_cmt((pfc_pp_db_justifications(P,Js))))), !.

% Interactive
pfcWhyBrouse(P,Js):-
  pfc_pp_db_justifications(P,Js),
  pfc_prompt_ask(' >> ',Answer),
  pfc_handle_why_command(Answer,P,Js).

pfc_handle_why_command(q,_,_):- !.
pfc_handle_why_command(h,_,_):-
  !,
  format("~N
Justification Brouser Commands:
 q   quit.
 N   focus on Nth justification.
 N.M brouse step M of the Nth justification
 user   up a level ~n",
  []).

pfc_handle_why_command(N,_ZP,Js):-
  float(N),
  !,
  pfc_select_justification_node(Js,N,Node),
  pfcWhy1(Node).

pfc_handle_why_command(u,_,_):-
  % u=up
  !.

pfc_unhandled_command(N,_,_):-
  integer(N),
  !,
  format("~N~p is a yet unimplemented command.",[N]),
  fail.

pfc_unhandled_command(X,_,_):-
 format("~N~p is an unrecognized command, enter h. for help.",[X]),
 fail.

pfc_pp_db_justifications(P,Js):-
 show_current_source_location, 
 must_ex(quietly_ex(( format("~NJustifications for ~p:",[P]),
  pfc_pp_db_justification1('',Js,1)))).

pfc_pp_db_justification1(_Prefix,[],_).

pfc_pp_db_justification1(Prefix,[J|Js],N):-
  % show one justification and recurse.
  nl,  
  pfc_pp_db_justifications2(Prefix,J,N,1),
  reset_shown_justs,
  N2 is N+1,
  pfc_pp_db_justification1(Prefix,Js,N2).

pfc_pp_db_justifications2(_Prefix,[],_,_).

pfc_pp_db_justifications2(Prefix,[C|Rest],JustNo,StepNo):-
(nb_hasval('$last_printed',C)-> dmsg_pretty(chasVal(C)) ;
(
 (StepNo==1->fmt('~N~n',[]);true),
  sformat(LP,' ~w.~p.~p',[Prefix,JustNo,StepNo]),
  nb_pushval('$last_printed',LP),
  format("~N  ~w ~p",[LP,C]),
  ignore(loop_check(pfcWhy_sub_sub(C))),
  StepNext is 1+StepNo,
  pfc_pp_db_justifications2(Prefix,Rest,JustNo,StepNext))).

pfc_prompt_ask(Info,Ans):-
  format("~N~p",[Info]),
  read(Ans).

pfc_select_justification_node(Js,Index,Step):-
  JustNo is integer(Index),
  nth1(JustNo,Js,Justification),
  StepNo is 1+ integer(Index*10 - JustNo*10),
  nth1(StepNo,Justification,Step).


%%  pfc_supported(+P) is semidet.
%
%  succeeds if P is "supported". What this means
%  depends on the TMS mode selected.
%
pfc_supported(P):-
  must_ex(get_tms_mode(P,Mode))->
  pfc_supported(Mode,P).

%%  pfc_supported(+TMS,+P) is semidet.
%
%  succeeds if P is "supported". What this means
%  depends on the TMS mode supplied.
%
pfc_supported(local,P):- !, pfc_get_support(P,_),!, not_rejected(P).
pfc_supported(cycles,P):-  !, well_founded(P),!, not_rejected(P).
pfc_supported(How,P):- ignore(How=unknown),not_rejected(P).

not_rejected(~P):- nonvar(P),  \+ pfc_get_support(P,_).
not_rejected(P):-  \+ pfc_get_support(~P,_).

%% well_founded(+Fact) is semidet.
%
% a fact is well founded if it is supported by the user
%  or by a set of facts and a rules, all of which are well founded.
%
well_founded(Fact):- each_E(well_founded_0,Fact,[_]).

well_founded_0(F,_):-
  % supported by user (axiom) or an "absent" fact (assumption).
  (pfc_axiom(F) ; pfc_assumption(F)),
  !.

well_founded_0(F,Descendants):-
  % first make sure we aren't in a loop.
  (\+ memberchk(F,Descendants)),
  % find a justification.
  supporters_list0(F,Supporters),!,
  % all of whose members are well founded.
  well_founded_list(Supporters,[F|Descendants]),
  !.

%%  well_founded_list(+List,-Decendants) is det.
%
% simply maps well_founded over the list.
%
well_founded_list([],_).
well_founded_list([X|Rest],L):-
  well_founded_0(X,L),
  well_founded_list(Rest,L).

%% supporters_list(+F,-ListofSupporters) is det.
%
% where ListOfSupports is a list of the
% supports for one justification for fact F -- i.e. a list of facts which,
% together allow one to deduce F.  One of the facts will typically be a rule.
% The supports for a user-defined fact are: [ax].
%
supporters_list(F,ListO):- no_repeats_cmp(same_sets,ListO,supporters_list_each(F,ListO)).

same_sets(X,Y):-
  flatten([X],FX),sort(FX,XS),
  flatten([Y],FY),sort(FY,YS),!,
  YS=@=XS.

supporters_list_each(F,ListO):-   
   supporters_list0(F,ListM),
   expand_supporters_list(ListM,ListM,ListO).

expand_supporters_list(_, [],[]):-!.
expand_supporters_list(Orig,[F|ListM],[F|NewListOO]):-
   supporters_list0(F,FList),
   list_difference_variant(FList,Orig,NewList),
   % NewList\==[],
   append(Orig,NewList,NewOrig),
   append(ListM,NewList,NewListM),!,
   expand_supporters_list(NewOrig,NewListM,ListO),
   append(ListO,NewList,NewListO),
   list_to_set_variant(NewListO,NewListOO).
expand_supporters_list(Orig,[F|ListM],[F|NewListO]):-
  expand_supporters_list(Orig,ListM,NewListO).


list_to_set_variant(List, Unique) :-
    list_unique_1(List, [], Unique),!.

list_unique_1([], _, []).
list_unique_1([X|Xs], So_far, Us) :-
    memberchk_variant(X, So_far),!,
    list_unique_1(Xs, So_far, Us).
list_unique_1([X|Xs], So_far, [X|Us]) :-
    list_unique_1(Xs, [X|So_far], Us).

% dif_variant(X,Y):- freeze(X,freeze(Y, X \=@= Y )).



%%	list_difference_variant(+List, -Subtract, -Rest)
%
%	Delete all elements of Subtract from List and unify the result
%	with Rest.  Element comparision is done using =@=/2.

list_difference_variant([],_,[]).
list_difference_variant([X|Xs],Ys,L) :-
	(   memberchk_variant(X,Ys)
	->  list_difference_variant(Xs,Ys,L)
	;   L = [X|T],
	    list_difference_variant(Xs,Ys,T)
	).


%%	memberchk_variant(+Val, +List)
%
%	Deterministic check of membership using =@= rather than
%	unification.

memberchk_variant(X, [Y|Ys]) :-
   (   X =@= Y
   ->  true
   ;   memberchk_variant(X, Ys)
   ).

:- module_transparent(supporters_list0/2).
supporters_list0(Var,[is_ftVar(Var)]):-is_ftVar(Var),!.
supporters_list0(F,OUT):-  
 pfcWith_quiet_vars_lock(supporters_list00(F,OUT)).

:- module_transparent(supporters_list00/2).
supporters_list00(F,OUT):- supporters_list1a(F,OUT) *-> true; supporters_list1b(F,OUT).

:- module_transparent(supporters_list1a/2).

supporters_list1a(F,[Fact|MoreFacts]):-
  pfc_get_support_why(F,(Fact,Trigger)),
  triggerSupports(Fact,Trigger,MoreFacts).
   

:- module_transparent(supporters_list1b/2).
supporters_list1b(Var,[is_ftVar(Var)]):- is_ftVar(Var),!.
supporters_list1b(U,[]):- axiomatic_supporter(U),!.
supporters_list1b((H:-B),[MFL]):- !, clause_match(H,B,Ref),find_hb_mfl(H,B,Ref,MFL).
supporters_list1b(\+ P, HOW):- !, supporters_list00(~ P,HOW),!.
supporters_list1b((H),[((H:-B))]):- may_cheat, clause_match(H,B,_Ref).

may_cheat:- fail.

uses_call_only(H):- predicate_property(H,foreign),!.
uses_call_only(H):- predicate_property(H,_), \+ predicate_property(H,interpreted),!.

clause_match(H,_B,uses_call_only(H)):- uses_call_only(H),!.
clause_match(H,B,Ref):- clause_asserted(H,B,Ref),!.
clause_match(H,B,Ref):- ((copy_term(H,HH),clause_u(H,B,Ref),H=@=HH)*->true;clause_u(H,B,Ref)), \+ reserved_body_helper(B).

find_mfl(C,MFL):- lookup_spft_match(C,MFL,ax).
find_mfl(C,MFL):- unwrap_litr0(C,UC) -> C\==UC -> find_mfl(UC,MFL).
find_mfl(C,MFL):- expand_to_hb(C,H,B),
   find_hb_mfl(H,B,_Ref,MFL)->true; (clause_match(H,B,Ref),find_hb_mfl(H,B,Ref,MFL)).

find_hb_mfl(_H,_B,Ref,mfl4(_VarNameZ,M,F,L)):- atomic(Ref),clause_property(Ref,line_count(L)),
 clause_property(Ref,file(F)),clause_property(Ref,module(M)). 
find_hb_mfl(H,B,_,mfl4(VarNameZ,M,F,L)):- lookup_spft_match_first( (H:-B),mfl4(VarNameZ,M,F,L),_),!.
find_hb_mfl(H,B,_Ref,mfl4(VarNameZ,M,F,L)):- lookup_spft_match_first(H,mfl4(VarNameZ,M,F,L),_),ground(B).
find_hb_mfl(H,_B,uses_call_only(H),MFL):- !,call_only_based_mfl(H,MFL).

/*


clause_match(H,_B,uses_call_only(H)):- uses_call_only(H),!.
clause_match(H,B,Ref):- clause_asserted(H,B,Ref),!.

clause_match(H,B,Ref):- no_repeats(Ref,((((copy_term(H,HH),clause_u(H,B,Ref),H=@=HH)*->true;clause_u(H,B,Ref)), \+ reserved_body_helper(B)))).

clause_match0(H,B,Ref):- no_repeats(Ref,clause_match1(H,B,Ref)).

clause_match1(H,B,Ref):- clause(H,B,Ref).
clause_match1(M:H,B,Ref):- !, (M:clause(H,B,Ref) ; clause_match2(H,B,Ref)).
clause_match1(H,B,Ref):- clause_match2(H,B,Ref).

clause_match2(H,B,Ref):- current_module(M),clause(M:H,B,Ref),(clause_property(Ref, module(MM))->MM==M;true).

find_mfl(C,MFL):-find_mfl0(C,MFL),compound(MFL),MFL=mfl4(VarNameZ,_,F,_),nonvar(F).
find_mfl0(C,MFL):- lookup_spft_match(C,MFL,ax).
% find_mfl0(mfl4(VarNameZ,M,F,L),mfl4(VarNameZ,M,F,L)):-!.
find_mfl0(C,MFL):-expand_to_hb(C,H,B),
   find_hb_mfl(H,B,_Ref,MFL)->true; (clause_match(H,B,Ref),find_hb_mfl(H,B,Ref,MFL)).
find_mfl0(C,MFL):-expand_to_hb(C,H,B),
   find_hb_mfl(H,B,_Ref,MFL)->true; (clause_match0(H,B,Ref),find_hb_mfl(H,B,Ref,MFL)).

*/
call_only_based_mfl(H,mfl4(_VarNameZ,M,F,L)):- 
  ignore(predicate_property(H,imported_from(M));predicate_property(H,module(M))),
  ignore(predicate_property(H,line_count(L))),
  ignore(source_file(M:H,F);predicate_property(H,file(F));(predicate_property(H,foreign),F=foreign)).

axiomatic_supporter(Var):-is_ftVar(Var),!,fail.
axiomatic_supporter(is_ftVar(_)).
axiomatic_supporter(clause_u(_)).
axiomatic_supporter(U):- is_file_ref(U),!.
axiomatic_supporter(ax):-!.

is_file_ref(A):-compound(A),A=mfl4(_VarNameZ,_,_,_).

triggerSupports(_,Var,[is_ftVar(Var)]):-is_ftVar(Var),!.
triggerSupports(_,U,[]):- axiomatic_supporter(U),!.
triggerSupports(FactIn,Trigger,OUT):-
  pfc_get_support(Trigger,(Fact,AnotherTrigger))*->
  (triggerSupports(Fact,AnotherTrigger,MoreFacts),OUT=[Fact|MoreFacts]);
  triggerSupports1(FactIn,Trigger,OUT).

triggerSupports1(_,X,[X]):- may_cheat.
/*
triggerSupports1(_,X,_):- pfc_db_type(X,trigger(_)),!,fail.
triggerSupports1(_,uWas(_),[]):-!.
triggerSupports1(_,U,[(U)]):- is_file_ref(U),!.
triggerSupports1(_,U,[uWas(U)]):- get_source_uu((U1,U2))->member(U12,[U1,U2]),U12=@=U.
triggerSupports1(_,X,[X]):- \+ pfc_db_type(X,trigger(_)).
*/


/*
:-module_transparent(pfc_ain/1).
:-module_transparent(pfc_aina/1).
:-module_transparent(pfc_ainz/1).
*/

% :- '$current_source_module'(M),forall(pfc_database_term(F,A,_),(abolish(pfc_lib:F/A),abolish(user:F/A),abolish(M:F/A))).
% :- initialization(ensure_abox(baseKB)).


% % :- set_prolog_flag(pfc_mpred_file,true).
% local_testing

:- fixup_exports.

:- set_prolog_flag(expect_mpred_file,unknown).

% =======================================================
/* 
%
%= predicates to examine the state of pfc 
% interactively exploring Pfc justifications.
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
% =======================================================
% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/mpred/pfc_list_triggers.pl
:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
pfc_listing_module:- nop( module(pfc_listing,
          [ draw_line/0,
            loop_check_just/1,
            pinfo/1,
            pp_items/2,
            pp_item/2,
            pp_filtered/1,
            pp_facts/2,
            pp_facts/1,
            pp_facts/0,
            pfc_list_triggers_types/1,
            pfc_list_triggers_nlc/1,
            pfc_list_triggers_1/1,
            pfc_list_triggers_0/1,
            pfc_list_triggers/1,
            pfc_contains_term/2,
            pfc_classify_facts/4,
            lqu/0,
            get_clause_vars_for_print/2,
            %pfcWhyBrouse/2,
            %pfcWhy1/1,
            %pfcWhy/1,
            %pfcWhy/0,
            pp_rules/0,
            pp_supports/0,
            pp_triggers/0,            
            print_db_items/1,
            print_db_items/2,
            print_db_items/3,
            print_db_items/4,
            print_db_items_and_neg/3,
            show_pred_info/1,
            show_pred_info_0/1,
            pfc_listing_file/0
          ])).

:- include('pfc_header.pi').

:- endif.

% :- use_module(logicmoo(util/logicmoo_util_preddefs)).



:- multifile((
              user:portray/1,
  	user:prolog_list_goal/1,
  	user:prolog_predicate_name/2,
  	user:prolog_clause_name/2)).

:- dynamic
  	user:portray/1.

% :- dynamic(whybuffer/2).



%= 	 	 

%% lqu is semidet.
%
% Lqu.
%
lqu :- listing(que/2).


 

%= 	 	 

%% pp_facts is semidet.
%
% Pretty Print Facts.
%
pp_facts :- pp_facts(_,true).


%= 	 	 

%% pp_facts( ?Pattern) is semidet.
%
% Pretty Print Facts.
%
pp_facts(Pattern) :- pp_facts(Pattern,true).


%= 	 	 

%% pp_facts( ?P, ?C) is semidet.
%
% Pretty Print Facts.
%
pp_facts(P,C) :-
  mpred_facts(P,C,L),
  pfc_classify_facts(L,User,Pfc,_Rule),
  draw_line,
  fmt("User added facts:",[]),
  pp_items(user,User),
  draw_line,
  draw_line,
  fmt("Pfc added facts:",[]),
  pp_items(system,Pfc),
  draw_line.



%= 	 	 

%% pp_items( ?Type, :TermH) is semidet.
%
% Pretty Print Items.
%
pp_items(_Type,[]):-!.
pp_items(Type,[H|T]) :-
  ignore(pp_item(Type,H)),!,
  pp_items(Type,T).
pp_items(Type,H) :- ignore(pp_item(Type,H)).

:- thread_local(t_l:print_mode/1).

%= 	 	 

%% pp_item( ?MM, :TermH) is semidet.
%
% Pretty Print Item.
%
pp_item(_M,H):-pp_filtered(H),!.
pp_item(MM,(H:-B)):- B ==true,pp_item(MM,H).
pp_item(MM,H):- flag(show_asserions_offered,X,X+1),find_and_call(get_print_mode(html)), ( \+ \+ if_defined(pp_item_html(MM,H))),!.


pp_item(MM,spft(W0,U,ax)):- W = (_KB:W0),!,pp_item(MM,U:W).
pp_item(MM,spft(W0,F,U)):- W = (_KB:W0),atom(U),!,    fmt('~N%~n',[]),pp_item(MM,U:W), fmt('rule: ~p~n~n', [F]),!.
pp_item(MM,spft(W0,F,U)):- W = (_KB:W0),         !,   fmt('~w~nd:       ~p~nformat:    ~p~n', [MM,W,F]),pp_item(MM,U).
pp_item(MM,nt(Trigger0,Test,Body)) :- Trigger = (_KB:Trigger0), !, fmt('~w n-trigger: ~p~ntest: ~p~nbody: ~p~n', [MM,Trigger,Test,Body]).
pp_item(MM,pt(F0,Body)):- F = (_KB:F0),             !,fmt('~w p-trigger:~n', [MM]), pp_item('',(F:-Body)).
pp_item(MM,bt(F0,Body)):- F = (_KB:F0),             !,fmt('~w b-trigger:~n', [MM]), pp_item('',(F:-Body)).


pp_item(MM,U:W):- !,sformat(S,'~w  ~w:',[MM,U]),!, pp_item(S,W).
pp_item(MM,H):- \+ \+ (( get_clause_vars_for_print(H,HH),fmt("~w ~p~N",[MM,HH]))).


%= 	 	 

%% get_clause_vars_for_print( ?HB, ?HB) is semidet.
%
% Get Clause Variables For Print.
%
get_clause_vars_for_print(HB,HB):- ground(HB),!.
get_clause_vars_for_print(I,I):- is_listing_hidden(skipVarnames),!.
get_clause_vars_for_print(H0,MHB):- get_clause_vars_copy(H0,MHB),!.
get_clause_vars_for_print(HB,HB).

%= 	 	 

%% pfc_classify_facts( :TermH, ?User, :TermPfc, ?H) is semidet.
%
% Managed Predicate Classify Facts.
%
pfc_classify_facts([],[],[],[]).

pfc_classify_facts([H|T],User,Pfc,[H|Rule]) :-
  pfc_db_type(H,rule),
  !,
  pfc_classify_facts(T,User,Pfc,Rule).

pfc_classify_facts([H|T],[H|User],Pfc,Rule) :-
  pfc_get_support(H,(mfl4(_VarNameZ,_,_,_),ax)),
  !,
  pfc_classify_facts(T,User,Pfc,Rule).

pfc_classify_facts([H|T],User,[H|Pfc],Rule) :-
  pfc_classify_facts(T,User,Pfc,Rule).



%= 	 	 

%% print_db_items( ?T, ?I) is semidet.
%
% Print Database Items.
%
print_db_items(T, I):- 
    draw_line, 
    fmt("~N~w ...~n",[T]),
    print_db_items(I),
    draw_line,!.


%= 	 	 

%% print_db_items( ?I) is semidet.
%
% Print Database Items.
%
print_db_items(F/A):-number(A),!,safe_functor(P,F,A),!,print_db_items(P).
print_db_items(H):- bagof(H,clause_u(H,true),R1),pp_items((:),R1),R1\==[],!.
print_db_items(H):- \+ current_predicate(_,H),!. 
print_db_items(H):- catch( ('$find_predicate'(H,_),call_u(listing(H))),_,true),!,nl,nl.


%= 	 	 

%% pp_rules is semidet.
%
% Pretty Print Rules.
%
pp_rules :-
   print_db_items("Forward Rules",(_ ==> _)),
   print_db_items("Bidirectional Rules",(_ <==> _)), 
   print_db_items("Implication Rules",(_ => _)),
   print_db_items("Bi-conditional Rules",(_ <=> _)),
   print_db_items("Backchaining Rules",(_ <- _)),
   print_db_items("Positive Facts",(==>(_))),
   print_db_items("Negative Facts",(~(_))).


%= 	 	 

%% pp_triggers is semidet.
%
% Pretty Print Triggers.
%
pp_triggers :-
     print_db_items("Positive triggers", pt(_,_,_)),
     print_db_items("Negative triggers", nt(_,_,_,_)),
     print_db_items("Goal triggers",bt(_,_,_)).


%= 	 	 

%% pp_supports is semidet.
%
% Pretty Print Supports.
%
pp_supports :-
  % temporary hack.
  draw_line,
  fmt("Supports ...~n",[]), 
  setof((P =< S), (pfc_get_support(P,S), \+ pp_filtered(P)),L),
  pp_items('Support',L),
  draw_line,!.


pp_filtered(P):-var(P),!,fail.
pp_filtered(_:P):- !, pp_filtered(P).
pp_filtered(P):- safe_functor(P,F,A),F\==(/),!,pp_filtered(F/A).
pp_filtered(F/_):-F==pfc_prop.



%% draw_line is semidet.
%
% Draw Line.
%
draw_line:- \+ thread_self_main,!.
draw_line:- (t_l:print_mode(H)->true;H=unknown),fmt("~N%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%~n",[]),H=H.

 :- meta_predicate loop_check_just(0).

%= 	 	 

%% loop_check_just( :GoalG) is semidet.
%
% Loop Check Justification.
%
loop_check_just(G):-loop_check(G,ignore(arg(1,G,[]))).


%= 	 	 

%% show_pred_info( ?F) is semidet.
%
% Show Predicate Info.
%
show_pred_info(PI):-
   ((
       pi_to_head_l(PI,Head),      
       % doall(show_call(why,call_u(isa(Head,_)))),
        safe_functor(Head,F,_),
        doall(show_call(why,call_u(isa(F,_)))),
       ((current_predicate(_,M:Head), (\+ predicate_property(M:Head,imported_from(_))))
          -> show_pred_info_0(M:Head); 
             wdmsg_pretty(cannot_show_pred_info(Head))))),!.


%= 	 	 

%% show_pred_info_0( ?Head) is semidet.
%
% show Predicate info  Primary Helper.
%
show_pred_info_0(Head):- 
        doall(show_call(why,predicate_property(Head,_))),
        (has_cl(Head)->doall((show_call(why,clause(Head,_))));quietly((listing(Head)))),!.


% ===================================================
% Pretty Print Formula
% ===================================================



%= 	 	 

%% print_db_items( ?Title, ?Mask, ?What) is semidet.
%
% Print Database Items.
%
print_db_items(Title,Mask,What):-print_db_items(Title,Mask,Mask,What).

%= 	 	 

%% print_db_items( ?Title, ?Mask, ?SHOW, ?What0) is semidet.
%
% Print Database Items.
%
print_db_items(Title,Mask,SHOW,What0):-
     get_pi(Mask,H),get_pi(What0,What),
     format(atom(Showing),'~p for ~p...',[Title,What]),
     statistics(cputime,Now),Max is Now + 2,!,
       gripe_time(1.0,
         doall((once(statistics(cputime,NewNow)),NewNow<Max,clause_or_call(H,B),
             quietly(pfc_contains_term(What,(H:-B))),
             flag(print_db_items,LI,LI+1),
             ignore(quietly(pp_item(Showing,SHOW)))))),
     ignore(pp_item(Showing,done)),!.


%= 	 	 

%% pfc_contains_term( ?What, ?VALUE2) is semidet.
%
% Managed Predicate Contains Term.
%
pfc_contains_term(What,_):-is_ftVar(What),!.
pfc_contains_term(What,Inside):- compound(What),!,(\+ \+ ((copy_term_nat(Inside,Inside0),snumbervars(Inside0),contains_term(What,Inside0)))),!.
pfc_contains_term(What,Inside):- (\+ \+ once((subst(Inside,What,foundZadooksy,Diff),Diff \=@= Inside ))),!.



%= 	 	 

%% hook_pfc_listing( ?What) is semidet.
%
% Hook To [baseKB:hook_pfc_listing/1] For Module Mpred_listing.
% Hook Managed Predicate Listing.
%
baseKB:hook_pfc_listing(What):- on_x_debug(pfc_list_triggers(What)).

:- thread_local t_l:pfc_list_triggers_disabled.
% listing(L):-locally(t_l:pfc_list_triggers_disabled,listing(L)).


%= 	 	 

%% pfc_list_triggers( ?What) is semidet.
%
% Managed Predicate List Triggers.
%
pfc_list_triggers(_):-t_l:pfc_list_triggers_disabled,!.
pfc_list_triggers(What):-loop_check(pfc_list_triggers_nlc(What)).

:- meta_predicate(pfc_list_triggers_nlc(?)).


%= 	 	 

%% pfc_list_triggers_nlc( ?What) is semidet.
%
% Managed Predicate List Triggers Nlc.
%
pfc_list_triggers_nlc(MM:What):-atom(MM),!,MM:pfc_list_triggers(What).
pfc_list_triggers_nlc(What):-loop_check(pfc_list_triggers_0(What),true).


%= 	 	 

%% pfc_list_triggers_0( ?What) is semidet.
%
% Managed Predicate list triggers  Primary Helper.
%
pfc_list_triggers_0(What):-get_pi(What,PI),PI\=@=What,pfc_list_triggers(PI).
pfc_list_triggers_0(What):-nonvar(What),What= ~(Then),!, \+ \+ pfc_list_triggers_1(Then), \+ \+ pfc_list_triggers_1(What).
pfc_list_triggers_0(What):- \+ \+  pfc_list_triggers_1(~(What)), \+ \+ pfc_list_triggers_1(What).


%= 	 	 

%% pfc_list_triggers_types( ?VALUE1) is semidet.
%
% Managed Predicate list triggers  Types.
%
pfc_list_triggers_types('Triggers').
pfc_list_triggers_types('Instances').
pfc_list_triggers_types('Subclasses').
pfc_list_triggers_types('ArgTypes').
pfc_list_triggers_types('Arity').
pfc_list_triggers_types('Forward').
pfc_list_triggers_types('Bidirectional').
pfc_list_triggers_types('Backchaining').
pfc_list_triggers_types('Negative').
pfc_list_triggers_types('Sources').
pfc_list_triggers_types('Supports').
pfc_list_triggers_types('Edits').

% print_db_items_and_neg(Title,Fact,What):-nonvar(Fact),Fact= ~(_),!,fail.

%= 	 	 

%% print_db_items_and_neg( ?Title, ?Fact, ?What) is semidet.
%
% Print Database Items And Negated.
%
print_db_items_and_neg(Title,Fact,What):-print_db_items(Title,Fact,What).
print_db_items_and_neg(Title,Fact,What):-print_db_items(Title,~(Fact),What).


%= 	 	 

%% pfc_list_triggers_1( ?What) is semidet.
%
% Managed Predicate list triggers  Secondary Helper.
%
pfc_list_triggers_1(~(What)):-var(What),!.
pfc_list_triggers_1(~(_What)):-!.
pfc_list_triggers_1(What):-var(What),!.
pfc_list_triggers_1(What):- 
   print_db_items('Supports User',spft_precanonical(P,mfl4(VarNameZ,_,_,_),ax),spft(P,mfl4(VarNameZ,_,_,_),ax),What),
   print_db_items('Forward Facts',(nesc(F)),F,What),
   print_db_items('Forward Rules',(_==>_),What),
 ignore((What\= ~(_),safe_functor(What,IWhat,_),
   print_db_items_and_neg('Instance Of',isa(IWhat,_),IWhat),
   print_db_items_and_neg('Instances: ',isa(_,IWhat),IWhat),
   print_db_items_and_neg('Subclass Of',genls(IWhat,_),IWhat),
   print_db_items_and_neg('Subclasses: ',genls(_,IWhat),IWhat))),
   forall(suggest_m(M),print_db_items('PFC Watches', pfc_prop(M,_,_,_),What)),
   print_db_items('Triggers Negative', nt(_,_,_,_),What),
   print_db_items('Triggers Goal',bt(_,_,_),What),
   print_db_items('Triggers Positive',pt(_,_,_),What),
   print_db_items('Bidirectional Rules',(_<==>_),What), 
   dif(A,B),print_db_items('Supports Deduced',spft_precanonical(P,A,B),spft(P,A,B),What),
   dif(G,ax),print_db_items('Supports Nonuser',spft_precanonical(P,G,G),spft(P,G,G),What),
   print_db_items('Backchaining Rules',(_<-_),What),
   % print_db_items('Edits',is_disabled_clause(_),What),
   print_db_items('Edits',is_edited_clause(_,_,_),What),
   print_db_items('Instances',isa(_,_),What),
   print_db_items('Subclasses',genls(_,_),What),
   print_db_items('Negative Facts',~(_),What),

   print_db_items('ArgTypes',argGenls(_,_,_),What),
   print_db_items('ArgTypes',argIsa(_,_,_),What),
   print_db_items('ArgTypes',argQuotedIsa(_,_,_),What),
   print_db_items('ArgTypes',meta_argtypes(_),What),
   print_db_items('ArgTypes',predicate_property(G,meta_predicate(G)),What),
   print_db_items('ArgTypes',resultGenls(_,_),What),
   print_db_items('ArgTypes',resultIsa(_,_),What),
   print_db_items('Arity',arity(_,_),What),
   print_db_items('Arity',current_predicate(_),What),
   print_db_items('MetaFacts Predicate',predicate_property(_,_),What),
   print_db_items('Sources',module_property(_,_),What),
   print_db_items('Sources',predicateConventionMt(_,_),What),
   print_db_items('Sources',source_file(_,_),What),
   print_db_items('Sources',_:man_index(_,_,_,_,_),What),
   print_db_items('Sources',_:'$pldoc'(_,_,_,_),What),
   print_db_items('Sources',_:'$pred_option'(_,_,_,_),What),
   print_db_items('Sources',_:'$mode'(_,_),What),
   !.     


pinfo(F/A):- listing(F/A),safe_functor(P,F,A),findall(Prop,predicate_property(P,Prop),List),wdmsg_pretty(pinfo(F/A)==List),!.



%% pp_DB is semidet.
%
% Pretty Print All.
%
%pp_DB:- defaultAssertMt(M),clause_b(mtHybrid(M)),!,pp_DB(M).
%pp_DB:- forall(clause_b(mtHybrid(M)),pp_DB(M)).

pp_DB:- defaultAssertMt(M),pp_DB(M).
 

pp_DB(M):-
 with_exact_kb(M,
 M:must_det_l((
  pp_db_facts,
  pp_db_rules,
  pp_db_triggers,
  pp_db_supports))).

pp_db_facts:- context_module(M), pp_db_facts(M).
pp_db_rules:- context_module(M), pp_db_rules(M).
pp_db_triggers:- context_module(M), pp_db_triggers(M).
pp_db_supports:- context_module(M), pp_db_supports(M).


:- system:import(pp_DB/0).
:- system:export(pp_DB/0).

%  pp_db_facts ...

pp_db_facts(MM):- ignore(pp_db_facts(MM,_,true)).

pp_db_facts(MM,Pattern):- pp_db_facts(MM,Pattern,true).

pp_db_facts(MM,P,C):-
  mpred_facts_in_kb(MM,P,C,L),
  pfc_classifyFacts(L,User,Pfc,_ZRule),
  length(User,UserSize),length(Pfc,PfcSize),
  format("~N~nUser added facts in [~w]: ~w",[MM,UserSize]),
  pp_db_items(User),
  format("~N~nSystem added facts in [~w]: ~w",[MM,PfcSize]),
  pp_db_items(Pfc).

%  printitems clobbers it''s arguments - beware!


pp_db_items(Var):-var(Var),!,format("~N  ~p",[Var]).
pp_db_items([]):-!.
pp_db_items([H|T]):- !,
  % numbervars(H,0,_),
  format("~N  ~p",[H]),
  nonvar(T),pp_db_items(T).

pp_db_items((P >= FT)):- is_hidden_pft(P,FT),!.
  
pp_db_items(Var):-
  format("~N  ~p",[Var]).


is_hidden_pft(_,(mfl4(_VarNameZ,baseKB,_,_),ax)).
is_hidden_pft(_,(why_marked(_),ax)).


pp_mask(Type,MM,Mask):-   
  bagof_or_nil(Mask,lookup_kb(MM,Mask),Nts),
  list_to_set_variant(Nts,NtsSet),!,
  pp_mask_list(Type,MM,NtsSet).

pp_mask_list(Type,MM,[]):- !,
  format("~N~nNo ~ws in [~w]...~n",[Type,MM]).
pp_mask_list(Type,MM,NtsSet):- length(NtsSet,Size), !,
  format("~N~n~ws (~w) in [~w]...~n",[Type,Size,MM]),
  pp_db_items(NtsSet).

pfc_classifyFacts([],[],[],[]).

pfc_classifyFacts([H|T],User,Pfc,[H|Rule]):-
  pfc_db_type(H,rule(_)),
  !,
  pfc_classifyFacts(T,User,Pfc,Rule).

pfc_classifyFacts([H|T],[H|User],Pfc,Rule):-
  % get_source_uu(UU),
  get_first_user_reason(H,_UU),
  !,
  pfc_classifyFacts(T,User,Pfc,Rule).

pfc_classifyFacts([H|T],User,[H|Pfc],Rule):-
  pfc_classifyFacts(T,User,Pfc,Rule).


pp_db_rules(MM):- 
 pp_mask("Forward Rule",MM,==>(_,_)),
 pp_mask("Bi-conditional Rule",MM,<==>(_,_)),
 pp_mask("Backward Rule",MM,<-(_,_)),
 % pp_mask("Prolog Rule",MM,:-(_,_)),
 !.


pp_db_triggers(MM):- 
 pp_mask("Positive trigger",MM,pt(_,_)),
 pp_mask("Negative trigger",MM,nt(_,_,_)),
 pp_mask("Goal trigger",MM,bt(_,_)),!.

pp_db_supports(MM):-
  % temporary hack.
  format("~N~nSupports in [~w]...~n",[MM]),
  with_exact_kb(MM, bagof_or_nil((P >= S), pfc_get_support(P,S),L)),
  list_to_set_variant(L,LS),
  pp_db_items(LS),!.



:- fixup_exports.

pfc_listing_file.

/* 
% Game loading Utils
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/

% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/mpred/pfc_loader.pl
:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
pfc_loader_module:- fail, nop(module(pfc_loader,
          [ add_from_file/1,
          % unused_assertion/1,
          pfc_ops/0,
          set_file_lang/1,
          pfc_te/6,
          pfc_dcg/0,
          get_original_term_src/1,

          set_lang/1,
           simplify_language_name/2,
           %is_undefaulted/1,
          current_op_alias/2,
            show_load_call/1,
            add_term/2,
            
            % system:import_module_to_user/1,
            
            
            make_file_command/3,
            % import_shared_pred/3,
            % import_to_user0/3,
            % import_to_user_mfa0/4,

            %predicate_is_undefined_fa/2,
            
            same_language/2,
            call_file_command0/4,
            is_compiling_clause/0,
            to_prolog_xform/2,
            pfc_ain_loaded/0,


            begin_pfc/0,
            call_file_command/4,
            can_be_dynamic/1,
            cl_assert/2,
            clear_predicates/1,
            collect_expansions/3,
            compile_clause/1,
            pfc_term_expansion_by_storage_type/3,
            convert_side_effect/2,
            convert_side_effect/3,
            convert_side_effect_buggy/2,
            current_context_module/1,
            % cwc/0,
            decache_file_type/1,
            pfc_ops/0,
            %setup_module_ops/1,
            %pfc_op_each/1,
            %pfc_op_unless/4,
            declare_load_dbase/1,
            disable_pfc_expansion/0,
            disable_mpreds_in_current_file/0,
            
            dyn_begin/0,
            dyn_end/0,
            enable_pfc_expansion/0,
            end_module_type/1,
            end_module_type/2,
            ensure_loaded_no_mpreds/1,

            % ensure_prolog_file_consulted/2, ensure_mpred_file_consulted/2,
            ensure_mpred_file_loaded/1,
            ensure_mpred_file_loaded/2,
            
            etrace/0,
            expand_in_pfc_kb_module/2,
            expanded_already_functor/1,
            file_begin/1,
            file_end/1,
            finish_processing_world/0,
            force_reload_mpred_file/1,
            force_reload_mpred_file/2,
            force_reload_mpred_file2/2,
            get_file_type/2,
            get_lang/1,
            get_lang0/1,
            get_last_time_file/3,
            get_op_alias/2,
            gload/0,
            hdr_debug/2,
            include_mpred_files/1,
            include_prolog_files/1,
            get_lang0/1,
            is_code_body/1,
            is_compiling/0,
            is_compiling_sourcecode/0,
            is_directive_form/1,
            is_mpred_file/1,
            lang_op_alias/3,
            expand_term_to_load_calls/2,
            pfc_expander_now_physically/3,
            load_init_world/2,
            load_language_file/1,
            load_mpred_files/0,
            load_pfc_on_file_end/2,
            loader_side_effect_capture_only/2,
            loader_side_effect_verify_only/2,
            must_expand_term_to_command/2,
            
            make_db_listing/0,
            make_dynamic/1,
           (make_dynamic_ilc)/1,
            module_typed_term_expand/2,
            module_typed_term_expand/5,
            pfc_begin/0,
            pfc_expand_inside_file_anyways/0,
            pfc_expand_inside_file_anyways/1,
            pfc_te/6,
            mpred_file_term_expansion/4,
            dont_term_expansion/2,
            mpred_file_term_expansion/4,
            
            pfc_expand_file_module_clause/4,
            pfc_expand_file_module_clause/4,
            pfc_implode_varnames/1,
            
            pfc_prolog_only_file/1,
            pfc_may_expand/0,
            pfc_may_expand_module/1,
            pfc_maybe_skip/1,
            
            baseKB:pfc_skipped_module/1,
            pfc_term_expansion/2,
            pfc_use_module/1,
            must_compile_special_clause/1,
            expand_term_to_load_calls/2,
            must_locate_file/2,
            maybe_locate_file/2,
            myDebugOnError/1,
            
            op_alias/2,
            op_lang/1,
            pl_to_pfc_syntax/2,
            pl_to_pfc_syntax_h/2,
            pop_predicates/2,
            push_predicates/2,
            read_one_term/2,
            read_one_term/3,
            register_module_type/1,
            register_module_type/2,
            rsavedb/0,
            savedb/0,
            scan_updates/0,
            show_bool/1,
            show_interesting_cl/2,
            show_load_context/0,
            simplify_why/2,
            simplify_why_r/4,
            stream_pos/1,
            term_expand_local_each/5,
            
            transform_opers/3,
            
            use_was_isa/3,
            was_exported_content/3,
            with_pfc_expansions/1,
            % with_delayed_chaining/1,
            lmcache:pfc_directive_value/3,

            baseKB:loaded_file_world_time/3,
            baseKB:pfc_provide_clauses/3,
            baseKB:never_reload_file/1,
            always_expand_on_thread/1,
            t_l:current_lang/1,

            baseKB:pfc_skipped_module/1,
            %prolog_load_file_loop_checked/2,
%            registered_module_type/2,
            %t_l:into_form_code/0,
            %t_l:pfc_module_expansion/1,
            
            user:term_expansion/2,
            pfc_loader_module_transparent/1,
            convert_side_effect_0a/2, convert_side_effect_0b/2, 
            convert_side_effect_0c/2, guess_if_mpred_file0/1, expand_term_to_load_calls/2, load_file_term_to_command_1/3, 
            load_file_term_to_command_1b/3, pfc_term_expansion_by_pred_class/3, 
            must_expand_term_to_command/2, pl_to_pfc_syntax0/2, 
            
            transform_opers_0/2, transform_opers_1/2,
            pfc_loader_file/0,
            pfc_unload_file/0,
            pfc_unload_file/1
          ])).

:- include('pfc_header.pi').
:- use_module(library(dictoo_lib)).

:- endif.

%:- user:use_module(library('file_scope')).

:- thread_local(t_l:into_form_code/0).

:- thread_local(t_l:disable_px/0).
:- multifile(prolog:make_hook/2).
:- dynamic(prolog:make_hook/2).

% :- asserta_if_new((prolog:make_hook(BA, C):- dmsg_pretty(prolog:make_hook(BA, C)),fail)).
% prolog:make_hook(before, FileS):- maplist(pfc_loader:pfc_unload_file,FileS).

% Avoid Warning: pfc_loader:prolog_load_context(reload,true), which is called from
pfc_unload_file:- prolog_load_context(reload,true),!.
pfc_unload_file:- source_location(File,_),pfc_unload_file(File).
pfc_unload_file(File):- dmsg(nop(pfc_unload_file(File))),!.
pfc_unload_file(File):-
  findall(
    pfcWithdraw(Data,(mfl4(VarNameZ,Module, File, LineNum),AX)),
    % clause_u
    call_u(spft(Data, mfl4(VarNameZ,Module, File, LineNum),AX)),
                    ToDo),
     length(ToDo,Len),
     dmsg_pretty(pfc_unload_file(File,Len)),
     maplist(call,ToDo),!.


 :- module_transparent((load_file_term_to_command_1b/3,pfc_dcg/0, pfc_term_expansion_by_pred_class/3,
   must_expand_term_to_command/2, pl_to_pfc_syntax0/2, 
    
    transform_opers_0/2, transform_opers_1/2)).

 :- meta_predicate
        % make_reachable(?,?),
        call_file_command(?, ?, ?, ?),
        cl_assert(?, ?),
        show_bool(0),
        convert_side_effect(?, +, -),
        
        ensure_loaded_no_mpreds(:),
        ensure_mpred_file_loaded(:),
        ensure_mpred_file_loaded(+, :),
        force_reload_mpred_file(?),
        force_reload_mpred_file2(+,+),
        get_last_time_file(+, +, -),
        expand_term_to_load_calls(?, ?),
        pfc_expander_now_physically(?, ?, ?),
        load_init_world(+, :),
        module_typed_term_expand(?, ?),
        pfc_te(+, +, +,+, -,-),
        
        pfc_term_expansion(?, ?),
        myDebugOnError(0),        
        with_pfc_expansions(0),
        %with_delayed_chaining(0),
        pfc_loader_module_transparent(?),       
        baseKB:loaded_file_world_time(+, +, +).
:- multifile(( user:term_expansion/2)).
:- (dynamic   user:term_expansion/2).
% :- (module_transparent add_from_file/1, add_term/2
%  begin_pfc/0, call_file_command/4, 
% call_from_module/2, with_source_module/2, can_be_dynamic/1, cl_assert/2, clear_predicates/1, collect_expansions/3, compile_clause/1,
%  pfc_term_expansion_by_storage_type/3, convert_side_effect/2, convert_side_effect/3, convert_side_effect_0a/2, convert_side_effect_0b/2, convert_side_effect_0c/2, 
% convert_side_effect_buggy/2, current_context_module/1, current_op_alias/2, cwc/0, decache_file_type/1, ensure_abox/1, declare_load_dbase/1, 
% disable_pfc_expansion/0, disable_mpreds_in_current_file/0, dyn_begin/0, dyn_end/0, enable_pfc_expansion/0, end_module_type/1, end_module_type/2, ensure_loaded_no_mpreds/1, ensure_mpred_file_consulted/2, ensure_mpred_file_loaded/1, ensure_mpred_file_loaded/2, ensure_prolog_file_consulted/2, etrace/0, expand_in_pfc_kb_module/2, expanded_already_functor/1, file_begin/1, file_end/1, finish_processing_world/0, force_reload_mpred_file/1, 
%  force_reload_mpred_file2/2, force_reload_mpred_file/2, from_kif_string/2, get_file_type/2, get_lang/1, get_last_time_file/3, get_op_alias/2, gload/0, guess_file_type_loader/2, hdr_debug/2, in_include_file/0, in_pfc_kb_module/0, include_mpred_files/1, get_lang/1, is_code_body/1, is_compiling/0, is_compiling_sourcecode/0, is_kif_string/1, is_mpred_file/1, guess_if_mpred_file0/1, lang_op_alias/3, load_file_dir/2, load_file_some_type/2, expand_term_to_load_calls/2, load_file_term_to_command_1/3, load_file_term_to_command_1b/3, pfc_term_expansion_by_pred_class/3, expand_term_to_load_calls/2, expand_term_to_load_calls/4, load_init_world/2, load_language_file/1, load_mpred_files/0, load_pfc_on_file_end/2, loader_side_effect_capture_only/2, loader_side_effect_verify_only/2, expand_term_to_command/2, loading_source_file/1, make_db_listing/0, make_dynamic/1, module_typed_term_expand/2, module_typed_term_expand/5, pfc_begin/0,  pfc_expand_inside_file_anyways/0, pfc_expand_inside_file_anyways/1, pfc_te/4, pfc_expander_now/2, pfc_expand_file_module_clause/4, pfc_implode_varnames/1, pfc_loader_file/0, pfc_may_expand/0, pfc_may_expand_module/1, pfc_maybe_skip/1, pfc_process_input/2, pfc_process_input_1/1, baseKB:pfc_skipped_module/1, pfc_term_expansion/2, pfc_use_module/1, must_compile_special_clause/1, expand_term_to_load_calls/2, must_locate_file/2, must_expand_term_to_command/2, myDebugOnError/1, op_alias/2, op_lang/1, pl_to_pfc_syntax/2, pl_to_pfc_syntax0/2, pl_to_pfc_syntax_h/2, pop_predicates/2, process_this_script/0, process_this_script/1, process_this_script0/1, prolog_load_file_loop_checked/2, prolog_load_file_loop_checked_0/2, prolog_load_file_nlc/2, prolog_load_file_nlc_0/2, push_predicates/2, read_one_term/2, read_one_term/3, register_module_type/1, register_module_type/2, rsavedb/0, savedb/0, scan_updates/0, show_bool/1, show_interesting_cl/2, show_load_context/0, simplify_why/2, simplify_why_r/4, stream_pos/1, term_expand_local_each/5, transform_opers/3, transform_opers_0/2, transform_opers_1/2, use_file_type_loader/2, use_was_isa/3, was_exported_content/3, with_pfc_expansions/1, with_delayed_chaining/1, with_source_module/2, xfile_module_term_expansion_pass_3/7,  
% (~)/1, baseKB:cl_assert/2, baseKB:cwc/0, baseKB:pfc_provide_clauses/3, always_expand_on_thread/1, t_l:current_lang/1, current_op_alias/2, defaultAssertMt/1,  baseKB:loaded_file_world_time/3, pfc_directive_value/3, baseKB:pfc_skipped_module/1, 
%   never_reload_file/1, prolog_load_file_loop_checked/2, registered_module_type/2).
:- module_transparent 
            pfc_ops/0.
            %setup_module_ops/1.

:- thread_local(t_l:into_form_code/0).
:- thread_local(t_l:pfc_module_expansion/1).

%:- (volatile t_l:into_form_code/0, t_l:pfc_module_expansion/1).
%:-  /**/ export((convert_side_effect_0a/2, convert_side_effect_0b/2, convert_side_effect_0c/2, guess_if_mpred_file0/1, expand_term_to_load_calls/2, load_file_term_to_command_1/3, load_file_term_to_command_1b/3, pfc_term_expansion_by_pred_class/3, pfc_process_input_1/1, must_expand_term_to_command/2, pl_to_pfc_syntax0/2, process_this_script0/1, prolog_load_file_loop_checked_0/2, prolog_load_file_nlc_0/2, transform_opers_0/2, transform_opers_1/2, xfile_module_term_expansion_pass_3/7)).
%:- dynamic((registered_module_type/2, current_op_alias/2, baseKB:pfc_skipped_module/1, prolog_load_file_loop_checked/2, lmcache:pfc_directive_value/3, defaultAssertMt/1, baseKB:loaded_file_world_time/3, baseKB:never_reload_file/1, always_expand_on_thread/1, t_l:current_lang/1, current_op_alias/2, defaultAssertMt/1, baseKB:loaded_file_world_time/3, pfc_directive_value/3, baseKB:pfc_skipped_module/1, never_reload_file/1, prolog_load_file_loop_checked/2, registered_module_type/2,  user:prolog_load_file/2, user:term_expansion/2)).
%:- dynamic(registered_module_type/2).        


:- multifile((baseKB:registered_module_type/2)).
:-   dynamic((baseKB:registered_module_type/2)).



pfc_load(In):- is_stream(In),!,
   repeat,
   line_count(In,_Lineno),
   % double_quotes(_DQBool)
   Options = [variables(_Vars),variable_names(VarNames),singletons(_Singletons),comment(_Comment)],
   catchv((read_term(In,Term,[syntax_errors(error)|Options])),E,(dmsg_pretty(E),fail)),
   set_varname_list(VarNames),expand_term(Term,TermO),pfc_load_term(TermO),
   Term==end_of_file,
   close(In).

pfc_load(PLNAME):- % unload_file(PLNAME),
   open(PLNAME, read, In, []),
   absolute_file_name(PLNAME,Disk),
   set_how_virtualize_file(heads,Disk),
   pfc_load(In).

pfc_reload(PLNAME):- pfc_unload_file(PLNAME),pfc_load(PLNAME).



% TODO uncomment the next line without breaking it all!
% baseKB:use_cyc_database.




%% pfc_loader_module_transparent( ?F) is det.
%
% Managed Predicate Loader Module Transparent.
%
pfc_loader_module_transparent(F/A):-!,pfc_loader_module_transparent(F/A).
pfc_loader_module_transparent(M:F/A):-!, M:module_transparent(M:F/A),dtrace, system:import(M:F/A).
pfc_loader_module_transparent(F/A):-!, module_transparent(F/A).

% :- module_property(pfc_loader, exports(List)),maplist(pfc_loader_module_transparent,List).

:- thread_local(t_l:pfc_already_in_file_expansion/1).




%% pfc_prolog_only_file( ?File) is det.
%
% Managed Predicate Prolog Only File.
%
pfc_prolog_only_file(File):- var(File),!,fail.
pfc_prolog_only_file(File):- get_how_virtualize_file(false,File),!.
pfc_prolog_only_file(File):- lmcache:pfc_directive_value(File,language,pl),!.
pfc_prolog_only_file(File):- file_name_extension(File,_,pfc),!,fail.
pfc_prolog_only_file(File):- lmcache:pfc_directive_value(File,language,pfc),!,fail.
pfc_prolog_only_file(_).


% pfc_te(_,_,I,OO):-thread_self(X),X\==main,!,I=OO.
% not actual function



%% pfc_te( +OUT1, +OUT2, +I, +Pos, -IN4, -POS4) is det.
%
% Managed Predicate Expander.
%

:- prolog_load_context(directory,Dir),asserta(baseKB:pfc_loader_dir(Dir)).

pfc_te(Type,_,I,_,_,_):- !,fail,quietly(dont_term_expansion(Type,I)),!,fail.
pfc_te(Type,Module,I,PosI,O,PosO):- 
  \+ current_prolog_flag(pfc_te,false),
   % prolog_load_context(file,S),prolog_load_context(source,S),   
   mpred_file_term_expansion(Type,Module,I,O)->PosO=PosI.

dont_term_expansion(Type,I):- 
   current_prolog_flag(subclause_expansion,false);
   var(I);
   I=(_ --> _) ;    
   current_prolog_flag(xref,true);
   (prolog_load_context(directory,Dir), baseKB:pfc_loader_dir(Dir));
   I= '$si$':'$was_imported_kb_content$'(_,_); 
   (Type \== term , Type \= _:term ) ; 
   (t_l:disable_px, false ).




%% mpred_file_term_expansion( ?Type, ?LoaderMod, ?I, ?OO) is det.
%
% Managed Predicate Expander Primary Helper.
%
:- meta_predicate mpred_file_term_expansion(+,+,+,-).
% mpred_file_term_expansion(_,_,_,_):- \+ current_predicate(_,_:pfc_loader_file),!,fail.
mpred_file_term_expansion(_,_,I,_):- is_directive_form(I),!,fail.
mpred_file_term_expansion(_,_,I,_):- is_ftVar(I),!,fail.
% mpred_file_term_expansion(_,_,_,_):- get_lang(pl),!,fail.
% mpred_file_term_expansion(Type,LoaderMod,(I:-B),OO):-B==true,!,mpred_file_term_expansion(Type,LoaderMod,I,OO).
% mpred_file_term_expansion(_Type,_LoaderMod,I,( :- must(ain(I)))):-!.

mpred_file_term_expansion(Type,LoaderMod,I,OO):- !,fail,
   no_loop_check(mpred_file_term_expansion0(Type,LoaderMod,I,OO)).

% Ensure rule macro predicates are being used checked just before assert/query time
mpred_file_term_expansion0(Type,LoaderMod,I,O):- 
  sanity((ground(Type:LoaderMod),nonvar(I),var(O))),
  quietly_must(get_source_mfl(mfl4(VarNameZ,MF,F,L))),!,
  % \+ pfc_prolog_only_file(F),
  call_u(baseKB:mtHybrid(MT1)),
  must((proper_source_mod([LoaderMod,MF,MT1],AM))),
  (((nb_current('$source_term',TermWas), TermWas == I);
    (b_getval('$term',TermWas), TermWas == I))),  
  call_cleanup(
        locally(t_l:current_why_source(mfl4(VarNameZ,AM,F,L)),
        (( get_original_term_src(Orig), 
           b_setval('$orig_term',Orig),
           b_setval('$term',[]),
           (O= (:- must(pfc_ain(I,(mfl4(VarNameZ,AM,F,L),ax)))))))),
    b_setval('$term',TermWas)),!, dmsg_pretty(I-->O).


proper_source_mod(List,AM):- member(AM,List),call_u(mtHybrid(AM)),!.
proper_source_mod(List,AM):- member(AM,List),call_u(mtCanAssert(AM)),!.

%% pfc_expand_file_module_clause( +File, +Module, +:Term, -:Expanded) is det.
%
% Managed Predicate Expander Now One Cc.
%
%pfc_expand_file_module_clause(_,_,I,O):- var(I),!,quietly_must(I=O).

%pfc_expand_file_module_clause(_,_,(?-(G0)),(?-(G1))):-!,quietly_must(fully_expand_goal(change(assert,ain),G0,G1)).
%pfc_expand_file_module_clause(F,M,I,O):- is_directive_form(I),!,quietly_must(fully_expand(change(assert,load(F,M)),I,O)).
%pfc_expand_file_module_clause(F,M,(H:-B),O):- get_lang(pl),!,quietly_must(fully_expand(change(assert,load(F,M)),(H:-B),O)).
%pfc_expand_file_module_clause(_,_,I,O):- t_l:verify_side_effect_buffer,!,loader_side_effect_verify_only(I,O).
%pfc_expand_file_module_clause(_,_,I,O):- t_l:use_side_effect_buffer,!,loader_side_effect_capture_only(I,O).
pfc_expand_file_module_clause(_,M,I,O):- pfc_expander_now_physically(M,I,O).
  


%% pfc_expander_now_physically( ?M, ?I, ?OO) is det.
%
% Managed Predicate Expander Now Physically.
%
pfc_expander_now_physically(M,I,OO):- 
 '$set_source_module'(Old,M),
 call_cleanup(M:((
   quietly_must((source_context_module(CM),CM\==pfc_lib,CM\==pfc_loader)),
   quietly_must(loop_check(expand_term_to_load_calls(I,O),trace_or_throw_ex(in_loop(expand_term_to_load_calls(I,O))))),!,
   quietly_must(I\=@=O),
  (((t_l:pfc_term_expansion_ok;pfc_expand_inside_file_anyways)-> true ; 
    ((show_load_context,dmsg_pretty(warning,wanted_pfc_term_expansion(I,O))),fail)),
   ((O=(:-(CALL))) ->  quietly_must((M:call_file_command(I,CALL,OO,O))); 
        (OO = O))))),'$set_source_module'(Old)).






%% show_bool( :GoalG) is det.
%
% Show Bool.
%
show_bool(G):- must(forall((G*->dmsg_pretty(true=G);dmsg_pretty(false=G)),true)).




%% show_load_context is det.
%
% Show Load Context.
%
show_load_context:- 
  must((
  %listing(baseKB:registered_mpred_file),
  show_bool(pfc_may_expand),
  show_bool(in_pfc_kb_module),
  show_bool(pfc_expand_inside_file_anyways),
  show_bool(t_l:pfc_term_expansion_ok),
  show_bool(loading_source_file(_)),
  show_bool(nb_current('$source_term',_)),
  show_bool(nb_current('$goal_term',_)),
  show_bool(nb_current('$term',_)),
  show_bool(nb_current('$orig_term',_)),
  show_bool(get_lang(_)))).





%% add_term( ?Term, ?Vs) is det.
%
% Add Term.
%
add_term(end_of_file,_):-!.
add_term(Term,Vs):- 
   put_variable_names( Vs),
    add_from_file(Term).





%% add_from_file( ?Term) is det.
%
% Add Converted From File.
%
add_from_file(Term):-  
  locally(t_l:pfc_already_in_file_expansion(Term),quietly_must(ain(Term))).




%% myDebugOnError( :GoalTerm) is det.
%
% My Debug Whenever Error.
%
myDebugOnError(Term):-catch(once(quietly_must((Term))),E,(dmsg_pretty(error(E,start_myDebugOnError(Term))),dumpST,dtrace,rtrace((Term)),dmsginfo(stop_myDebugOnError(E=Term)),dtrace,Term)).
         



%% read_one_term( ?Term, ?Vs) is det.
%
% Read One Term.
%
read_one_term(Term,Vs):- catch(once(( read_term(Term,[double_quotes(string),variable_names(Vs)]))),E,(Term=error(E),dmsg_pretty(error(E,read_one_term(Term))))).



%% read_one_term( ?Stream, ?Term, ?Vs) is det.
%
% Read One Term.
%
read_one_term(Stream,Term,Vs):- catch(once(( read_term(Stream,Term,[double_quotes(string),variable_names(Vs)]))),E,(Term=error(E),dmsg_pretty(error(E,read_one_term(Term))))).

% rescan_pfc_stubs:- doall((pfc_prop(M,F,A,prologHybrid),arity(F,A),A>0,warnOnError(declare_pfc_local_dynamic(moo,F,A)))).



:-  /**/ export(etrace/0).



%% etrace is det.
%
% E Trace.
%
etrace:-leash(+all),leash(+exception),dtrace.


% el(X):- cwc,sanity(nonvar(X)),logicmoo_util_filesystem:filematch(X,Y),sanity(atom(Y)),ensure_loaded(Y),!.


:- style_check(+singleton).
:- style_check(-discontiguous).
% :- style_check(-atom).

% gload:- ensure_mpred_file_loaded(savedb),!.



%% gload is det.
%
% Gload.
%
gload:- baseKB:ensure_mpred_file_loaded(logicmoo('rooms/startrek.all.pfc.pl')).

%:-meta_predicate(savedb/0).



%% savedb is det.
%
% Savedb.
%
savedb:-!.
savedb:- on_x_debug(rsavedb),!.
%:-meta_predicate(rsavedb/0).



%% rsavedb is det.
%
% Rsavedb.
%
rsavedb:-
 nop(on_x_debug(agenda_pfc_repropigate)),
 catch((   
   ignore(catch(make_directory('/tmp/lm/'),_,true)),
   ignore(catch(delete_file('/tmp/lm/savedb'),E,(dmsginfo(E:delete_file('/tmp/lm/savedb'))))),   
   tell('/tmp/lm/savedb'),make_db_listing,told),E,dmsginfo(savedb(E))),!.





%% make_db_listing is det.
%
% Make Database Listing.
%
make_db_listing:-
 % defaultAssertMt(DBM),
%   listing(t),
 %  listing(mpred_f),
     listing(_),
     listing(baseKB:_),  
     listing(dbase:_),
     listing(dyn:_),
     listing(moo_loader:_),
     listing(world :_),
     listing(_),!.







%% hdr_debug( ?F, ?A) is det.
%
% Hdr Debug.
%
hdr_debug(_,_):-!.
hdr_debug(F,A):-'format'(F,A).
:- meta_predicate module_typed_term_expand(?,?).





%% module_typed_term_expand( ?X, ?UPARAM2) is det.
%
% Module Typed Term Expand.
%
module_typed_term_expand(X,_):-not(compound(X)),!,fail.
module_typed_term_expand( ((':-'(_))) , _ ):-!,fail.
module_typed_term_expand(_:B1,B2):-!,module_typed_term_expand(B1,B2),!.
module_typed_term_expand(X,CvtO):- compound(X),loading_module(CM),functor_catch(X,F,A),module_typed_term_expand(CM,X,F,A,CvtO).




%% module_typed_term_expand( ?CM, ?X, ?F, ?A, ?CvtO) is det.
%
% Module Typed Term Expand.
%
module_typed_term_expand(CM,X,F,A,CvtO):-findall(CvtO,term_expand_local_each(CM,X,F,A,CvtO),Ys), Ys == [],!,fail.  




%% term_expand_local_each( ?VALUE1, ?VALUE2, ?F, ?A, ?VALUE5) is det.
%
% Term Expand Local Each.
%
term_expand_local_each(_,_,F,A,_):- member(F / A,[never_expand]),!,fail.
term_expand_local_each(CM,X,F,A,X):-baseKB:registered_module_type(CM,utility),export(F/A).
term_expand_local_each(CM,X,F,A,X):-baseKB:registered_module_type(CM,dynamic),dynamic(F/A).





% ========================================
% include_mpred_file(MASK)
% ========================================




%% include_mpred_files( ?Mask) is det.
%
% Include Managed Predicate Files.
%
include_mpred_files(Mask):- 
     forall(maybe_locate_file(Mask,E),ensure_mpred_file_loaded(E)).

:- module_transparent(include_prolog_files/1).

include_prolog_files(Mask):- 
     forall(maybe_locate_file(Mask,E),ensure_loaded(E)).

/*
module(M,Preds):-
    'format'(user_output /*e*/,'% visting module ~w.~n',[M]),
    forall(member(P,Preds),export(P)).
*/



%% scan_updates is det.
%
% Scan Updates.
%
scan_updates:-thread_property(X,alias(loading_code)),thread_property(X,status(running)),!.
scan_updates:-!.
scan_updates:-ignore(catch(make,_,true)).

/*
do_term_expansions:- source_context_module(CM), (do_term_expansions(CM)).

do_term_expansions(_):- thread_self(ID),baseKB:always_expand_on_thread(ID),!.
%do_term_expansions(_):- always_transform_heads,not(prevent_transform_mpreds),!.
do_term_expansions(_):- is_compiling_clause.
do_term_expansions(CM):- check_how_virtualize_file(heads,CM),!, not(ended_transform_mpreds), not(prevent_transform_mpreds).

check_term_expansions:- not(do_term_expansions).
*/

% :- (do_term_expansions(_)->true;throw(not_term_expansions)).


:- op(1120,fx,export),op(1120,fx,export).

:-  /**/ export(((current_context_module/1,
    module_typed_term_expand/2,
         register_module_type/1,          
         end_module_type/1))).










% :- user:use_module(library(base32)).

% :-autoload.

% https://docs.google.com/document/u/0/export?format=txt&id=1yyGne4g8vXKxNPKIKVLOtt0OxIM2kxyfmvjqR1lgbcY
% http_get
:- asserta_if_new(t_l:infForward).

:- dynamic(baseKB:pfc_skipped_module/1).



%% pfc_skipped_module( ?VALUE1) is det.
%
% Hook To [baseKB:pfc_skipped_module/1] For Module Mpred_loader.
% Managed Predicate Skipped Module.
%
% :-show_call(why,loading_module(X)),retractall(X).

%:-listing(baseKB:pfc_skipped_module/1).


%fwc:-true.
%bwc:-true.

%is_fc_body(P):- quietly(fwc==P ; (compound(P),arg(1,P,E),is_fc_body(E))),!.
%is_bc_body(P):- quietly(bwc==P ; (compound(P),arg(1,P,E),is_bc_body(E))),!.



%% is_code_body( ?P) is det.
%
% If Is A Code Body.
%
is_code_body(P):- quietly(cwc==P ; (compound(P),arg(1,P,E),is_code_body(E))),!.


% :- meta_predicate(with_source_module(:,(*))).



%% get_file_type( ?File, ?Type) is det.
%
% Get File Type.
%
get_file_type(File,Type):-var(File),!,quietly_must(loading_source_file(File)),get_file_type(File,Type).
get_file_type(File,Type):-lmcache:pfc_directive_value(File,language,Type).
get_file_type(File,pfc):-file_name_extension(_,'.pfc.pl',File).
get_file_type(File,Type):-file_name_extension(_,Type,File).




%% is_mpred_file(?F) is det.
%
% If Is A Managed Predicate File.
%
is_mpred_file(F):- var(F),!,quietly_must(loading_source_file(F)),F\==user,!, baseKB:how_virtualize_file(heads,F,0),!.
is_mpred_file(F):- guess_if_mpred_file0(F),!,guess_if_mpred_file0(F),(set_how_virtualize_file(heads,F,0)),!.

%% guess_if_mpred_file0( ?F) is det.
%
% If Is A Managed Predicate File Primary Helper.
%
guess_if_mpred_file0(F):- file_name_extension(_,pfc,F),!.
guess_if_mpred_file0(F):- atom_concat(_,'.pfc.pl',F),!.
guess_if_mpred_file0(F):- file_name_extension(_,plmoo,F),!.
% guess_if_mpred_file0(F):- filematch(prologmud(**/*),F0),F0=F.
guess_if_mpred_file0(F):- loop_check(get_lang(pfc)),!,loop_check(loading_source_file(F0)),F0=F.
guess_if_mpred_file0(F):- atom(F),exists_file(F), file_name_extension(_,WAS,F),WAS\=pl,WAS\= '',WAS\=chr,!.



%% decache_file_type( ?F) is det.
%
% Decache File Type.
%
decache_file_type(F):-
  forall(clause(baseKB:how_virtualize_file(_,F,_),true,Ref),erase(Ref)).



%% must_compile_special_clause( ?CL) is det.
%
% Must Be Successfull Compile Special Clause.
%
must_compile_special_clause(:- (_) ):-!,fail.
%must_compile_special_clause(CL):- sanity(nonvar(CL)),not(t_l:into_form_code),not(t_l:pfc_already_in_file_expansion(CL)),not((get_functor(CL,F),expanded_already_functor(F))).
must_compile_special_clause(CL):- \+ t_l:disable_px, 
   sanity(nonvar(CL)), \+(t_l:into_form_code),
    \+(t_l:pfc_already_in_file_expansion(CL)),
    \+((get_functor(CL,F),expanded_already_functor(F))),
   pfc_db_type(CL,_),!.

:- thread_local(t_l:pfc_module_expansion/1).




%% pfc_use_module( ?M) is det.
%
% Managed Predicate Use Module.
%
pfc_use_module(M):- \+ atom(M),!.
pfc_use_module(M):- atom(M),quietly_must(atom(M)),retractall(baseKB:pfc_skipped_module(M)),show_call(why,asserta_if_new(t_l:pfc_module_expansion(M))).

% ================================================================================
% DETECT PREDS THAT NEED SPECIAL STORAGE 
% ================================================================================


%% pfc_may_expand is det.
%
% Managed Predicate May Expand.
%
pfc_may_expand:-loading_source_file(_F),get_lang(pfc).
pfc_may_expand:-loading_source_file(_F),get_lang(mpred).
pfc_may_expand:-quietly_must(loading_module(M)),pfc_may_expand_module(M),!,pfc_expand_inside_file_anyways.




%% pfc_may_expand_module( ?M) is det.
%
% Managed Predicate May Expand Module.
%
pfc_may_expand_module(M):-baseKB:pfc_skipped_module(M),!,fail.
pfc_may_expand_module(M):-module_property(M,file(F)),check_how_virtualize_file(heads,F).
pfc_may_expand_module(M):- t_l:pfc_module_expansion(M),!.
pfc_may_expand_module(_):- t_l:pfc_module_expansion(*),!.




%% pfc_expand_inside_file_anyways is det.
%
% Managed Predicate Expand Inside File Anyways.
%
pfc_expand_inside_file_anyways:- loading_source_file(F),!,pfc_expand_inside_file_anyways(F).




%% pfc_expand_inside_file_anyways( ?F) is det.
%
% Managed Predicate Expand Inside File Anyways.
%
pfc_expand_inside_file_anyways(F):- var(F),!,loading_source_file(F),nonvar(F),pfc_expand_inside_file_anyways(F).
pfc_expand_inside_file_anyways(F):- check_how_virtualize_file(heads,F), !.
pfc_expand_inside_file_anyways(F):- t_l:loading_mpred_file(_,F),!.
pfc_expand_inside_file_anyways(F):- check_how_virtualize_file(heads,F),quietly_must(loading_module(M);source_module(M)), 
  (M=user; \+ baseKB:pfc_skipped_module(M)),!.




%% was_exported_content( ?I, ?CALL, ?Output) is det.
%
% Was Exported Content.
%
was_exported_content(I,CALL,'$si$':'$was_imported_kb_content$'(I,CALL)).

:- thread_local(t_l:pfc_term_expansion_ok/0).
:- thread_local(t_l:pfc_already_inside_file_expansion/1).

:- assert_if_new(t_l:pfc_term_expansion_ok).





%% pfc_provide_clauses( ?H, ?B, ?What) is det.
%
% Hook To [baseKB:pfc_provide_clauses/3] For Module Mpred_loader.
% Managed Predicate Provide Clauses.
%
baseKB:pfc_provide_clauses(_H,_B,_What):- fail.




%% show_interesting_cl( ?Dir, ?VALUE2) is det.
%
% Show Interesting Clause.
%
show_interesting_cl(_Dir,_).
show_interesting_cl(Dir,P):- loading_source_file(File),get_file_type(File,Type),
  ((nonvar(Dir),functor(Dir,Type,_))->true;dmsg_pretty(Type:cl_assert(Dir,P))).

:- meta_predicate(cl_assert(?,?)).



%% cl_assert( ?Dir, ?P) is det.
%
% Clause Assert.
%
cl_assert(kif(Dir),P):- show_if_debug(must_det_l(( show_interesting_cl(kif(Dir),P),call(call,kif_process,P)))),!.
cl_assert(Dir,P):- show_interesting_cl(Dir,P),ain(P),!.
cl_assert(pl,P):-  !, show_if_debug(must_det_l((source_location(F,_L), '$compile_aux_clauses'(P,F)))).
cl_assert(_Code,P):- !, show_if_debug(ain(P)).

:- meta_predicate(call_file_command(?,?,?,?)).
%call_file_command(_,cl_assert(pl,OO),OO,_):-!,show_interesting_cl(pl,OO).


get_original_term_src(Orig):- nb_current('$orig_term',Orig),!. 
get_original_term_src(Orig):- nb_current('$term',Orig),Orig\==[],!. 
get_original_term_src(true).

make_file_command(IN,(:- CALL),OUT):- nonvar(CALL),!, must(make_file_command(IN,CALL,OUT)).

make_file_command(_IN,cl_assert(pfc(WHY),PFC),(NEWSOURCE:-true)):- 
  current_why(CY),
  CMD = pfc_ain(PFC,(CY,ax)),
  get_original_term_src(Orig),
  was_exported_content(Orig,WHY,NEWSOURCE),!,
  show_call(quietly_must((CMD))).


make_file_command(_IN,cl_assert(pfc(WHY),PFC),[(:- CMD), NEWSOURCE]):- 
  current_why(CY),
  CMD = ain(PFC,CY),
  get_original_term_src(Orig),
  was_exported_content(Orig,WHY,NEWSOURCE),!.
  

make_file_command(IN,cl_assert(WHY,NEWISH),OUT):- get_lang(kif),if_defined(is_kif_clause(NEWISH)),!,must(make_file_command(IN,cl_assert(kif(WHY),NEWISH),OUT)).
make_file_command(_IN,cl_assert(WHY,CMD2),SET):- 
  get_original_term_src(Orig),
  was_exported_content(Orig,WHY,NEWSOURCE),list_to_set([(:- cl_assert(WHY,CMD2)), NEWSOURCE],SET).
 
make_file_command(IN,cl_assert(WHY,CMD2),[CMD2, (:- cl_assert(WHY,CMD2)), NEWSOURCE ]):- was_exported_content(WHY,IN,NEWSOURCE),!.

make_file_command(_IN,'$si$':'$was_imported_kb_content$'(IN2,WHY),'$si$':'$was_imported_kb_content$'(IN2,WHY)).


%% call_file_command( ?I, ?CALL, ?OO, ?O) is det.
%
% Call File Command.
%
call_file_command(I,CALL,OO,O):- call_file_command0(I,CALL,OO,O),dmsg_pretty(call_file_command(I,CALL,OO,O)).

call_file_command0(I,cl_assert(OTHER,OO),OO,I):- get_lang(kif),if_defined(is_kif_clause(OO)),!,call_file_command(I,cl_assert(kif(OTHER),OO),OO,I).
call_file_command0(I,CALL,[(:- quietly_must(CALL2)),(:- quietly_must(CALL)),OO],(:-CALL2)):- CALL2\=@=CALL, 
  was_exported_content(I,CALL,OO),!.
call_file_command0(I,CALL,[(:- quietly_must(CALL)),OO],(:-CALL)):- was_exported_content(I,CALL,OO),!.
% call_file_command(I,CALL,OO,O):- (current_predicate(_,CALL) -> ((quietly_must(call(CALL)),was_exported_content(I,CALL,OO))); OO=[O,:-CALL]).



%% pfc_implode_varnames( :TermN) is det.
%
% Managed Predicate Implode Varnames.
%
pfc_implode_varnames([]):-!.
pfc_implode_varnames([N=V|Vs]):-V='$VAR'(N),pfc_implode_varnames(Vs),!.

% mudKeyword("happy","happy") -> mudKeyword(vHappy,"happy").

% quietly_must skip already loaded modules (we remember these so make/0 doesnt dbreak)



%% pfc_maybe_skip( ?M) is det.
%
% Managed Predicate Maybe Skip.
%
pfc_maybe_skip(M):- t_l:pfc_module_expansion(N),N==M,!.
pfc_maybe_skip(M):- asserta_if_new(baseKB:pfc_skipped_module(M)),!.
% :- forall(current_module(M),pfc_maybe_skip(M)).


:- dynamic(lmcache:pfc_directive_value/3).





%% expanded_already_functor( :TermARG1) is det.
%
% Expanded Already Functor.
%
expanded_already_functor('$si$':'$was_imported_kb_content$').
expanded_already_functor(was_enabled).
expanded_already_functor(_:NV):-nonvar(NV),!,expanded_already_functor(NV).

% expanded_already_functor(F):-pfc_prop(M,F,A,pl).


%:- thread_local is_compiling_clause/0.
%is_compiling:-is_compiling_clause;compiling.

%:- kb_local(user:term_expansion/2).
%:- kb_local(system:goal_expansion/2).
% system:goal_expansion(A,_B):-fail,quietly((source_module(M),(M=pfc_sanity;M=user;M=system),if_defined(pmsg(M:goal_expansion(A)),format(user_output /*e*/,'~N% ~q~n',M:goal_expansion(A))))),fail.
% user:term_expansion(A,_B):-fail,quietly((source_module(M),(M=pfc_sanity;M=user;M=system),if_defined(pmsg(M:term_expansion(A)),format(user_output /*e*/,'~N% ~q~n',M:term_expansion(A))))),fail.

% system:goal_expansion(N,pfc_prove_neg(P)):-fail,mpred_from_negation_plus_holder(N,P),show_failure(why,pfc_isa(P,pfcControlled)).




%% setup_module_ops is det.
%
% Managed Predicate Oper.s.
%
pfc_ops:-  prolog_load_context(module,M),setup_module_ops(M).


%% pfc_dcg is det.
%
% Managed Predicate Dcg Oper.s.
%
pfc_dcg:- file_begin(pfc), op(400,yfx,('\\\\')),op(1200,xfx,('-->>')),op(1200,xfx,('--*>>')), op(1200,xfx,('<<--')).

:- thread_local(pfc_ain_loaded/0).






% ========================================
% begin/end_transform_mpreds
% ========================================
:- dynamic(t_l:current_lang/1).


:- dynamic(always_expand_on_thread/1).
:- thread_local is_compiling_clause/0.

%% is_compiling is det.
%
% If Is A Compiling.
%
is_compiling:-is_compiling_clause;compiling.

:- style_check(+discontiguous).
:- style_check(-discontiguous).


unload_this_file(File):- 
   ignore((
   source_file(M:P,File),
   copy_term(P,PP),
   clause(M:P,_,Ref),
   clause_property(Ref,file(File)),
   erase(Ref),
   \+ clause(M:PP,_,_),
   abolish(M:PP),fail)),
   unload_file(File).


:- export(clause_count/2).
:- module_transparent(clause_count/2).

clause_count(Mask,N):- arg(_,Mask,Var),nonvar(Var),!,
   flag(clause_count,_,0),
    ignore((current_module(M),clause(M:Mask,_,Ref),
       (clause_property(Ref,module(MW))->must(ignore((M==MW)));true),
       flag(clause_count,X,X+1),fail)),flag(clause_count,N,0),!.
clause_count(Mask,N):- 
     flag(clause_count,_,0),
      ignore((current_module(M), M\==rdf_rewrite,
         \+ predicate_property(M:Mask,imported_from(_)),
         predicate_property(M:Mask,number_of_clauses(Count)),
         flag(clause_count,X,X), must(ignore(sanity((X=0,nop(clause_count(Mask,M,Count)))))),
         flag(clause_count,X,X+Count),fail)),flag(clause_count,N,0),!.


:- dynamic(checked_clause_count/1).

checked_clause_count(isa(_,_)).
checked_clause_count(~(_)).
checked_clause_count(prologBuiltin(_)).
checked_clause_count(prologHybrid(_)).
checked_clause_count(hybrid_support(_)).
checked_clause_count(pfcControlled(_)).
checked_clause_count(t(_,_)).
checked_clause_count(t(_,_,_)).
checked_clause_count(arity(_,_)).
checked_clause_count(argIsa(_,_,_)).
checked_clause_count(argQuotedIsa(_,_,_)).
checked_clause_count(tCol(_)).
checked_clause_count(resultIsa(_,_)).
checked_clause_count(genls(_,_)).
checked_clause_count((_ <- _)).
checked_clause_count((_ ==> _)).
checked_clause_count((_ <==> _)).
%checked_clause_count(spft(_,_,ax)).
checked_clause_count(agent_command(_,_)).
checked_clause_count(how_virtualize_file(_,_,_)).


:- dynamic(lmcache:last_clause_count/2).

check_clause_count(MMask):- swc,
 strip_module(MMask,_,Mask),
 clause_count(Mask,N),
    (retract(lmcache:last_clause_count(Mask,Was)) -> true ; Was=0),
     (assert(lmcache:last_clause_count(Mask,N)),
     Diff is N - Was), 
     (Diff ==0 -> true;
     (Diff == -1 -> true;
     ((Diff<0 ,Change is N/abs(Diff ), Change>0.20)
         -> trace_or_throw_ex(bad_count(Mask,(Was --> N))) ; dmsg_pretty(good_count(Mask,(Was --> N)))))).

check_clause_counts:-!.
check_clause_counts:- flag_call(runtime_speed==true),!.
check_clause_counts:- current_prolog_flag(unsafe_speedups , true) ,!.
check_clause_counts:- ((forall(checked_clause_count(Mask),sanity(check_clause_count(Mask))))),fail.
check_clause_counts.
:- sexport(check_clause_counts/0).



%% pfc_begin is det.
%
% Managed Predicate Begin.
%
pfc_begin:-file_begin(pfc).



%% dyn_begin is det.
%
% Dyn Begin.
%
dyn_begin:-file_begin(dyn).



%% dyn_end is det.
%
% Dyn End.
%
dyn_end:-file_end(dyn).

        


%% enable_pfc_expansion is det.
%
% Enable Managed Predicate Expansion.
%
enable_pfc_expansion :- 
    set_prolog_flag(pfc_te,true),
     (( \+ (t_l:disable_px, false )) -> true ;
                 (retractall(t_l:disable_px),
                 call_on_eof(asserta_if_new(t_l:disable_px)))).




%% disable_pfc_expansion is det.
%
% Disable Managed Predicate Expansion.
%
disable_pfc_expansion:- 
            set_prolog_flag(pfc_te,false),
             (( t_l:disable_px) -> true ;
                 assert_until_eof(t_l:disable_px)).



predicate_is_undefined_fa(F,A):-
  call((
  ( \+ current_predicate(_:F/A)),
  functor(P,F,A),
  (( 
  \+ predicate_property(_:P,exported),
  \+ predicate_property(_:P,static),
  \+ predicate_property(_:P,dynamic))))).


:-multifile(baseKB:locked_baseKB/0).
:-dynamic(baseKB:locked_baseKB/0).

simplify_language_name(W,W2):-var(W),!,W2=W.
simplify_language_name(mpred,pfc).
simplify_language_name(plmoo,pfc).
simplify_language_name(prolog,pl).
simplify_language_name(code,pl).
simplify_language_name(W,W).

%% file_begin( ?W) is det.
%
% File Begin.
%

file_begin(WIn):- simplify_language_name(WIn,pfc), !, begin_pfc,op_lang(WIn).
file_begin(WIn):- 
 simplify_language_name(WIn,Else), 
 must_det_l((   
   op_lang(WIn),
   set_file_lang(Else),
   disable_pfc_expansion)),!,
   sanity(get_lang(Else)).


%% begin_pfc is det.
%
% Begin Prolog Forward Chaining.
%
begin_pfc:- 
 must_det_l((   
   pfc_ops,
   op_lang(pfc),
   set_file_lang(pfc),
   fileAssertMt(Mt),
   set_fileAssertMt(Mt),
   enable_pfc_expansion)),!,
   sanity(get_lang(pfc)).

:- nodebug(logicmoo(loader)).

set_file_lang(W):- 
   source_location(File,_Line),
   assert_if_new(lmcache:pfc_directive_value(File,language,W)),
   (W==pfc-> (set_how_virtualize_file(heads,File)) ; true),!,
  set_lang(W).
set_file_lang(W):-
  forall((prolog_load_context(file,Source);which_file(Source);prolog_load_context(source,Source)),
  ignore((  % \+ lmcache:pfc_directive_value(Source,language,W),
  source_location(File,Line),
  (W==pfc-> (set_how_virtualize_file(heads,File)) ; true),
  prolog_load_context(module,Module),
  INFO = source_location_lang(Module,File,Line,Source,W),
  asserta(lmconf:INFO),
  decache_file_type(Source),
  debug(logicmoo(loader),'~N~p~n',[INFO]),
  % (Source = '/root/lib/swipl/pack/logicmoo_base/prolog/logicmoo/pfc/system_common.pfc.pl'-> must(W=pfc);true),
  assert(lmcache:pfc_directive_value(Source,language,W))))),
  sanity(get_lang(W)),
  asserta_until_eof(t_l:current_lang(W)),!.


set_lang(WIn):- simplify_language_name(WIn,W),!,
   set_prolog_flag_until_eof(dialect_pfc,W),
   asserta_until_eof(t_l:current_lang(W)).
    

%% file_end( ?W) is det.
%
% File End.
%
file_end(WIn):- 
 must_det((
  simplify_language_name(WIn,W),
  loading_source_file(ISource),decache_file_type(ISource),
  ignore(show_failure(retract(lmcache:pfc_directive_value(ISource,language,W)))))),!.


%% get_lang( ?LANG) is det.
%
% Get Language.
% Inside File.
%
get_lang(LANG):- ((get_lang0(LANGVAR)->same_language(LANG,LANGVAR))).

same_language(LANG,LANGVAR):- 
    simplify_language_name(LANGVAR,LANGVARS),
    simplify_language_name(LANG,LANGS),!,
    LANGS=LANGVARS.

:-thread_local( t_l:current_lang/1).

get_lang0(W) :- t_l:current_lang(W),!.
get_lang0(W) :- prolog_load_context(file,Source)->lmcache:pfc_directive_value(Source,language,W).
get_lang0(W) :- prolog_load_context(source,Source)->lmcache:pfc_directive_value(Source,language,W).
get_lang0(W) :- loading_source_file(Source)->lmcache:pfc_directive_value(Source,language,W).
get_lang0(W):- current_prolog_flag(dialect_pfc,W).
get_lang0(pfc):- loading_source_file(F)->check_how_virtualize_file(heads,F),!.
get_lang0(pl).





:- meta_predicate(expand_term_to_load_calls(?,?)).
:- meta_predicate(pfc_term_expansion(?,?)).

% Specific "*SYNTAX*" based default

% :- ensure_loaded(logicmoo(snark/common_logic_sexpr)).




%% op_alias( ?OP, ?OTHER) is det.
%
% Oper. Alias.
%
op_alias(OP,OTHER):-retractall(current_op_alias(OP,_)),asserta(current_op_alias(OP,OTHER)).



%% op_lang( ?LANG) is det.
%
% Oper. Language.
%
op_lang(_LANG):- !.




%% get_op_alias( ?OP, ?ALIAS) is det.
%
% Get Oper. Alias.
%
get_op_alias(OP,ALIAS):-current_op_alias(OP,ALIAS).
get_op_alias(OP,ALIAS):-get_lang(LANG),lang_op_alias(LANG,OP,ALIAS).

% current_op_alias((<==>),dup(impliesF,(','))).
% current_op_alias((=>),==>).
% current_op_alias((not),(~)).



%% current_op_alias( ?VALUE1, ?VALUE2) is det.
%
% Current Oper. Alias.
%
:- dynamic(current_op_alias/2).
current_op_alias( not(:-),~(:-)).
current_op_alias( (:-),(:-)).



%% lang_op_alias( ?VALUE1, ?VALUE2, ?VALUE3) is det.
%
% Language Oper. Alias.
%
lang_op_alias(pfc,(<==>),(<==>)).
lang_op_alias(pfc,(==>),==>).
% lang_op_alias(pfc,(<=>),(<==>)).
lang_op_alias(pfc,(<=),(<-)).
lang_op_alias(pfc,(<-),(<-)).
lang_op_alias(pfc,(not),(~)).
lang_op_alias(pfc,not(:-),~(:-)).
lang_op_alias(pfc,(:-),(:-)).
% lang_op_alias(pfc,(A=B),{(A=B)}).
% kif
lang_op_alias(kif,(<==>),(<==>)).
lang_op_alias(kif,(==>),==>).
lang_op_alias(kif,(not),(~)).
lang_op_alias(kif,(~),(~)).
lang_op_alias(kif,(=>),(if)).
lang_op_alias(kif,(<=>),(iff)).
lang_op_alias(kif, not(':-'),~('<-')).
lang_op_alias(kif,(:-),rev(==>)).
% cyc
lang_op_alias(cyc,(<==>),(<==>)).
lang_op_alias(cyc,(==>),==>).
lang_op_alias(cyc,(implies),(if)).
lang_op_alias(cyc,(equiv),(iff)).
lang_op_alias(cyc, not(':-'),~('<-')).
lang_op_alias(cyc,(:-),rev(==>)).
% prolog - pl
lang_op_alias(pl,(<==>),(<==>)).
lang_op_alias(pl,(==>),==>).
lang_op_alias(pl, not(':-'),~('<-')).
lang_op_alias(pl,(:-),(:-)).
lang_op_alias(pl,(<=),(<=)).
lang_op_alias(pl,(<-),(<-)).




%% transform_opers( ?LANG, ?PFCM, ?PFCO) is det.
%
% Transform Opers.
%
transform_opers(LANG,PFCM,PFCO):- quietly((locally(t_l:current_lang(LANG),((transitive_lc(transform_opers_0,PFCM,PFC),!, subst(PFC,(not),(~),PFCO)))))).

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




%% transform_opers_0( ?AIS, ?AIS) is det.
%
% transform opers  Primary Helper.
%
transform_opers_0(AIS,AIS):- if_defined(leave_as_is(AIS)),!.
transform_opers_0((A/B),C):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]),conjoin_op((/),AA,BB,C).
transform_opers_0(PFCM,PFC):- transform_opers_1(PFCM,PFC),!.
transform_opers_0(=>(A),=>(C)):- !, transform_opers_0(A,C).
transform_opers_0(==>(A),==>(C)):- !, transform_opers_0(A,C).
transform_opers_0(~(A),~(C)):- !, transform_opers_0(A,C).
transform_opers_0(nesc(A),nesc(C)):- !, transform_opers_0(A,C).
transform_opers_0({A},{A}):-!.
transform_opers_0((A;B),C):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]),conjoin_op((;),AA,BB,C).
transform_opers_0((B=>A),(BB=>AA)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0((B==>A),(BB==>AA)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0(<=(A,B),<=(AA,BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0((A<-B),(AA<-BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0((A<=>B),(AA<=>BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0((A<==>B),(AA<==>BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0((A<==>B),(AA<==>BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0(if(A,B),if(AA,BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0(iff(A,B),iff(AA,BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0(implies(A,B),implies(AA,BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0(equiv(A,B),equiv(AA,BB)):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]).
transform_opers_0((B:-A),OUTPUT):- !, must_maplist(transform_opers_0,[A,B],[AA,BB]),=((BB:-AA),OUTPUT).
transform_opers_0(not(A),OUTPUT):- !, must_maplist(transform_opers_0,[A],[AA]),=(not(AA),OUTPUT).
transform_opers_0(not(A),C):- !, transform_opers_0(~(A),C).
%transform_opers_0((A),OUTPUT):- !, must_maplist(transform_opers_0,[A],[AA]),=((AA),OUTPUT).
transform_opers_0(O,O).




%% transform_opers_1( ?AB, ?BBAA) is det.
%
% transform opers  Secondary Helper.
%
transform_opers_1(not(AB),(BBAA)):- get_op_alias(not(OP),rev(OTHER)), atom(OP),atom(OTHER),AB=..[OP,A,B],!, must_maplist(transform_opers_0,[A,B],[AA,BB]),BBAA=..[OTHER,BB,AA].
transform_opers_1(not(AB),(BOTH)):- get_op_alias(not(OP),dup(OTHER,AND)),atom(OTHER), atom(OP),AB=..[OP,A,B],!, must_maplist(transform_opers_0,[A,B],[AA,BB]),AABB=..[OTHER,AA,BB],BBAA=..[OTHER,BB,AA],BOTH=..[AND,AABB,BBAA].
transform_opers_1(not(AB),~(NEG)):- get_op_alias(not(OP),~(OTHER)),atom(OTHER), atom(OP),AB=..[OP|ABL],!, must_maplist(transform_opers_0,ABL,AABB),NEG=..[OTHER|AABB].
transform_opers_1(not(AB),(RESULT)):- get_op_alias(not(OP),(OTHER)), atom(OP),atom(OTHER),AB=..[OP|ABL],!, must_maplist(transform_opers_0,ABL,AABB),RESULT=..[OTHER|AABB].
transform_opers_1((AB),(BBAA)):- get_op_alias(OP,rev(OTHER)), atom(OP),atom(OTHER),AB=..[OP,A,B],!, must_maplist(transform_opers_0,[A,B],[AA,BB]),BBAA=..[OTHER,BB,AA].
transform_opers_1((AB),(BOTH)):- get_op_alias(OP,dup(OTHER,AND)), atom(OP),atom(OTHER),AB=..[OP,A,B],!, must_maplist(transform_opers_0,[A,B],[AA,BB]),AABB=..[OTHER,AA,BB],BBAA=..[OTHER,BB,AA],BOTH=..[AND,AABB,BBAA].
transform_opers_1((AB),(RESULT)):- get_op_alias(OP,(OTHER)),atom(OP), atom(OTHER),AB=..[OP|ABL],!, must_maplist(transform_opers_0,ABL,AABB),RESULT=..[OTHER|AABB].
transform_opers_1(OP,OTHER):- get_op_alias(OPO,OTHER),OPO=OP,!.

%% Possibly should term expand since we are in the userKb modules



%% to_prolog_xform(+Clause,-Command) is det.
%
% Convert an input clause to a call that will have assumed it is loaded
%
to_prolog_xform(O,OO):-
    ( is_directive_form(O) -> (OO = O); OO=  (:- cl_assert(pfc(to_prolog_xform),O))),!.



%% is_directive_form( :TermV) is det.
%
% If Is A Prolog Xform.
%
is_directive_form((:-(V))):-!,nonvar(V).
is_directive_form((?-(V))):-!,nonvar(V).
is_directive_form(List):-is_list(List),!,member(E,List),is_directive_form(E).
%is_directive_form((:-(V,_))):-!,nonvar(V).
%is_directive_form(_:(:-(V,_))):-!,nonvar(V).





%% expand_in_pfc_kb_module( ?I, ?O) is det.
%
% Expand In Managed Predicate Knowledge Base Module.
%
expand_in_pfc_kb_module(I,O):- is_directive_form(I),quietly_must(I=O),!.
expand_in_pfc_kb_module(I,OO):- quietly_must(expand_term_to_load_calls(I,O)),!,quietly_must(to_prolog_xform(O,OO)).


%% expand_term_to_load_calls( ?I, ?OO) is det.
%
% Load File Term Converted To Command 0c.
%
expand_term_to_load_calls(I,OO):- if_defined(convert_if_kif_string(I,O)),!,
   quietly_must(expand_term_to_load_calls(O,OO)).

expand_term_to_load_calls(PI,OO):- PI=..[P,I], if_defined(convert_if_kif_string(I,O)),!,
   quietly_must((PO=..[P,O], expand_term_to_load_calls(PO,OO))).

expand_term_to_load_calls((H:-B),O):- B==true,!,quietly_must(expand_term_to_load_calls(H,O)).

expand_term_to_load_calls(HB,O):- strip_module(HB,M,(H:-B)),B==true,(H:-B)\=@=HB,!,quietly_must(expand_term_to_load_calls(M:H,O)).

expand_term_to_load_calls(C,O):- fail,  quietly((get_lang(LANG),show_success(transform_opers,(quietly_must(transform_opers(LANG,C,M)),C\=@=M)))),!,
   quietly_must(expand_term_to_load_calls(M,O)).

expand_term_to_load_calls(C,O):- fail,quietly(show_success(load_calls,(compound(C), get_op_alias(OP,ALIAS),
  atom(OP),atom(ALIAS),C=..[OP|ARGS]))),CC=..[ALIAS|ARGS],quietly_must(loop_check(must_expand_term_to_command(CC,O))),!.

expand_term_to_load_calls(C,O):- must_expand_term_to_command(C,O)->quietly_must(is_directive_form(O)).
expand_term_to_load_calls(O,(:-compile_clause(O))):- get_lang(pl),!.


%% must_expand_term_to_command( ?M, ?O) is det.
%
% Must Be Successfull Managed Predicate term expansion  Extended Helper.
%
must_expand_term_to_command(C,O):- pfc_term_expansion(C,O),C\=@=O,quietly_must(is_directive_form(O)),!.
must_expand_term_to_command(O,(:-compile_clause(O))):- get_lang(pl),!.

%% pfc_term_expansion( ?Fact, ?Output) is det.
%
% Managed Predicate Term Expansion.
%

pfc_term_expansion(((P==>Q)),(:- cl_assert(pfc(fwc),(P==>Q)))).
pfc_term_expansion((('=>'(Q))),(:- cl_assert(pfc(fwc),('=>'(Q))))).
pfc_term_expansion((('==>'(Q))),(:- cl_assert(pfc(fwc),('=>'(Q))))).
pfc_term_expansion(((nesc(Q))),(:- cl_assert(pfc(fwc),nesc(Q)))).
pfc_term_expansion(~(Q),(:- cl_assert(pfc(fwc),~(Q)))).
pfc_term_expansion(('<-'(P,Q)),(:- cl_assert(pfc(bwc),('<-'(P,Q))))).
pfc_term_expansion(('<==>'(P,Q)),(:- cl_assert(pfc(bwc),(P<==>Q)))).
pfc_term_expansion((<=(Q,P)),(:- cl_assert(pfc(bwc),(Q<-P)))).



pfc_term_expansion(if(P,Q),(:- cl_assert(kif(fwc),if(P,Q)))).
pfc_term_expansion(iff(P,Q),(:- cl_assert(kif(fwc),iff(P,Q)))).
pfc_term_expansion(not(Q),(:- cl_assert(kif(fwc),not(Q)))).
pfc_term_expansion(exists(V,PQ),(:- cl_assert(kif(fwc),exists(V,PQ)))).
pfc_term_expansion(forall(V,PQ),(:- cl_assert(kif(fwc),forall(V,PQ)))).
pfc_term_expansion(all(V,PQ),(:- cl_assert(kif(fwc),all(V,PQ)))).


% maybe reverse some rules?
%pfc_term_expansion((P==>Q),(:- cl_assert(pfc(fwc),('<-'(Q,P))))).  % speed-up attempt
pfc_term_expansion((RuleName :::: Rule),(:- cl_assert(named_rule,(RuleName :::: Rule)))).
pfc_term_expansion((==>(P)),(:- cl_assert(pfc(fwc),(==>(P))))).
pfc_term_expansion(Fact,(:- cl_assert(pl,Fact))):- get_functor(Fact,F,_A),(a(prologDynamic,F)).
pfc_term_expansion(Fact,Output):- load_file_term_to_command_1(_Dir,Fact,C),quietly_must(pfc_term_expansion(C,Output)),!.


%% load_file_term_to_command_1( ?Type, :TermIn, :TermOut) is det.
%
% load file term Converted To command  Secondary Helper.
%
      load_file_term_to_command_1(pfc(act),(H:-(Chain,B)),(PFC==>PH)):-cwc, is_action_body(Chain),pl_to_pfc_syntax((Chain,B),PFC),pl_to_pfc_syntax_h(H,PH).
      load_file_term_to_command_1(pfc(fwc),(H:-(Chain,B)),(PFC==>PH)):-cwc, is_fc_body(Chain),pl_to_pfc_syntax((Chain,B),PFC),pl_to_pfc_syntax_h(H,PH),can_be_dynamic(PH),make_dynamic(PH).
      load_file_term_to_command_1(pfc(bwc),(H:-(Chain,B)),(PH<-PFC)):-cwc, is_bc_body(Chain),pl_to_pfc_syntax((Chain,B),PFC),pl_to_pfc_syntax_h(H,PH),can_be_dynamic(PH),make_dynamic(PH).
      load_file_term_to_command_1(pfc(awc),(H:-(Chain,B)),(H:-(Chain,B))):-cwc, has_body_atom(awc,Chain),!.
      load_file_term_to_command_1(pfc(zwc),(H:-(Chain,B)),(H:-(Chain,B))):-cwc, has_body_atom(zwc,Chain),!.


pfc_term_expansion(Fact,Output):- load_file_term_to_command_1b(_Dir,Fact,C),!,quietly_must(pfc_term_expansion(C,Output)),!.

%% load_file_term_to_command_1b( ?VALUE1, :TermH, :TermH) is det.
%
% Load File Term Converted To Command 1b.
%
      load_file_term_to_command_1b(pfc(act),(H:-Chain,B),(H==>{(Chain,B)})):-cwc, is_action_body(Chain),make_dynamic(H).
      load_file_term_to_command_1b(pfc(fwc),(H:-Chain,B),((Chain,B)==>H)):-cwc, is_fc_body(Chain),make_dynamic(H).
      load_file_term_to_command_1b(pfc(bwc),(H:-Chain,B),(H<-(Chain,B))):-cwc, is_bc_body(Chain),make_dynamic(H).


% pfc_term_expansion((H:-Chain,B),(H:-(B))):- atom(Chain),is_code_body(Chain),!,quietly_must(atom(Chain)),make_dynamic(H).



  
pfc_term_expansion_by_storage_type(_M,'$si$':'$was_imported_kb_content$'(_,_),pl):-!.
pfc_term_expansion_by_storage_type(M,( \+ C ),HOW):- nonvar(C), !,pfc_term_expansion_by_storage_type(M,C,HOW).
pfc_term_expansion_by_storage_type(_M,C,compile_clause(static)):- is_static_predicate(C).
%pfc_term_expansion_by_storage_type(_M,C,requires_storage(WHY)):- requires_storage(C,WHY),!.
pfc_term_expansion_by_storage_type(_M,C,must_compile_special):- must_compile_special_clause(C),t_l:pfc_already_inside_file_expansion(C).


pfc_term_expansion(Fact,Fact):- get_functor(Fact,F,_A),(a(prologDynamic,F)),!.
pfc_term_expansion(Fact,(:- ((cl_assert(Dir,Fact))))):- show_success(pfc_term_expansion_by_pred_class(Dir,Fact,_Output)),!.

pfc_term_expansion(MC,(:- cl_assert(ct(How),MC))):- fail, strip_module(MC,M,C),quietly(pfc_rule_hb(C,H,_B)),
  (pfc_term_expansion_by_storage_type(M,H,How)->true;(C \= (_:-_),pfc_term_expansion_by_storage_type(M,C,How))),!.


pfc_term_expansion((Fact:- BODY),(:- ((cl_assert(Dir,Fact:- BODY))))):- nonvar(Fact),
   pfc_term_expansion_by_pred_class(Dir,Fact,_Output),!.

pfc_term_expansion((M:Fact:- BODY),(:- ((cl_assert(Dir,M:Fact:- BODY))))):- nonvar(Fact),
   pfc_term_expansion_by_pred_class(Dir,Fact,_Output),!.

%% pfc_term_expansion_by_pred_class( ?VALUE1, ?Fact, ?Output) is det.
%
% load file term Converted To command  Extended Helper.
% Specific to the "*PREDICATE CLASS*" based default
%
      pfc_term_expansion_by_pred_class(_,Fact,Output):- get_functor(Fact,F,_A),lookup_u(prologOnly(F)),Output='$si$':'$was_imported_kb_content$'(Fact,pfcControlled(F)),!,fail.
      pfc_term_expansion_by_pred_class(pfc(pred_type),Fact,Output):- get_functor(Fact,F,_A),lookup_u(ttRelationType(F)),Output='$si$':'$was_imported_kb_content$'(Fact,ttRelationType(F)),!.
      pfc_term_expansion_by_pred_class(pfc(func_decl),Fact,Output):- get_functor(Fact,F,_A),lookup_u(functorDeclares(F)),Output='$si$':'$was_imported_kb_content$'(Fact,functorDeclares(F)),!.
      pfc_term_expansion_by_pred_class(pfc(macro_head),Fact,Output):- get_functor(Fact,F,_A),lookup_u(functorIsMacro(F)),Output='$si$':'$was_imported_kb_content$'(Fact,functorIsMacro(F)),!.
      pfc_term_expansion_by_pred_class(pfc(pfc_ctrl),Fact,Output):- get_functor(Fact,F,_A),lookup_u(pfcControlled(F)),Output='$si$':'$was_imported_kb_content$'(Fact,pfcControlled(F)),!.
      pfc_term_expansion_by_pred_class(pfc(hybrid),Fact,Output):- get_functor(Fact,F,_A),lookup_u(prologHybrid(F)),Output='$si$':'$was_imported_kb_content$'(Fact,pfcControlled(F)),!.
      pfc_term_expansion_by_pred_class(pfc(pl),Fact,Output):- get_functor(Fact,F,_A),(a(prologDynamic,F)),Output='$si$':'$was_imported_kb_content$'(Fact,pfcControlled(F)),!.
      % pfc_term_expansion_by_pred_class(pfc(in_pfc_kb_module),Fact,Output):- in_pfc_kb_module,Output=Fact,!.


% Specific "*FILE*" based default
pfc_term_expansion(Fact,(:- ((cl_assert(dyn(get_lang(dyn)),Fact))))):- get_lang(dyn),!.
pfc_term_expansion(Fact,(:- ((cl_assert(kif(get_lang(kif)),Fact))))):- get_lang(kif),!.
%pfc_term_expansion(Fact,(:- ((cl_assert(pfc(in_pfc_kb_module),Fact))))):- in_pfc_kb_module,!.
%pfc_term_expansion(Fact,(:- ((cl_assert(pfc(get_lang(pl)),Fact))))):- get_lang(pl),!.
pfc_term_expansion(Fact,Fact):- get_lang(pl),!.
%pfc_term_expansion(Fact,(:- ((cl_assert(pfc(get_lang(pfc)),Fact))))):- get_lang(pfc),!.

/*
pfc_term_expansion(Fact,(:- ((cl_assert(pfc(expand_file),Fact))))):-
    quietly(pfc_expand_inside_file_anyways(F)),!,_Output='$si$':'$was_imported_kb_content$'(Fact,pfc_expand_inside_file_anyways(F)),!.
*/




%% can_be_dynamic( ?H) is det.
%
% Can Be Dynamic.
%
can_be_dynamic(H):- predicate_property(H,dynamic),!.
can_be_dynamic( \+ H):- nonvar(H), predicate_property(H,dynamic),!.
can_be_dynamic(H):- \+ is_static_predicate(H), \+ predicate_property(H,static),  \+ predicate_property(H,meta_predicate(_)).




%% pl_to_pfc_syntax_h( ?A, ?PFC_A) is det.
%
% Pl Converted To Managed Predicate Syntax Head.
%
pl_to_pfc_syntax_h(A,PFC_A):- quietly_must(pl_to_pfc_syntax0(A,PFC_A)),!, PFC_A \= '{}'(_).



%% pl_to_pfc_syntax( ?A, ?PFC_A) is det.
%
% Pl Converted To Managed Predicate Syntax.
%
pl_to_pfc_syntax(A,PFC_A):- quietly_must(pl_to_pfc_syntax0(A,PFC_A)),!.




%% pl_to_pfc_syntax0( ?A, ?A) is det.
%
% Pl Converted To Managed Predicate Syntax Primary Helper.
%
pl_to_pfc_syntax0(A,A):-is_ftVar(A),!.
pl_to_pfc_syntax0((A,B),PFC):-!,pl_to_pfc_syntax(A,PFC_A),pl_to_pfc_syntax(B,PFC_B),conjoin_body(PFC_A,PFC_B,PFC).
pl_to_pfc_syntax0(pfc(A),A):-!.
pl_to_pfc_syntax0(A,{A}):-!.



%% conjoin_body( ?H, B, ?C) is semidet.
%
% Conjoin Body.
%
conjoin_body({H},{BB},{C}):-conjoin_body(H,BB,C).
conjoin_body({H},({BB},D),O):-conjoin_body(H,BB,C),conjoin_body({C},D,O).
conjoin_body(H,(BB,D),O):-conjoin_body(H,BB,C),conjoin_body(C,D,O).
conjoin_body(H,BB,C):-conjoin(H,BB,C).


%% stream_pos( :TermFile) is det.
%
% Stream Pos.
%
stream_pos(File:LineNo):-loading_source_file(File),current_input(S),stream_property(S, position(Position)), !,stream_position_data(line_count, Position, LineNo),!.




%% compile_clause( ?CL) is det.
%
% Compile Clause.
%
compile_clause(CL):- quietly_must((make_dynamic(CL),assertz_if_new(CL),!,clause_asserted(CL))).




%% make_dynamic( ?C) is det.
%
% Make Dynamic.
%
make_dynamic((H:-_)):- sanity(nonvar(H)),!,must(make_dynamic(H)).
make_dynamic(M:(H:-_)):- sanity(nonvar(H)),!,must(make_dynamic(M:H)).
make_dynamic(C):- loop_check(make_dynamic_ilc(C),trace_or_throw_ex(looped_make_dynamic(C))).

make_dynamic_ilc(baseKB:C):- predicate_property(baseKB:C, dynamic),!.
% make_dynamic_ilc(C):- predicate_property(C, dynamic).
make_dynamic_ilc(C):- % trace_or_throw_ex(make_dynamic_ilc(C)),
   compound(C),strip_module(C,MIn,_),get_functor(C,F,A),quietly_must(F\=='$VAR'),
  (\+ a(mtHybrid,MIn) -> must(defaultAssertMt(M)) ; MIn =M),
  functor(P,F,A),

  ( \+predicate_property(M:P,_) -> kb_local(M:F/A) ; 
    (predicate_property(M:P,dynamic)->true;dynamic_safe(M:P))),!,
  kb_local(M:F/A),
  quietly_must((predicate_property(M:P,dynamic))).

% once(baseKB:pfc_is_impl_file(F);asserta(baseKB:pfc_is_impl_file(F))).

%user:goal_expansion(G,OUT):- \+  t_l:disable_px, G\=isa(_,_),(use_was_isa(G,I,C)),!,to_isa_form(I,C,OUT).
%user:term_expansion(G,OUT):- \+  t_l:disable_px, quietly(use_was_isa(G,I,C)),!,to_isa_form(I,C,OUT).
%user:term_expansion(I,O):- \+ t_l:disable_px, t_l:consulting_sources, locally_hide(t_l:consulting_sources,ain(I)),O=true.



% :-set_prolog_flag(allow_variable_name_as_functor,true).

% :- source_location(S,_),forall(loading_source_file(H,S),ignore(( \+predicate_property(M:H,built_in), functor(H,F,A),M:module_transparent(F/A),M:export(F/A)))).



%:- user:use_module(library(shlib)).
%:- user:use_module(library(operators)).

:- source_location(F,_),(set_how_virtualize_file(false,F)).

% filetypes 
%
%  pfc - all terms are sent to ain/1 (the the execeptions previously defined)
%  pl - all terms are sent to compile_clause/1 (the the execeptions previously defined)
%  prolog - all terms are sent to compile_clause/1 (even ones defined conflictingly)
%  dyn - all terms are sent to ain/1 (even ones defined conflictingly)

:- thread_local(t_l:pretend_loading_file/1).


:- dynamic(baseKB:never_reload_file/1).




%% load_language_file( ?Name0) is det.
%
% Load Language File.
%
load_language_file(Name0):- 
 forall(filematch_ext('qlf',Name0,Name),
  once((dmsg_pretty(load_language_file(Name0->Name)),
   locally([set_prolog_flag(subclause_expansion,false),
         set_prolog_flag(read_attvars,false),
         (t_l:disable_px),
         (user:term_expansion(_,_):-!,fail),
         (user:term_expansion(_,_,_,_):-!,fail),
         (user:goal_expansion(_,_):-!,fail),
         (user:goal_expansion(_,_,_,_):-!,fail),
         (system:term_expansion(_,_):-!,fail),
         (system:term_expansion(_,_,_,_):-!,fail),
         (system:goal_expansion(_,_,_,_):-!,fail),
         (system:goal_expansion(_,_):-!,fail)],
     gripe_time(1,(baseKB:load_files([Name],[qcompile(part),if(not_loaded)])))
       ->asserta(baseKB:never_reload_file(Name));retract(baseKB:never_reload_file(Name)))))),!.
 


%% disable_mpreds_in_current_file is det.
%
% Disable Managed Predicates In Current File.
%
disable_mpreds_in_current_file:- loading_source_file(F),show_call(why,asserta((t_l:disable_px:-loading_source_file(F),!))).


:-  /**/ export(with_pfc_expansions/1).
:- meta_predicate(with_pfc_expansions(0)).



%% with_pfc_expansions( :Goal) is det.
%
% Using Managed Predicate Expansions.
%
with_pfc_expansions(Goal):-
  locally_hide(tlbugger:no_buggery_tl,
    locally_hide(t_l:disable_px,Goal)).

:-  /**/ export(ensure_loaded_no_mpreds/1).
:- meta_predicate(ensure_loaded_no_mpreds(:)).



%% ensure_loaded_no_mpreds( :GoalF) is det.
%
% Ensure Loaded No Managed Predicates.
%
ensure_loaded_no_mpreds(M:F):- 
  with_delayed_chaining(forall(must_locate_file(F,L),((set_how_virtualize_file(false,L)),M:ensure_loaded(M:L)))).

:- meta_predicate(with_delayed_chaining(:)).
%% with_delayed_chaining( :Goal) is det.
%
% Using No Managed Predicate Expansions.
%
with_delayed_chaining(Goal):-
  locally(tlbugger:no_buggery_tl,
    locally(t_l:disable_px,Goal)).
:- export(with_delayed_chaining/1).
:- system:import(with_delayed_chaining/1).



%% use_was_isa( ?G, ?I, ?C) is det.
%
% use was  (isa/2).
%
use_was_isa(G,I,C):-call((current_predicate(_,_:pfc_types_loaded/0),if_defined(was_isa(G,I,C)))).




%% current_context_module( ?Ctx) is det.
%
% Current Context Module.
%
current_context_module(Ctx):-quietly((loading_module(Ctx))),!.
current_context_module(Ctx):-quietly((source_context_module(Ctx))).

% ========================================
% register_module_type/end_module_type
% ========================================
%:- was_module_transparent(baseKB:register_module_type/1).



%% register_module_type( ?Type) is det.
%
% Register Module Type.
%
register_module_type(Type):-current_context_module(CM),register_module_type(CM,Type).



%% register_module_type( ?CM, ?Types) is det.
%
% Register Module Type.
%
:- multifile(baseKB:registered_module_type/2).
register_module_type(CM,Types):-is_list(Types),!,forall(member(T,Types),register_module_type(CM,T)).
register_module_type(CM,Type):-asserta_new(baseKB:registered_module_type(CM,Type)).

:-  /**/ export(end_module_type/2).



%% end_module_type( ?Type) is det.
%
% End Module Type.
%
end_module_type(Type):-current_context_module(CM),end_module_type(CM,Type).



%% end_module_type( ?CM, ?Type) is det.
%
% End Module Type.
%
end_module_type(CM,Type):-retractall(baseKB:registered_module_type(CM,Type)).



:-  export(declare_load_dbase/1).



%% declare_load_dbase( ?Spec) is det.
%
% Declare Load Dbase.
%
declare_load_dbase(Spec):- forall(no_repeats(File,must_locate_file(Spec,File)),
  show_call(why,(set_how_virtualize_file(heads,File)))).

% :-  /**/ export((is_compiling_sourcecode/1)).



%% is_compiling_sourcecode is det.
%
% If Is A Compiling Sourcecode.
%
is_compiling_sourcecode:-is_compiling,!.
is_compiling_sourcecode:-compiling, current_input(X),not((stream_property(X,file_no(0)))),prolog_load_context(source,F),\+((t_l:loading_mpred_file(_,_))),F=user,!.
is_compiling_sourcecode:-compiling,dmsg_pretty(system_compiling),!.

:-  /**/ export(load_mpred_files/0).



%% load_mpred_files is det.
%
% Load Managed Predicate Files.
%
load_mpred_files :- 
   forall((baseKB:how_virtualize_file(Heads,File,_),false\==Heads,bodies\==Heads), 
     baseKB:ensure_mpred_file_loaded(File)).


% =======================================================
:- meta_predicate show_load_call(0).
show_load_call(C):- must(on_x_debug(show_call(why,C))).



:- dynamic(baseKB:loaded_file_world_time/3).
:- meta_predicate(baseKB:loaded_file_world_time(+,+,+)).
:- meta_predicate(get_last_time_file(+,+,+)).



%% get_last_time_file( +FileIn, +World, +LastTime) is det.
%
% Get Last Time File.
%
get_last_time_file(FileIn,World,LastTime):- absolute_file_name(FileIn,File),FileIn\==File,!,get_last_time_file(File,World,LastTime).
get_last_time_file(File,World,LastTime):- baseKB:loaded_file_world_time(File,World,LastTime),!.
get_last_time_file(File,_, LoadTime):- source_file_property(File, modified(LoadTime)).
get_last_time_file(_,_,0.0).

:- meta_predicate(load_init_world(+,:)).



%% load_init_world( +World, ?File) is det.
%
% Load Init World.
%
load_init_world(World,File):- 
 locally_hide(baseKB:use_cyc_database,
    ( world_clear(World),
      retractall(baseKB:loaded_file_world_time(_,_,_)),
      time_call(ensure_mpred_file_loaded(File)),!,
      time_call(finish_processing_world))).


:- meta_predicate(ensure_mpred_file_loaded(:)).



/******

% :- meta_predicate(ensure_mpred_file_loaded(:)). 

:- meta_predicate ensure_mpred_file_loaded(:,+).


ensure_mpred_file_loaded(M:F0,List):-!,
  must_locate_file(M:F0,F),  % scope_settings  expand(true),register(false),
  % 'format'(user_error ,'%  ~q + ~q -> ~q.~n',[M,F0,F]),
  load_files([F],[if(not_loaded), must_be_module(true)|List]).
   %load_files(F,[redefine_module(false),if(not_loaded),silent(false),exported(true),must_be_module(true)|List]).   
ensure_mpred_file_loaded(M:F0,List):-
  must_locate_file(M:F0,F),  % scope_settings
  'format'(user_error ,'% load_mpred_file_M ~q.~n',[M=must_locate_file(F0,F)]),
   load_files([F],[redefine_module(false),module(M),expand(true),if(not_loaded),exported(true),register(false),silent(false),must_be_module(true)|List]).

******/

%% ensure_mpred_file_loaded( ?MFileIn) is det.
%
% Ensure Managed Predicate File Loaded.
%
:- meta_predicate(ensure_mpred_file_loaded(:)).

% ensure_mpred_file_loaded(MFileIn):- baseKB:ensure_loaded(MFileIn),!.
ensure_mpred_file_loaded(MFileIn):- strip_module(MFileIn,M,_),
 forall((must_locate_file(MFileIn,File),
   needs_load_or_reload_file(File)),   
   (set_how_virtualize_file(heads,File),
      force_reload_mpred_file(M:File))).

needs_load_or_reload_file(File) :- \+ source_file_property(File, _),!.
needs_load_or_reload_file(File) :-
    source_file_property(Source, modified(Time)),
    \+ source_file_property(Source, included_in(_,_)),
    Time > 0.0,                     % See source_file/1
    (   source_file_property(Source, derived_from(File, LoadTime))
    ->  true
    ;   File = Source,
        LoadTime = Time
    ),
    (   catch(time_file(File, Modified), _, fail),
        Modified - LoadTime > 0.001             % (*)
    ->  true
    ;   source_file_property(Source, includes(Included, IncLoadTime)),
        catch(time_file(Included, Modified), _, fail),
        Modified - IncLoadTime > 0.001          % (*)
    ->  true
    ).

old_pfc_ensure_loaded(M,File):-
   must_det_l((set_how_virtualize_file(heads,File),time_file(File,FileTime),!,
   get_last_time_file(File,_World,LastLoadTime),
   (FileTime \== LastLoadTime -> force_reload_mpred_file(M:File); M:ensure_loaded(File)))).

:- meta_predicate(force_reload_mpred_file(?)).

:- meta_predicate(ensure_mpred_file_loaded(+,:)).



%% ensure_mpred_file_loaded( +World, ?FileIn) is det.
%
% Ensure Managed Predicate File Loaded.
%
ensure_mpred_file_loaded(World,FileIn):- 
  with_umt(World,ensure_mpred_file_loaded(FileIn)).




%% must_locate_file( ?FileIn, ?File) is det.
%
% Must Be Successfull Locate File.
%
must_locate_file(FileIn,File):- must(maybe_locate_file(FileIn,File)).

maybe_locate_file(FileIn,File):- 
 no_repeats(File, quietly(filematch_ext(['','mpred','ocl','moo','plmoo','pl','plt','pro','p','pl.in','pfc','pfct'],FileIn,File))).







%% force_reload_mpred_file( ?FileIn) is det.
%
% Force Reload Managed Predicate File.
%
force_reload_mpred_file(MFileIn):- 
 strip_module(MFileIn,M,FileIn),
 (FileIn==MFileIn->defaultAssertMt(World);World=M),
  quietly_must(force_reload_mpred_file(World,FileIn)).




%% force_reload_mpred_file( ?World, ?MFileIn) is det.
%
% Force Reload Managed Predicate File.
%

%force_reload_mpred_file(World,MFileIn):- must(World:consult(MFileIn)),!.
force_reload_mpred_file(World,MFileIn):- 
 without_varname_scan(force_reload_mpred_file2(World,MFileIn)).

%% force_reload_mpred_file2( ?World, ?MFileIn) is det.
%
% Helper for Force Reloading of a Managed Predicate File.
%

force_reload_mpred_file2(World,MFileIn):-
  time_file(MFileIn,NewTime),
  system:retractall(baseKB:loaded_file_world_time(MFileIn,World,_)),
  system:assert(baseKB:loaded_file_world_time(MFileIn,World,NewTime)),
  must(World:consult(MFileIn)),!.

force_reload_mpred_file2(WorldIn,MFileIn):- 
 sanity(call_u(baseKB:mtHybrid(WorldIn))),
 must(call_u(baseKB:mtHybrid(WorldIn)->World=WorldIn;defaultAssertMt(World))),
 strip_module(MFileIn,_MaybeNewModule,_),
 NewModule = World,
 with_source_module(NewModule,((
 % NewModule:ensure_loaded(logicmoo(mpred/pfc_userkb)),
 forall(must_locate_file(MFileIn,File),
   must_det_l((
   sanity(\+ check_how_virtualize_file(false,File) ),
   once(show_success(prolog_load_file,defaultAssertMt(DBASE));DBASE=NewModule),
   sanity(exists_file(File)),
   sanity((true,defaultAssertMt(World))),
   nop(pfc_remove_file_support(File)),
   (set_how_virtualize_file(heads,File)),
   quietly_must(time_file(File,NewTime)),
   retractall(baseKB:loaded_file_world_time(File,World,_)),
   system:assert(baseKB:loaded_file_world_time(File,World,NewTime)),    DBASE = DBASE,
   locally_hide(t_l:disable_px,
     locally(set_prolog_flag(subclause_expansion,true),
      locally(set_prolog_flag(pfc_te,true),
     show_call((with_source_module(NewModule,load_files(NewModule:File, [module(NewModule)]))))))),
         must(force_reload_mpred_file3(File,World))
     )))))).

force_reload_mpred_file3(File,World):-
   catch((locally(t_l:loading_mpred_file(World,File),     
      load_pfc_on_file_end(World,File))),
    Error,
    (dmsg_pretty(error(Error,File)),retractall(baseKB:loaded_mpred_file(World,File)),
     retractall(baseKB:loaded_file_world_time(File,World,_AnyTime)))).


:- dynamic(baseKB:loaded_mpred_file/2).

%% load_pfc_on_file_end( ?World, ?File) is det.
%
% Load Managed Predicate Whenever File End.
%
:- export(load_pfc_on_file_end/2).
load_pfc_on_file_end(World,File):- 
   sanity(atom(File)),   
   asserta_new(baseKB:loaded_mpred_file(World,File)),
   must(signal_eof(File)),!.


%% finish_processing_world is det.
%
% Finish Processing World.
%
finish_processing_world :- 
  load_mpred_files, 
  loop_check(locally(t_l:agenda_slow_op_do_prereqs,doall(finish_processing_dbase)),true).




%% loader_side_effect_verify_only( ?I, ?Supposed) is det.
%
% Loader Side Effect Verify Only.
%
loader_side_effect_verify_only(I,Supposed):-   
   sanity(var(Supposed)),
    push_predicates(t_l:side_effect_buffer/3,STATE),
    prolog_load_context(module,M),
    pfc_expander_now_physically(M,I,Supposed),
    get_source_ref1(Why),
    collect_expansions(Why,I,Actual),
    convert_side_effect(suppose(Supposed),S),
    conjoin(S, Actual,ActualSupposed),
    conjuncts_to_list(ActualSupposed,Readable),
    system:assert(t_l:actual_side_effect(I,Readable)),
    pop_predicates(t_l:side_effect_buffer/3,STATE),!.




%% loader_side_effect_capture_only( ?I, ?ActualSupposed) is det.
%
% Loader Side Effect Capture Only.
%
loader_side_effect_capture_only(I,ActualSupposed):-   
   sanity(var(ActualSupposed)),
    push_predicates(t_l:side_effect_buffer/3,STATE),
    prolog_load_context(module,M),
    pfc_expander_now_physically(M,I,Supposed),
    get_source_ref1(Why),
    collect_expansions(Why,I,Actual),
    conjoin(Actual,Supposed,ActualSupposed),
    pop_predicates(t_l:side_effect_buffer/3,STATE),!.


with_assert_buffer(G,List):-
      sanity(var(List)),
      push_predicates(t_l:side_effect_buffer/3,STATE),
      locally(t_l:use_side_effect_buffer,(call_u(G),pfc_run)),
      findall(Tell,(retract(t_l:side_effect_buffer(OP, Data, _Why)),convert_as_tell(OP,Data,Tell)),List),
      pop_predicates(t_l:side_effect_buffer/3,STATE),!.

convert_as_tell(_P,Data,_Tell):- must_be(nonvar,Data),fail.
convert_as_tell(OP,M:Data,Tell):-M==baseKB,!,convert_as_tell(OP,Data,Tell).
convert_as_tell(OP,Data,Tell):- is_assert_op(OP),!,Tell=Data.
convert_as_tell(OP,Data,call(OP,Data)).

is_assert_op(OP):-must_be(callable,OP),fail.
is_assert_op(call(OP,_)):-!,is_assert_op(OP),!.
is_assert_op(db_op_call(OP,_)):-!,is_assert_op(OP),!.
is_assert_op(asserta).
is_assert_op(assertz).
is_assert_op(assert).


%% collect_expansions( ?Why, ?I, ?I) is det.
%
% Collect Expansions.
%
collect_expansions(_Why,I,I):- \+ t_l:side_effect_buffer(_Op,_Data,_),!.
collect_expansions(NWhy,_I, TODO):- findall(ReproduceSWhy, 
  ( retract(t_l:side_effect_buffer(Op, Data, Why)),
    must_det_l(convert_side_effect(Op, Data,Reproduce)),
    quietly_must(simplify_why_r(Reproduce,Why,NWhy,ReproduceSWhy))), TODOs),
   must_det_l( list_to_conjuncts(TODOs,TODO)).




%% simplify_why_r( ?Reproduce, ?Why, ?NWhy, :TermReproduce) is det.
%
% Simplify Generation Of Proof R.
%
simplify_why_r(Reproduce,Why,NWhy,   Reproduce):- Why==NWhy, !.
simplify_why_r(Reproduce,Why,_,Reproduce:SWhy):-simplify_why(Why,SWhy),!.
 
% aliases
:- meta_predicate(convert_side_effect(?,+,-)).




%% simplify_why( ?Why, ?SWhy) is det.
%
% Simplify Generation Of Proof.
%
simplify_why(Why,SWhy):-var(Why),!,Why=SWhy.
simplify_why(Why:0,SWhy):-!,simplify_why(Why,SWhy).
simplify_why(Why:N,SWhy:N):-!,simplify_why(Why,SWhy).
simplify_why(Why,SWhy):- atom(Why),!,directory_file_path(_,SWhy,Why).
simplify_why(Why,Why).




%% convert_side_effect( ?C, +A, -SE) is det.
%
% Convert Side Effect.
%
convert_side_effect(M:C,A,SE):- Call=..[C,A],!,convert_side_effect(M:Call,SE).
convert_side_effect(C,A,SE):- Call=..[C,A],!,convert_side_effect(Call,SE).




%% convert_side_effect( ?I, ?OO) is det.
%
% Convert Side Effect.
%
convert_side_effect(suppose(OO), suppose(Result)):- convert_side_effect_0a(OO,Result),!.
convert_side_effect(I,OO):-convert_side_effect_0c(I,O),((O=(N-_V),number(N))->OO=O;OO=O),!.




%% convert_side_effect_0a( ?I, ?O) is det.
%
% Convert Side Effect 0a.
%
convert_side_effect_0a(asserta(Data), (  a(DataR))):-convert_side_effect_0a(Data,DataR).
convert_side_effect_0a(assertz(Data), (  z(DataR))):-convert_side_effect_0a(Data,DataR).
convert_side_effect_0a(retract(Data), (  r(DataR))):-convert_side_effect_0a(Data,DataR).
convert_side_effect_0a(cl_assert(Why,Data), (  cl_assert(Why,DataR))):-convert_side_effect_0a(Data,DataR).
convert_side_effect_0a(attvar_op(How,Data),Reproduce):-!,convert_side_effect(How,Data,Reproduce),!.
convert_side_effect_0a(I,O):-convert_side_effect_0b(I,O),!.
convert_side_effect_0a(I,I).




%% convert_side_effect_0b( :TermOpData, ?Result) is det.
%
% Convert Side Effect 0b.
%
convert_side_effect_0b((OpData:-TRUE),Result):- is_true(TRUE),!,convert_side_effect_0a(OpData,Result),!.
convert_side_effect_0b(suppose(OpData),Result):-!,convert_side_effect_0a(OpData,Result),!.
convert_side_effect_0b(baseKB:OpData,Reproduce):- !,convert_side_effect_0a(OpData,Reproduce),!.
convert_side_effect_0b(( :- OpData),( ( (Result)))):-!,convert_side_effect_0a(OpData,Result),!.
convert_side_effect_0b('$si$':'$was_imported_kb_content$'(_, OO),Result):-!,convert_side_effect_0a(OO,Result),!.
convert_side_effect_0b(asserta_if_new(Data),Result):-!,convert_side_effect_0a(asserta(Data),Result).
convert_side_effect_0b(assertz_if_new(Data),Result):-!,convert_side_effect_0a(assertz(Data),Result).
convert_side_effect_0b(assert_if_new(Data),Result):-!,convert_side_effect_0a(assertz(Data),Result).
convert_side_effect_0b(assert(Data),Result):-!,convert_side_effect_0a(assertz(Data),Result).


% unused_assertion('$was_imported_kb_content$'([], A)):-atom(A).


%% convert_side_effect_0c( ?OpData, ?Reproduce) is det.
%
% Convert Side Effect 0c.
%
convert_side_effect_0c(OpData,Reproduce):- convert_side_effect_0b(OpData,Reproduce),!.
convert_side_effect_0c(OpData,Reproduce):- show_success(convert_side_effect,convert_side_effect_buggy(OpData,Reproduce)),!.
convert_side_effect_0c(OpData,Reproduce):- trace_or_throw_ex(unknown_convert_side_effect(OpData,Reproduce)),!.

% todo



%% convert_side_effect_buggy( ?H, ?HB) is det.
%
% Convert Side Effect Buggy.
%
convert_side_effect_buggy(erase(clause(H,B,_Ref)), (e(HB))):- convert_side_effect_0a((H:-B),HB).
convert_side_effect_buggy(retract(Data), (r(DataR))):-convert_side_effect_0a(Data,DataR).
convert_side_effect_buggy(retractall(Data), (c(DataR))):-convert_side_effect_0a(Data,DataR).
convert_side_effect_buggy(OpData,( (  error_op(OpData)))):-dmsg_pretty(unknown_convert_side_effect(OpData)).





%% clear_predicates( :TermM) is det.
%
% Clear Predicates.
%
clear_predicates(M:H):- forall(M:clause(H,_,Ref),erase(Ref)).



%% push_predicates( :TermM, ?STATE) is det.
%
% Push Predicates.
%
push_predicates(M:F/A,STATE):- functor(H,F,A),findall((H:-B), (M:clause(H,B,Ref),erase(Ref)), STATE).



%% pop_predicates( :TermM, ?STATE) is det.
%
% Pop Predicates.
%
pop_predicates(M:F/A,STATE):- functor(H,F,A),forall(member((H:-B),STATE),M:assert((H:-B))).




:- fixup_exports.

pfc_loader_file.

%system:term_expansion(end_of_file,_):-must(check_clause_counts),fail.
%system:term_expansion(EOF,_):-end_of_file==EOF,must(check_clause_counts),fail.



/* 
% ===================================================================
% File 'pfc_db_preds.pl'
% Purpose: Emulation of OpenCyc for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface.pl' 1.0.0
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

:- module(pfc_prolog_file,[
            guess_file_type_loader/2,
            prolog_load_file_loop_checked/2,
            prolog_load_file_loop_checked_0/2, 
            prolog_load_file_nlc/2,
            prolog_load_file_nlc_0/2,
            load_file_dir/2,
            load_file_some_type/2,
            use_file_type_loader/2,
            never_load_special/2
          ]).

:- include('pfc_header.pi').

:- multifile(user:prolog_load_file/2).
:- dynamic(user:prolog_load_file/2).
% :- '$set_source_module'(system).






%% never_load_special( :TermARG1, ?Options) is semidet.
%
% Never Load Special.
%


never_load_special(_, [if(not_loaded)]):-!.
never_load_special(_:library(make), [if(not_loaded)]):-!.
% never_load_special(Module:Spec, Options) :- with_dmsg_to_main((dmsg_pretty(check_load(Module:Spec,Options)))),fail.
never_load_special(_, Options) :- memberchk(must_be_module(true),Options),!.
never_load_special(_, Options) :- memberchk(autoload(true),Options),!.
never_load_special(_Module:_Spec, Options) :- memberchk(if(not_loaded),Options),memberchk(imports([_/_]),Options),!.   


% :- use_module(library(logicmoo/util/logicmoo_util_filesystem)).
:- dynamic(prolog_load_file_loop_checked/2).
:- export(prolog_load_file_loop_checked/2).

% probably an autoload (SKIP)



%% prolog_load_file_loop_checked( ?ModuleSpec, ?Options) is semidet.
%
% Prolog Load File Loop Checked.
%

prolog_load_file_loop_checked(ModuleSpec, Options) :- 
  filematch(ModuleSpec,F),
  system:'$load_context_module'(F, Was, _),
  strip_module(ModuleSpec,To,File),
  To\==Was,
  Was==user,
  wdmsg_pretty(warn(loading_into_wrong_module(Was:File->To:File,Options))),!,
  loop_check(load_files(Was:File,Options)),!.
prolog_load_file_loop_checked(ModuleSpec, Options) :- never_load_special(ModuleSpec, Options),!,fail.
prolog_load_file_loop_checked(ModuleSpec, Options) :- 
  loop_check(show_success(prolog_load_file,prolog_load_file_loop_checked_0(ModuleSpec, Options))).




%% prolog_load_file_loop_checked_0( ?ModuleSpec, ?Options) is semidet.
%
% prolog load file loop checked  Primary Helper.
%
prolog_load_file_loop_checked_0(ModuleSpec, Options) :- current_predicate(_,_:exists_file_safe(_)),
   catch(prolog_load_file_nlc_pre(ModuleSpec, Options),E,(nop((dtrace,prolog_load_file_nlc(ModuleSpec, Options))),throw(E))).


prolog_load_file_nlc_pre(Module:Spec, Options) :- 
  call_from_module(Module,prolog_load_file_nlc(Module:Spec, Options)).

%% prolog_load_file_nlc( :TermModule, ?Options) is semidet.
%
% Prolog Load File Nlc.
%
% :- export(prolog_load_file_nlc/2).
prolog_load_file_nlc(Module:Spec, Options) :- 
   filematch(Module:Spec,Where1),Where1\=Spec,!,forall(filematch(Module:Spec,Where),Module:load_files(Module:Where,Options)).

prolog_load_file_nlc(Module:Spec, Options):- baseKB:never_reload_file(Spec),
   wdmsg_pretty(warn(error(skip_prolog_load_file_nlc(baseKB:never_reload_file(Module:Spec, Options))))),!.

prolog_load_file_nlc(Module:Spec, Options):- thread_self(TID), \+ thread_self_main,
   nop(wdmsg_pretty(warn(error(skip_prolog_load_file_nlc(wrong_thread(TID):-thread(Module:Spec, Options)))))),!.

prolog_load_file_nlc(Module:Spec, Options):- thread_self(TID), \+ thread_self_main,
   nop(wdmsg_pretty(warn(error(skip_prolog_load_file_nlc(wrong_thread(TID):-thread(Module:Spec, Options)))))),!,fail,dumpST.

prolog_load_file_nlc(Module:DirName, Options):-  atom(DirName), is_directory(DirName)->
  current_predicate(_,_:'load_file_dir'/2)->loop_check(show_call(why,call(load_file_dir,Module:DirName, Options))).

prolog_load_file_nlc(Module:Spec, Options):- absolute_file_name(Spec,AFN,[extensions(['pl'])]), 
   (Spec\==AFN),exists_file_safe(AFN),!,prolog_load_file_nlc(Module:AFN, Options).

prolog_load_file_nlc(Module:FileName, Options):- exists_file_safe(FileName),!,
   prolog_load_file_nlc_0(Module:FileName, Options).

prolog_load_file_nlc(Module:Spec, Options):- term_to_atom(Spec,String),member(S,['?','*']),sub_atom(String,_,1,_,S),!, 
 foreach(baseKB:filematch(Module:Spec,FileName),
    (loop_check((prolog_load_file_nlc_0(Module:FileName, Options))),TF=true)),!,
  nonvar(TF).


%% prolog_load_file_nlc_0( :TermModule, ?Options) is semidet.
%
% prolog load file nlc  Primary Helper.
%
prolog_load_file_nlc_0(Module:Spec, Options):- thread_self(TID), \+ thread_self_main,
   wdmsg_pretty(warn(error(skip_prolog_load_file_nlc(wrong_thread(TID):-thread(Module:Spec, Options))))),!.

prolog_load_file_nlc_0(Module:FileName, Options):- 
  '$set_source_module'(SM,SM),
 (source_file_property(FileName,load_context(MC,SubFile:Line)),MC\==user,SM==user),!,
  wdmsg_pretty(skipping(prolog_load_file_nlc(Module:FileName, Options):source_file_property(FileName,load_context(MC,SubFile:Line)))),!.

prolog_load_file_nlc_0(Module:FileName, Options):-  
  file_name_extension(_Base,Ext,FileName),
  use_file_type_loader(Ext,Loader)-> loop_check(call(Loader,Module:FileName, Options)).

prolog_load_file_nlc_0(Module:FileName, Options):- fail, fail, fail, fail, fail, fail, fail, fail, fail, fail, fail, fail, 
  file_name_extension(_Base,Ext,FileName),
  guess_file_type_loader(Ext,Loader)-> loop_check(call(Loader,Module:FileName, Options)).



%% guess_file_type_loader( ?Ext, ?Loader) is semidet.
%
% Guess File Type Loader.
%
guess_file_type_loader(Ext,Loader):-use_file_type_loader(Ext,Loader).
guess_file_type_loader(Ext,Pred):- atom(Ext),
   (Ext==''->Pred='load_file_some_type';system:atom_concat('load_file_type_,',Ext,Pred)),
   current_predicate(Pred/2).




%% load_file_dir( :TermModule, ?Options) is semidet.
%
% Load File Dir.
%
load_file_dir(Module:DirName, Options):- fail,
  directory_files(DirName,Files),
  foreach((member(F,Files),
            file_name_extension(_,Ext,F),
            guess_file_type_loader(Ext,Loader),
            current_predicate(_,_:Loader/2),
            directory_file_path(DirName,F,FileName)),
      (user:prolog_load_file(Module:FileName, Options),TF=true)),
     nonvar(TF).





%% use_file_type_loader( ?VALUE1, ?VALUE2) is semidet.
%
% Use File Type Loader.
%
use_file_type_loader(pfc,ensure_mpred_file_consulted).
use_file_type_loader(pddl,ensure_mpred_file_consulted).
use_file_type_loader(plmoo,ensure_mpred_file_consulted).
% use_file_type_loader(pl,ensure_prolog_file_consulted).




%% ensure_prolog_file_consulted( :TermM, ?Options) is semidet.
%
% Ensure Prolog File Consulted.
%
ensure_prolog_file_consulted(M:File,Options):-must(load_files(M:File,Options)),!.




%% ensure_mpred_file_consulted( :TermM, ?Options) is semidet.
%
% Ensure Managed Predicate File Consulted.
%
ensure_mpred_file_consulted(M:File,Options):- 
 call_from_module(M,
  with_pfc_expansions(locally_tl(pretend_loading_file(File),
              must((file_begin(pfc),
                    load_files(M:File,Options)))))),!.




%% load_file_some_type( :TermM, ?Options) is semidet.
%
% Load File Some Type.
%
load_file_some_type(M:File,Options):- call_from_module(M,must(load_files(M:File,Options))),!.



:- multifile(user:prolog_load_file/2).
:- dynamic(user:prolog_load_file/2).


%% prolog_load_file( ?ModuleSpec, ?Options) is semidet.
%
% Hook To [user:prolog_load_file/2] For Module Mpred_loader.
% Prolog Load File.
%

maybe_load_mpred_files(Module:Spec, Options):- 
   \+ exists_source(Spec),
   findall(SpecO,(logicmoo_util_filesystem:filematch(Module:Spec,SpecO),exists_file(SpecO)),SpecOList),!,
   SpecOList\==[], !, 
   forall(member(SpecO,SpecOList),load_files(Module:SpecO, Options)),!.


maybe_load_mpred_files(Module:Spec, Options):- fail,
  Spec \== 'MKINDEX.pl',
   catch(find_and_call(prolog_load_file_loop_checked(Module:Spec, Options)),
    E,
     ((wdmsg_pretty(E),dtrace,find_and_call(prolog_load_file_loop_checked(Module:Spec, Options)),throw(E)))),!.
%user:prolog_load_file(_,_):- get_lang(pl),!,fail.
%user:prolog_load_file(_,_):- set_file_lang(pl),set_lang(pl),fail.


:- fixup_exports.

:- module_transparent(user:prolog_load_file/1).

user:prolog_load_file(ModuleSpec, Options):- maybe_load_mpred_files(ModuleSpec, Options),!.


% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/mpred/pfc_terms.pl
%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(pfc_terms,
          [ 
          any_to_number/2,
          is_ftText/1,
          any_to_value/2,
          atom_to_value/2
          ]).

:- include('pfc_header.pi').

/** <module> pfc_terms
% Provides a common set of operators in translation between the several logical languages
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/


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
is_ftText(Arg):- safe_functor(Arg,s,_),!.
is_ftText([Arg|_]):-string(Arg),!.
is_ftText(Arg):- is_ftVar(Arg),!,fail.
is_ftText(Arg):- text_to_string_safe(Arg,_),!.
is_ftText(Arg):- safe_functor(Arg,S,_), ereq(resultIsa(S,ftText)).

:- kb_global(baseKB:ftText/1).
:-ain(baseKB:(ftText(A):- !, if_defined(term_is_ft(A, ftText),is_ftText(A)),!)).

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
% replace_arg(C,A,VAR,CO):- dupe_term(C,CC),setarg(A,CC,VAR),!,CC=CO.
replace_arg(C,A,VAR,CC):- C=..FARGS,replace_nth_arglist(FARGS,A,VAR,FARGO),!,CC=..FARGO.

% :- pfc_trace_nochilds(replace_arg/4).

%% replace_nth_arglist(+List, +Index, +Element, -NewList) is det[private]
% Replace the Nth (1-based) element of a list.
% :- pfc_trace_nochilds(replace_nth_arglist/4).



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


% :- pfc_trace_nochilds(update_value/3).



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

%% never_pfc_tcall( ?VALUE1) is semidet.
%
% Never Managed Predicate Managed Predicate.
%

never_pfc_tcall(pfc_prop).
never_pfc_tcall(isa).
never_pfc_tcall(arity).


local_qh_pfc_prop(M,F,A,C):- call_u(pfc_prop(M,F,A,C)).


% :- setup_pfc_ops.


                   
%= 	 	 

:- meta_predicate(if_result(0,0)).

%= 	 	 

%% if_result( :GoalTF, :Goal) is semidet.
%
% If Result.
%
if_result(TF,Call):-(TF->Call;true).




%= 	 	 

%% pfc_plist_t( ?P, :TermLIST) is semidet.
%
% Managed Predicate Plist True Stucture.
%
/* pfc_plist_t(P,[]):-!,t(P). */
pfc_plist_t(P,LIST):-var(P),!,is_list(LIST),CALL=..[t,P|LIST],on_x_debug((CALL)).
pfc_plist_t(t,[P|LIST]):-!, pfc_plist_t(P,LIST).
%pfc_plist_t(pfc_isa,[C,_A,I]):-!,ground(I:C),local_qh_pfc_isa(C,I).
pfc_plist_t(isa,[I,C]):-!,call(call,t,C,I).
pfc_plist_t(P,_):-never_pfc_tcall(P),!,fail.
pfc_plist_t(P,[L|IST]):-is_holds_true(P),!,pfc_plist_t(L,IST).
pfc_plist_t(P,LIST):-is_holds_false(P),!,call_u(mpred_f(LIST)).
pfc_plist_t(P,LIST):- CALL=..[t,P|LIST],on_x_debug(CALL).


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
mpred_fact_arity(F,A):- call_u(arity(F,A)),
  suggest_m(M),
  once(local_qh_pfc_prop(M,F,A,prologHybrid);
     local_qh_pfc_prop(M,F,A,pfcControlled);
     local_qh_pfc_prop(M,F,A,prologPTTP);
     local_qh_pfc_prop(M,F,A,prologKIF)),!.


%= 	 	 

%% prologHybridFact( ?G) is semidet.
%
% Prolog Hybrid Fact.
%
prologHybridFact(G):- (var(G)->(mpred_fact_arity(F,A),safe_functor(G,F,A));true),into_mpred_form(G,M),!,no_repeats(call_u(M)).



