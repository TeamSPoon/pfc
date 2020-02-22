/*
% ===================================================================
% File 'mpred_db_preds.pl'
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
%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
:- module(mpred_at_box,[
         assert_setting01/1,
         make_module_name_local/2,
         make_module_name_local0/2,
         (make_shared_multifile)/1,
         (make_shared_multifile)/3,
         (make_shared_multifile)/4,
         % (kb_global)/1,
         add_import_predicate/3,
         autoload_library_index/4,
         ensure_abox/1,
         baseKB_hybrid_support/2,
         correct_module/3,
         correct_module/5,
         defaultAssertMt/1,
         ensure_imports/1,

         set_fileAssertMt/1,
          setup_module_ops/1,

         in_mpred_kb_module/0,
         
         makeConstant/1,
         mtCanAssert/1,
         %registerCycPred/4,
         %registerCycPred/5,

         set_defaultAssertMt/1,
         set_fileAssertMt/1,
         transitive_path/3,
         which_file/1,
         user_m_check/1,

         add_abox_module/1,

         ensure_tbox/1,
          get_file_type_local/2,

         fixup_modules/0,
         import_predicate/2,
         skip_user/1,
         inherit_into_module/2,
         box_type/3,
         make_reachable/2,
         % clause_b/1,
         fixup_module/2,
         is_undefaulted/1,
         ensure_imports_tbox/2,
         map_inheritance/1,


         which_file/1
    ]).



%:- endif.
:- set_module(class(library)).

:- module_transparent((
     baseKB_hybrid_support/2,
         correct_module/3,
         correct_module/5,
         defaultAssertMt/1,
         ensure_imports/1,
         fileAssertMt/1,

         in_mpred_kb_module/0)).

:-dynamic(unused_predicate/4).

:- include('mpred_header.pi').
:- flag_call(runtime_debug=false).

:- set_how_virtualize_file(bodies).

user_m_check(_Out).

:- meta_predicate make_shared_multifile(+,+,+), mpred_op_each(3).
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
baseKB:mtNoPrologCode(mpred_userkb).

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
         in_mpred_kb_module/0,
         which_file/1,
         user_m_check/1 .


%% in_mpred_kb_module is semidet.
%
% In Managed Predicate Knowledge Base Module.
%
in_mpred_kb_module:- source_context_module(MT),defaultAssertMt(MT2),!,MT==MT2.


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
get_file_type_local(File,Type):-clause_b(lmcache:mpred_directive_value(File,language,Type)).


mtCanAssert(Module):- clause_b(mtNonAssertable(Module)),!,fail.
mtCanAssert(ABox):- \+ \+ (ABox=abox),!,trace_or_throw_ex(mtCanAssert(ABox)),fail.
mtCanAssert(Module):- clause_b(mtHybrid(Module)).
mtCanAssert(user):-  is_user_pfc.
% mtCanAssert(Module):- clause_b(mtExact(Module)).
mtCanAssert(Module):-  module_property(Module,file(_)),!,fail.
mtCanAssert(Module):- (loading_source_file(File),get_file_type_local(File,pfc),prolog_load_context(module,Module)).
mtCanAssert(Module):- clause_b(mtProlog(Module)),!,fail.
mtCanAssert(Module):- \+ mpred_core:is_code_module(Module),!.

is_user_pfc:- clause_b(mtHybrid(user)).



%% fileAssertMt(-ABox) is det.
%
% Gets ABox is an "assertion component" Prolog Module
% within a knowledge base.
%
% not just user modules

fileAssertMt(M):- nonvar(M), fileAssertMt(ABoxVar),!,M=@=ABoxVar.
fileAssertMt(M):- loading_source_file(File),clause_b(baseKB:file_to_module(File,M)),!.
fileAssertMt(M):- loading_source_file(File),clause_b(lmcache:mpred_directive_value(File,module,M)),!.
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
  assert_setting(lmcache:mpred_directive_value(File,module,M)),
  asserta_until_eof(t_l:current_defaultAssertMt(M)),!,
  ((pfc_lib:is_pfc_file) -> show_call(set_current_modules_until_eof(M)) ; true).


%:- import(pfc_lib:is_pfc_file/0).
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
get_fallBackAssertMt(M):- loading_source_file(File),clause_b(lmcache:mpred_directive_value(File,module,M)).
get_fallBackAssertMt(M):- guess_maybe_assertMt(M),clause_b(mtHybrid(M)),!.
get_fallBackAssertMt(M):- guess_maybe_assertMt(M),mtCanAssert(M),!.
get_fallBackAssertMt(M):- guess_maybe_assertMt(M).

guess_maybe_assertMt(M):- '$current_source_module'(M).
guess_maybe_assertMt(M):- context_module(M).
guess_maybe_assertMt(M):- loading_source_file(File),clause_b(baseKB:file_to_module(File,M)).
guess_maybe_assertMt(M):- loading_source_file(File),clause_b(lmcache:mpred_directive_value(File,module,M)).
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

is_pfc_module_file(M,F,TF):- (module_property(M,file(F)),pfc_lib:is_pfc_file(F)) *-> TF=true ; 
  (module_property(M,file(F))*->TF=false ; (F= (-), TF=false)).

maybe_ensure_abox(M):- is_pfc_module_file(M,F,_), (F \== (-)), !, 
  (pfc_lib:is_pfc_file(F)->show_call(pfc_lib:is_pfc_file(F),ensure_abox(M));dmsg_pretty(not_is_pfc_module_file(M,F))).
maybe_ensure_abox(M):- show_call(not_is_pfc_file,ensure_abox(M)).


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
  must(forall(mpred_database_term(F,A,_Type),
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


   

setup_module_ops(M):- mpred_op_each(mpred_op_unless(M)).

mpred_op_unless(M,A,B,C):- op_safe(A,B,M:C).

mpred_op_each(OpEach):-
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
%baseKB:mtGlobal(mpred_loader).

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
system:call_expansion(T,(mpred_at_box:defaultAssertMt(NewVar),NewT)):- current_predicate(_,get_lang(pfc)), compound(T),
   subst(T,abox,NewVar,NewT),NewT\=@=T.

system:body_expansion(T,(mpred_at_box:defaultAssertMt(NewVar),NewT)):- current_predicate(_,get_lang(pfc)), compound(T),
   subst(T,abox,NewVar,NewT),NewT\=@=T.
*/


:- fixup_exports.

