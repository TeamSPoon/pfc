/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
%:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )). 
:- module(logicmoo_base_file,[]).
:- '$set_source_module'(baseKB).
%:- endif.
:- load_files(library(prolog_stack), [silent(true)]).
%prolog_stack:stack_guard(none).

:- multifile(baseKB:'already_decl_kb_shared'/3).
:- dynamic(baseKB:'already_decl_kb_shared'/3).

:- multifile(system:goal_expansion/4).
:- dynamic(system:goal_expansion/4).
:- multifile(system:term_expansion/4).
:- dynamic(system:term_expansion/4).

:- thread_local(t_l:disable_px).

:- kb_shared(arity/2).
:- kb_shared(functorDeclares/1).
:- kb_shared(genlMt/2).

:- kb_shared(genls/2).
:- kb_shared(ttStringType/1).
:- kb_shared(mpred_f/2).
:- kb_shared(mpred_f/3).
:- kb_shared(ttExpressionType/1).
:- kb_shared(tCol/1).
:- kb_shared(tSet/1).
:- kb_shared(mtCore/1).
:- kb_shared(mtCycL/1).
:- kb_shared(mtExact/1).
:- kb_shared(mtGlobal/1).
:- kb_shared(mtProlog/1).
:- kb_shared(mtExact/1).
:- kb_shared(tCol/1).


:- kb_shared((
 rtQuotedPred/1,
   argIsa/3,
   bt/2, %basePFC
   hs/1, %basePFC
   hs/1, %basePFC
   nt/3, %basePFC
   pk/3, %basePFC
   pt/2, %basePFC
   que/1, %basePFC
   pm/1, %basePFC
   spft/3, %basePFC
   tms/1, %basePFC
   prologSingleValued/1)).

:- baseKB:ensure_loaded(library(logicmoo_utils)).
:- if( \+ current_predicate(system:each_call_cleanup/3)).
:- ensure_loaded(system:library(each_call_cleanup)).
:- endif.

% Kill YALL
:- ensure_loaded(system:library(yall)).
:- locally(set_prolog_flag(access_level,system),
   doall(( source_file(yall:lambda_functor(_),O),source_file(M:X,O),M\==yall,
   clause(M:X,_,Ref),clause_property(Ref,file(O)),on_x_fail(erase(Ref))))).

:- locally(set_prolog_flag(access_level,system),
   doall(( source_file(yall:lambda_functor(_),O),source_file(M:X,O),M\==yall,
   clause(M:X,B,Ref),clause_property(Ref,file(O)),wdmsg((M:X :- B)),on_x_fail(erase(Ref))))).

:- abolish(yall:lambda_functor,1),dynamic(yall:lambda_functor/1).
:- abolish(yall:lambda_like,1),dynamic(yall:lambda_like/1).

/*
% baseKB:startup_option(datalog,sanity). %  Run datalog sanity tests while starting
% baseKB:startup_option(clif,sanity). %  Run datalog sanity tests while starting
:- set_prolog_flag(fileerrors,false).
:- set_prolog_flag(access_level,system).
:- set_prolog_flag(gc,false).
:- set_prolog_flag(gc,true).
:- set_prolog_flag(optimise,false).
:- set_prolog_flag(last_call_optimisation,false).
:- set_prolog_flag(debug,true).
:- debug.
:- Six = 6, set_prolog_stack(global, limit(Six*10**9)),set_prolog_stack(local, limit(Six*10**9)),set_prolog_stack(trail, limit(Six*10**9)).
*/
:- set_prolog_flag(verbose_load,true).
%:- set_prolog_flag(verbose_autoload, true).
:- set_prolog_flag(debug_on_error,true).
:- set_prolog_flag(report_error,true).
%:- guitracer.
%:- set_prolog_flag(access_level,system).

% :- set_prolog_flag(logicmoo_autoload,false).
:- set_prolog_flag(logicmoo_autoload,true).


% must be xref-ing or logicmoo_autoload or used as include file
:- set_prolog_flag(logicmoo_include,lmbase:skip_module_decl).
% lmbase:skip_module_decl:- source_location(F,L),wdmsg(lmbase:skip_module_decl(F:L)),!,fail.
lmbase:skip_module_decl:-!,fail.
lmbase:skip_module_decl:-
   (current_prolog_flag(xref,true)-> false ;
    (current_prolog_flag(logicmoo_autoload,true)-> false ;
      ((prolog_load_context(file,F),  prolog_load_context(source,F))
             -> throw(error(format(":- include(~w).",[F]),ensure_loaded(F))) ; true))). 

%%% TODO one day :- set_prolog_flag(logicmoo_include,fail).


% :- include('pfc2.0/mpred_header.pi').

baseKB:mpred_skipped_module(eggdrop).
:- forall(current_module(CM),system:assert(baseKB:mpred_skipped_module(CM))).
:- retractall(baseKB:mpred_skipped_module(pfc)).

% ================================================
% DBASE_T System
% ================================================    

:- multifile(baseKB:safe_wrap/3).
:- dynamic(baseKB:safe_wrap/3).

:- set_prolog_flag(lm_expanders,false).
:- autoload([verbose(false)]).
:- set_prolog_flag(lm_expanders,true).
:- set_prolog_flag(virtual_stubs,true).
:- set_prolog_flag(mpred_te,false).

:- dmsg("Ensuring PFC Loaded",[]).

:- ensure_loaded(system:library('pfc2.0/mpred_core.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_at_box.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_type_isa.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_expansion.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_loader.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_props.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_kb_ops.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_agenda.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_storage.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_listing.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_stubs.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_type_constraints.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_type_naming.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_type_wff.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_type_args.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_hooks.pl')).
:- ensure_loaded(system:library('pfc2.0/mpred_prolog_file.pl')).


:- autoload([verbose(false)]).


%baseKB:sanity_check:- findall(U,(current_module(U),default_module(U,baseKB)),L),must(L==[baseKB]).
baseKB:sanity_check:- doall((current_module(M),setof(U,(current_module(U),default_module(U,M),U\==M),L),
     wdmsg(imports_eache :- (L,[sees(M)])))).
baseKB:sanity_check:- doall((current_module(M),setof(U,(current_module(U),default_module(M,U),U\==M),L),wdmsg(imports(M):-L))).
baseKB:sanity_check:- doall((baseKB:mtProlog(M),
    setof(U,(current_module(U),default_module(M,U),U\==M),L),wdmsg(imports(M):-L))).


%:- rtrace((mpred_at_box:defaultAssertMt(G40331),rtrace(set_prolog_flag(G40331:unknown,warning)))).
%:- dbreak.
:- must(set_prolog_flag(abox:unknown,error)).
%:- locally(t_l:side_effect_ok,doall(call_no_cuts(baseKB:module_local_init(abox,baseKB)))).
% :- forall(baseKB:sanity_check,true).


:- if( \+ prolog_load_context(reload,true)).
:-module_transparent(hook_database:ain/1).
:-module_transparent(hook_database:aina/1).
:-module_transparent(hook_database:ainz/1).
:-multifile(hook_database:ain/1).
:-multifile(hook_database:aina/1).
:-multifile(hook_database:ainz/1).
:-dynamic(hook_database:ain/1).
:-dynamic(hook_database:aina/1).
:-dynamic(hook_database:ainz/1).
:-asserta_new((hook_database:ainz(G):- !, mpred_ainz(G))).
:-asserta_new((hook_database:ain(G):- !, mpred_ain(G))).
:-asserta_new((hook_database:aina(G):- !, mpred_aina(G))).
:- endif.

% Load boot base file
user:lmbf:- 
 locally( set_prolog_flag(mpred_te,true),
  locally( set_prolog_flag(lm_expanders,true),
   locally(set_prolog_flag(pfc_booted,false),
     with_umt(baseKB,
  prolog_statistics:time((ensure_loaded(baseKB:library(logicmoo/pfc/'system_base.pfc')))))))),
  set_prolog_flag(pfc_booted,true).

:- module_transparent(user:exception/3).
:- multifile user:exception/3.
:- dynamic user:exception/3.
:- multifile system:exception/3.
:- module_transparent system:exception/3.
:- dynamic system:exception/3.



:- set_prolog_flag(system:unknown,error).
:- set_prolog_flag(user:unknown,error).
:- set_prolog_flag(lmcode:unknown,error).
:- set_prolog_flag(baseKB:unknown,error).


in_goal_expansion:- prolog_current_frame(F),
   prolog_frame_attribute(F,parent_goal,expand_goal(_,_,_,_)).

in_clause_expand(I):-  nb_current('$goal_term',Was),same_terms(I, Was),!,fail.
in_clause_expand(I):-  
   (nb_current_or_nil('$source_term',TermWas),\+ same_terms(TermWas, I)),
   (nb_current_or_nil('$term',STermWas),\+ same_terms(STermWas, I)),!,
   fail.
in_clause_expand(_).


maybe_should_rename(M,O):-current_prolog_flag(do_renames,term_expansion),do_renames(M,O),!.
maybe_should_rename(O,O).


:- multifile(baseKB:ignore_file_mpreds/1).
:- dynamic(baseKB:ignore_file_mpreds/1).
:- multifile(baseKB:expect_file_mpreds/1).
:- dynamic(baseKB:expect_file_mpreds/1).

:- if( \+ prolog_load_context(reload,true)).
:- during_boot(source_location(File, _)->asserta(baseKB:ignore_file_mpreds(File))).
:- doall((module_property(M,file(File)),module_property(M,class(library)),asserta(baseKB:ignore_file_mpreds(File)))).
:- doall((source_file(File),asserta(baseKB:ignore_file_mpreds(File)))).
:- doall((virtualize_ereq(F,A),base_kb_dynamic(F,A))).
:- endif.

% file late late joiners
baseKB:ignore_file_mpreds(File):- atom(File), module_property(M,file(File)),module_property(M,class(library)),asserta(baseKB:ignore_file_mpreds(File)),!.
baseKB:ignore_file_mpreds(File):- atom(File),( atom_concat(_,'.pfc.pl',File);atom_concat(_,'.plmoo',File);atom_concat(_,'.pfc',File)),!,asserta(baseKB:expect_file_mpreds(File)),fail.
baseKB:ignore_file_mpreds(File):- atom(File), baseKB:expect_file_mpreds(File),!,fail.
baseKB:ignore_file_mpreds(File):- baseKB:expect_file_mpreds(Stem),atom_concat(Stem,_,File),!,asserta(baseKB:expect_file_mpreds(File)),!,fail.
baseKB:ignore_file_mpreds(File):- baseKB:ignore_file_mpreds(Stem),atom_concat(Stem,_,File),!,asserta(baseKB:ignore_file_mpreds(File)).
baseKB:ignore_file_mpreds(File):- asserta(baseKB:expect_file_mpreds(File)),!,fail.

cannot_expand_current_file:- prolog_load_context(module,M),module_property(M,class(library)),!.
cannot_expand_current_file:- source_location(File,_)->baseKB:ignore_file_mpreds(File),!.

base_kb_dynamic(F,A):- ain(mpred_prop(F,A,prologHybrid)),kb_shared(F/A).

in_dialect_pfc:- \+ current_prolog_flag(dialect_pfc,false),
  ((current_prolog_flag(dialect_pfc,true); 
  is_pfc_file)),!.

is_pfc_file:- source_location(F,_W),( atom_concat(_,'.pfc.pl',F);atom_concat(_,'.plmoo',F);atom_concat(_,'.pfc',F)).

:- module_transparent(base_clause_expansion/2).
base_clause_expansion(_,_):- in_goal_expansion, !, fail.
base_clause_expansion(I,O):- base_clause_expansion_r(I,M),!,
   notrace((maybe_should_rename(M,O), ignore(( I\==O , nop(dmsg(base_clause_expansion(I)-->O)))))).

:- module_transparent(base_clause_expansion_r/2).
base_clause_expansion_r(':-'(IN), ':-'(O)):- !, IN = ('==>'(I)), sanity(nonvar(I)), fully_expand('==>'(I),O),!. % @TODO NOT NEEDED REALY UNLESS DO mpred_expansion:ensure_loaded(library('pfc2.0/mpred_expansion.pl')),
base_clause_expansion_r('==>'(I),  ':-'(ain_expanded('==>'(O)))):- !, sanity(nonvar(I)),must( fully_expand('==>'(I),O)), mpred_core:get_consequent_functor(O,F,A),kb_shared(F/A),ain(mpred_prop(F,A,prologHybrid)).
base_clause_expansion_r('==>'(I,M),':-'(ain_expanded('==>'(I,M)))):- !.
base_clause_expansion_r('<==>'(I,M),':-'(ain_expanded('<==>'(I,M)))):- !.
base_clause_expansion_r('<-'(I,M),':-'(ain_expanded('<-'(I,M)))):- !,mpred_core:get_consequent_functor(I,F,A),base_kb_dynamic(F,A).
base_clause_expansion_r(':-'(I,(Cwc,O)),':-'(ain_expanded(':-'(I,(Cwc,O))))):- Cwc == cwc,!,mpred_core:get_consequent_functor(I,F,A),base_kb_dynamic(F,A).
base_clause_expansion_r(I, O):- mpred_core:get_consequent_functor(I,F,A)->base_clause_expansion_fa(I,O,F,A),!. % @TODO NOT NEEDED REALY UNLESS DO mpred_core:ensure_loaded(library('pfc2.0/mpred_core.pl')),

% Checks if **should** be doing base_expansion or not      
:- module_transparent(base_clause_expansion_fa/4).
base_clause_expansion_fa(_,_,F,A):- clause_b(mpred_prop(F,A,prologBuiltin)),!,fail.
base_clause_expansion_fa(I,O,F,A):- 
  (needs_pfc(F,A) -> true ; (in_dialect_pfc, \+ cannot_expand_current_file, !, base_kb_dynamic(F,A))),!,
  base_clause_expansion_r('==>'(I),O).
base_clause_expansion_fa(_,_,F,A):- ain(mpred_prop(F,A,prologBuiltin)),!,fail.

:- module_transparent(needs_pfc/2).
needs_pfc(F,_):- (clause_b(functorIsMacro(F));clause_b(functorDeclares(F))).
needs_pfc(F,A):- clause_b(mpred_prop(F,_,prologHybrid)), \+ clause_b(mpred_prop(F,A,prologBuiltin)).
/*
maybe_builtin(I) :- nonvar(I),get_consequent_functor(I,F,A),
   \+ (clause_b(functorIsMacro(F));clause_b(functorDeclares(F));clause_b(mpred_prop(F,A,prologHybrid))),
   ain(prologBui sltin(F/A)).

*/

% :- ( defaultAssertMt(_)->true;set_defaultAssertMt(baseKB)).

% :- ensure_loaded(system:library('pfc2.0/mpred_userkb.pl')).


:- sanity((clause(baseKB:ignore_file_mpreds(_),B),compound(B))).

:- autoload([verbose(false)]).
:- statistics.
:- set_prolog_flag(lm_expanders,true).

:- ain(arity(functorDeclares, 1)).
% Load boot base file
%:- dynamic(isa/2).

%is_lm_mod(M):-atom_concat('logicmoo_i_',_,M).
%is_lm_mod(M):-atom_concat('common_logic_',_,M).
%is_lm_mod(M):-atom_concat('mpred_',_,M).
%is_lm_mod(M):-atom_concat('baseK',_,M).
is_lm_mod(M):-atom_concat('mud_',_,M).
make_exported(op(X,Y,Z),:-op(X,Y,Z)).
make_exported(Pred,:-export(Pred)).

system:term_expansion_UNUSED(:-module(M,List),Pos,ExportList,Pos):- nonvar(Pos),
  ((prolog_load_context(file,File),\+ prolog_load_context(source,File));is_lm_mod(M)),
   maplist(make_exported,List,ExportList).

%:- thread_local t_l:side_effect_ok/0.
%.
%system:goal_expansion(I,P1,O,P2):- current_prolog_flag(mpred_te,true),mpred_te(goal,system,I,P1,O,P2).
%system:term_expansion(I,P1,O,P2):- current_prolog_flag(mpred_te,true),mpred_te(term,system,I,P1,O,P2).

% system:clause_expansion(I,PosI,O,PosI):- base_clause_expansion(I,O),!.
system:term_expansion(I,PosI,O,PosI):- compound(I),nonvar(PosI), \+ current_prolog_flag(lm_expanders,false),
      in_clause_expand(I) -> base_clause_expansion(I,O) ->I\==O,!.
      
% Enable System
% system:exception(undefined_predicate,MFA, Action):- trace, current_prolog_flag(retry_undefined,true),ensure_loaded(library('pfc2.0/mpred_at_box.pl')), must(loop_check(mpred_at_box:uses_predicate(MFA, Action),Action=error)).
user:exception(undefined_predicate, MFA, Action):- fail, current_prolog_flag(retry_undefined,true),
  ensure_loaded(library('pfc2.0/mpred_at_box.pl')), 
    must(loop_check(mpred_at_box:uses_predicate(MFA, Action),Action=error)).

:- set_prolog_flag(mpred_te,true).
:- set_prolog_flag(lm_expanders,true).
:- set_prolog_flag(read_attvars,false).
:- set_prolog_flag(pfc_booted,false).
:- set_prolog_flag(virtual_stubs,true).
:- retractall(t_l:disable_px).

% prolog:message(ignored_weak_import(Into, From:PI))--> { nonvar(Into),Into \== system,dtrace(dmsg(ignored_weak_import(Into, From:PI))),fail}.
% prolog:message(Into)--> { nonvar(Into),functor(Into,_F,A),A>1,arg(1,Into,N),\+ number(N),dtrace(wdmsg(Into)),fail}.

:- ensure_loaded(baseKB:library(logicmoo/pfc/'system_base.pfc')).

:- fixup_exports.

