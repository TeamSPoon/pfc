/*   
%  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles
%
%   File   : pfccompile.pl
%   Author : Tim Finin, finin@prc.unisys.com
%   Updated: 10/11/87, ...
%   Purpose: compile system file for Pfc


*/
:- if(('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'using_pfc'(M,CM,SM,pfc_lib)))).
:- endif.
:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
:- module(pfc_lib,[]).
:- endif.
%:- set_prolog_flag(gc,false).
:- set_prolog_flag(pfc_version,2.0).

:- set_prolog_flag(retry_undefined, kb_shared).

:- if( \+ current_prolog_flag(xref,true)).

:- if(\+ current_prolog_flag(lm_no_autoload,_)).
:- set_prolog_flag(lm_no_autoload,true).
%:- print_message(informational,"WARNING: PFC_NOAUTOLOAD").
:- endif.

:- if(\+ current_prolog_flag(lm_pfc_lean,_)).
:- set_prolog_flag(lm_pfc_lean,false).
%:- print_message(informational,"WARNING: NOT PFC_LEAN").
:- endif.

:- endif.

:- set_prolog_flag(subclause_expansion,false).

kb_global_w(M:F/A):- 
   M:multifile(M:F/A),
   M:module_transparent(M:F/A),
   M:dynamic(M:F/A),
   M:export(M:F/A),
   do_import(system,M,F,A),
   do_import(user,M,F,A),
   do_import(pfc_lib,M,F,A),
   do_import(header_sane,M,F,A),
   M:kb_global(M:F/A),
   system:import(M:F/A).

:- use_module(library(logicmoo_utils_all)).

/*
:- use_module(library(file_scope)).
:- set_prolog_flag_until_eof(access_level,system).

:- use_module(library(hook_hybrid)).
:- use_module(library(logicmoo/each_call)).
:- use_module(library(logicmoo/attvar_reader)).
:- use_module(library(logicmoo/each_call_cleanup)).
:- use_module(library(logicmoo/must_trace)).
:- use_module(library(logicmoo/virtualize_source)).

:- use_module(library(logicmoo/no_repeats)).
:- use_module(library(logicmoo/logicmoo_util_strings)).
:- use_module(library(logicmoo/loop_check)).
:- use_module(library(logicmoo/attvar_serializer)).
*/

:- dynamic(rdf_rewrite:(~)/1).
:- kb_global_w(rdf_rewrite:arity/2).
:- kb_global_w(baseKB:genlMt/2).
:- kb_global_w(baseKB:predicateTriggerType/1).
:- kb_global_w(baseKB:mtHybrid/1).
:- kb_global_w(baseKB:mtProlog/1).
:- kb_global_w(baseKB:tCol/1).
:- kb_global_w(baseKB:mpred_database_term/3).
:- kb_global_w(baseKB:mtNoPrologCode/1).
:- kb_global_w(baseKB:ftText/1).
:- kb_global_w(baseKB:mtNotInherits/1).
:- kb_global_w(baseKB:mtInherits/1).
:- kb_global_w(baseKB:rtArgsVerbatum/1).
:- kb_global_w(baseKB:prologHybridType/3).
:- kb_global_w(baseKB:mpred_skipped_module/1).


:- kb_global_w(baseKB:mpred_prop/4).

:- kb_global_w(baseKB:pk/3).
:- kb_global_w(baseKB:hs/1).
:- kb_global_w(baseKB:que/2).
:- kb_global_w(baseKB:pm/1).
:- kb_global_w(baseKB:tms/1).

:- kb_global_w(baseKB:do_and_undo/2).
:- kb_global_w(baseKB:bt/2).
:- kb_global_w(baseKB:nt/3).
:- kb_global_w(baseKB:pt/2).
:- kb_global_w(baseKB:spft/3).

/*

WILL BE ..
:- kb_global_w(baseKB:tpky/4).
:- kb_global_w(baseKB:hlts/2).
:- kb_global_w(baseKB:quem/3).
:- kb_global_w(baseKB:pmfc/2).
:- kb_global_w(baseKB:tms/2).

:- kb_shared(baseKB:do_and_undo/3).
:- kb_shared(baseKB:bkch/3).
:- kb_shared(baseKB:tneg/4).
:- kb_shared(baseKB:tpos/3).
:- kb_shared(baseKB:spft/4).
*/

:- kb_shared(baseKB:never_assert_u/1).
:- kb_shared(baseKB:never_assert_u/2).
:- kb_shared(baseKB:never_retract_u/1).
:- kb_shared(baseKB:never_retract_u/2).






%:- listing(arity/2).
%:- listing(baseKB:_).

:- set_prolog_flag_until_eof(debug,true).

:- if(\+ current_prolog_flag(lm_no_autoload,_)).
:- set_prolog_flag(lm_no_autoload,true).
:- dmsg_pretty("WARNING: PFC_NOAUTOLOAD").
:- endif.

:- if(\+ current_prolog_flag(lm_pfc_lean,_)).
:- set_prolog_flag(lm_pfc_lean,true).
:- dmsg_pretty("WARNING: PFC_LEAN").
:- endif.


kb_shared_base(M:FA):-!,kb_shared(M:FA).
kb_shared_base(FA):-kb_local(baseKB:FA).
kb_local_base(M:FA):-!,kb_local(M:FA).
kb_local_base(FA):-kb_local(baseKB:FA).
kb_global_base(M:FA):-!,kb_global(M:FA).
kb_global_base(FA):- kb_local(baseKB:FA).



% :- kb_global_base(baseKB:genlMt/2).

% :- kb_shared(baseKB:mpred_prop/4).

:- baseKB:forall(between(1,11,A),kb_local(t/A)).
:- baseKB:forall(between(5,7,A),kb_local(mpred_f/A)).

% :- kb_shared_base(baseKB:admittedArgument/3).
%:- set_prolog_flag(runtime_speed,0). % 0 = dont care
:- set_prolog_flag(runtime_speed, 1). % 1 = default
:- set_prolog_flag(runtime_debug, 1). % 2 = important but dont sacrifice other features for it
:- set_prolog_flag(runtime_safety, 3).  % 3 = very important
:- set_prolog_flag(unsafe_speedups, false).
:- set_prolog_flag(pfc_booted,false).


:- use_module(library(prolog_pack)).

pfc_rescan_autoload_pack_packages_part_1:-!.
pfc_rescan_autoload_pack_packages_part_1:- dmsg_pretty("SCAN AUTOLOADING PACKAGES..."),
 forall('$pack':pack(Pack, _),
  forall(((pack_property(Pack, directory(PackDir)),prolog_pack:pack_info_term(PackDir,autoload(true)))),
  (access_file(PackDir,write) -> prolog_pack:post_install_autoload(PackDir, [autoload(true)]) ; dmsg_pretty(cannot_access_file(PackDir,write))))),
 dmsg_pretty(".. SCAN AUTOLOADING COMPLETE"),!.
:- current_prolog_flag(lm_no_autoload,true) -> true; pfc_rescan_autoload_pack_packages_part_1.


:- meta_predicate pack_autoload_packages(0).
pack_autoload_packages(NeedExistingIndex):- 
 forall(user:expand_file_search_path(library(''),Dir),
  ignore(( (\+ NeedExistingIndex ; absolute_file_name('INDEX',_Absolute,[relative_to(Dir),access(read),file_type(prolog),file_errors(fail)]))->
   maybe_index_autoload_dir(Dir)))),
 reload_library_index.


maybe_index_autoload_dir(PackDir):- \+ access_file(PackDir,write),!,dmsg_pretty(cannot_write_autoload_dir(PackDir)).
maybe_index_autoload_dir(PackDir):- user:library_directory(PackDir), make_library_index(PackDir, ['*.pl']),dmsg_pretty(update_library_index(PackDir)).
maybe_index_autoload_dir(PackDir):- fail,
  prolog_pack:pack_info_term(PackDir,autoload(true)),
  prolog_pack:post_install_autoload(PackDir, [autoload(true)]) ,
  dmsg_pretty(post_install_autoload(PackDir,write)).  
maybe_index_autoload_dir(PackDir):- asserta(user:library_directory(PackDir)), make_library_index(PackDir, ['*.pl']), dmsg_pretty(created_library_index_for(PackDir)).

pfc_rescan_autoload_pack_packages_part_2 :- !.
pfc_rescan_autoload_pack_packages_part_2 :- pack_autoload_packages(true).

:- current_prolog_flag(lm_no_autoload,true) -> true; pfc_rescan_autoload_pack_packages_part_2.



input_from_file:- prolog_load_context(stream,Stream),current_input(Stream).


:- module_transparent(intern_predicate/1).
:- module_transparent(intern_predicate/2).
intern_predicate(MFA):- '$current_typein_module'(To),intern_predicate(To,MFA).
intern_predicate(To,F/A):- !, '$current_source_module'(M),intern_predicate(To,M:F/A).
intern_predicate(To,From:F/A):-!,
  From:module_transparent(From:F/A),
  From:export(From:F/A),To:export(From:F/A),To:export(From:F/A),
  From:compile_predicates([F/A]),system:lock_predicate(From:F/A),
  export(From:F/A),export(From:F/A),
  pfc:export(From:F/A),pfc:export(From:F/A),
  user:export(From:F/A),user:export(From:F/A),
  baseKB:export(From:F/A),baseKB:export(From:F/A),
  system:export(From:F/A),system:export(From:F/A),!.


scan_missed_source:-!.
scan_missed_source:-
  prolog_load_context(file,File),scan_missed_source(File),
  prolog_load_context(source,SFile),!,
  (SFile==File-> true; scan_missed_source(SFile)).

:- system:import(pfc_lib:scan_missed_source/0).

scan_missed_source(SFile):-prolog_load_context(module,M),
   forall(source_file(Pred,SFile),scan_missed_source(M,Pred,SFile)).

scan_missed_source(M,Pred,SFile):- \+ M:clause(Pred,_,_),!,nop(dmsg_pretty(scan_missed_source(M,Pred,SFile))).
scan_missed_source(M,Pred,SFile):- doall((M:clause(Pred,_,Ref),
  (clause_property(Ref,file(SFile)) -> visit_pfc_file_ref(M,Ref) ; visit_pfc_non_file_ref(M,Ref)))).

visit_pfc_file_ref(M,Ref):- system:clause(H,B,Ref),dmsg_pretty(visit_pfc_file_ref(M,H,B)).
visit_pfc_non_file_ref(M,Ref):- system:clause(H,B,Ref),dmsg_pretty(visit_pfc_non_file_ref(M,H,B)).



:- intern_predicate(system,intern_predicate/1).

:- intern_predicate(system,intern_predicate/2).

'?='(ConsqIn):- fully_expand(ConsqIn,Consq),call_u(Consq),forall(mpred_why(Consq,Ante),dmsg_pretty(Ante)).
'?=>'(AnteIn):- fully_expand(AnteIn,Ante),call_u(Ante),forall(mpred_why(Consq,Ante),dmsg_pretty(Consq)).

:- lock_predicate(pfc:'?='/1).
:- lock_predicate(pfc:'?=>'/1).

:- thread_local(t_l:disable_px).

:- include('pfc2.0/mpred_header.pi').

/*
:- nop(kb_shared((
   bkch/2, %basePFC
   hs/1, %basePFC
   tneg/3, %basePFC
   tpky/3, %basePFC
   tpky/2, %basePFC
   que/1, %basePFC
   pm/1, %basePFC
   spft/3, %basePFC
   tms/1 %basePFC
   ))).
:- nop(kb_shared( ('~') /1)).
*/


:- if( \+ current_predicate(each_call_cleanup/3)).
:- use_module(library(each_call_cleanup)).
:- endif.

/*
% Make YALL require ">>" syntax (the problem was it autoloads when its sees PFC code containing "/" and gripes all the time)

disable_yall:- multifile(yall:lambda_functor/1),
   dynamic(yall:lambda_functor/1),
   with_no_mpred_expansions(use_module(yall:library(yall),[])),
   retractall(yall:lambda_functor('/')).

:- disable_yall.
*/

:- set_prolog_flag_until_eof(access_level,system).

/*
% baseKB:startup_option(datalog,sanity). %  Run datalog sanity tests while starting
% baseKB:startup_option(clif,sanity). %  Run datalog sanity tests while starting
:- set_prolog_flag(fileerrors,false).
%:- set_prolog_flag(gc,false).
:- set_prolog_flag(gc,true).
:- set_prolog_flag(optimise,false).
:- set_prolog_flag(last_call_optimisation,false).
:- set_prolog_flag(debug,true).
:- debug.
*/
%:- guitracer.
%:- set_prolog_flag(access_level,system).

% :- set_prolog_flag(logicmoo_autoload,false).
% :- set_prolog_flag(logicmoo_autoload,true).

% must be xref-ing or logicmoo_autoload or used as include file
:- set_prolog_flag(logicmoo_include,lmbase:skip_module_decl).
% lmbase:skip_module_decl:- source_location(F,L),dmsg_pretty(lmbase:skip_module_decl(F:L)),!,fail.
lmbase:skip_module_decl:- prolog_load_context(file,F), prolog_load_context(source,S),S\=F,!.
lmbase:skip_module_decl:-!,fail.
lmbase:skip_module_decl:-
   (current_prolog_flag(xref,true)-> false ;
    (current_prolog_flag(logicmoo_autoload,true)-> false ;
      ((prolog_load_context(file,F),  prolog_load_context(source,F))
             -> throw(error(format(":- include(~w).",[F]),reexport(F))) ; true))). 

%%% TODO one day :- set_prolog_flag(logicmoo_include,fail).


baseKB:mpred_skipped_module(eggdrop).
:- forall(current_module(CM),assert(baseKB:mpred_skipped_module(CM))).
:- retractall(baseKB:mpred_skipped_module(pfc_lib)).

% ================================================
% DBASE_T System
% ================================================    

:- multifile(baseKB:safe_wrap/4).
:- dynamic(baseKB:safe_wrap/4).

:- if((current_prolog_flag(runtime_debug,D),D>1)).
:- dmsg_pretty("Ensuring PFC Loaded").
:- endif.


%:- user:ensure_loaded(library('file_scope')).
% :- set_how_virtualize_file(bodies).
:- module_transparent(baseKB:prologBuiltin/1).
:- multifile baseKB:prologBuiltin/1.
:- discontiguous baseKB:prologBuiltin/1.
:- dynamic baseKB:prologBuiltin/1.

:- ensure_loaded(library('pfc2.0/mpred_at_box.pl')).
:- ensure_loaded(library('pfc2.0/mpred_justify.pl')).
:- ensure_loaded(library('pfc2.0/mpred_core.pl')).
:- ensure_loaded(library('pfc2.0/mpred_gvars.pl')).
:- ensure_loaded(library('pfc2.0/mpred_expansion.pl')).
:- ensure_loaded(library('pfc2.0/mpred_loader.pl')).
:- ensure_loaded(library('pfc2.0/mpred_database.pl')).
:- ensure_loaded(library('pfc2.0/mpred_listing.pl')).
:- ensure_loaded(library('pfc2.0/mpred_prolog_file.pl')).
:- ensure_loaded(library('pfc2.0/mpred_terms.pl')).


%:- autoload([verbose(false)]).



%baseKB:sanity_check:- findall(U,(current_module(U),default_module(U,baseKB)),L),must(L==[baseKB]).
baseKB:sanity_check:- doall((current_module(M),setof(U,(current_module(U),default_module(U,M),U\==M),L),
     dmsg_pretty(imports_eache :- (L,[sees(M)])))).
baseKB:sanity_check:- doall((current_module(M),setof(U,(current_module(U),default_module(M,U),U\==M),L),dmsg_pretty(imports(M):-L))).
baseKB:sanity_check:- doall((baseKB:mtProlog(M),
    setof(U,(current_module(U),default_module(M,U),U\==M),L),dmsg_pretty(imports(M):-L))).


%:- rtrace((pfc_lib:defaultAssertMt(G40331),rtrace(set_prolog_flag(G40331:unknown,warning)))).
%:- dbreak.
:- must(set_prolog_flag(abox:unknown,error)).
%:- locally_tl(side_effect_ok,doall(call_no_cuts(module_local_init(abox,baseKB)))).
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
:-asserta_new((hook_database:ain(G):- !, must(mpred_ain(G)))).
:-asserta_new((hook_database:ainz(G):- !, must(mpred_ainz(G)))).
:-asserta_new((hook_database:aina(G):- !, must(mpred_aina(G)))).

/*
:-module_transparent(pfc_lib:mpred_ain/1).
:-module_transparent(pfc_lib:mpred_aina/1).
:-module_transparent(pfc_lib:mpred_ainz/1).
:-multifile(pfc_lib:mpred_ain/1).
:-multifile(pfc_lib:mpred_ain/2).
:-multifile(pfc_lib:mpred_aina/1).
:-multifile(pfc_lib:mpred_ainz/1).
:-dynamic(pfc_lib:mpred_ain/1).
:-dynamic(pfc_lib:mpred_aina/1).
:-dynamic(pfc_lib:mpred_ainz/1).
*/
:- endif.

% Load boot base file
user:lmbf:- 
 locally( set_prolog_flag(mpred_te,true),
  locally( set_prolog_flag(subclause_expansion,true),
   locally(set_prolog_flag(pfc_booted,false),
     with_umt(baseKB,
  prolog_statistics:time((reexport(baseKB:library(logicmoo/pfc/'system_base.pfc')))))))),
  set_prolog_flag(pfc_booted,true).

/*
:- set_prolog_flag(unknown,error).
:- set_prolog_flag(user:unknown,error).
:- set_prolog_flag(lmcode:unknown,error).
:- set_prolog_flag(baseKB:unknown,error).
*/
:- sanity(current_prolog_flag(unknown,error)).
:- sanity(current_prolog_flag(user:unknown,error)).

in_goal_expansion:- prolog_current_frame(F),
   prolog_frame_attribute(F,parent_goal,expand_goal(_,_,_,_)).

in_clause_expand(I):-  nb_current('$goal_term',Was),same_terms(I, Was),!,fail.
in_clause_expand(I):-  
   (nb_current_or_nil('$source_term',TermWas),\+ same_terms(TermWas, I)),
   (nb_current_or_nil('$term',STermWas),\+ same_terms(STermWas, I)),!,
   fail.
in_clause_expand(_).


% SHOULD NOT NEED THIS 
%   maybe_should_rename(M,O):-current_prolog_flag(do_renames,term_expansion),if_defined(do_renames(M,O)),!.
maybe_should_rename(O,O).


% file late late joiners
:- if( \+ prolog_load_context(reload,true)).
:- source_location(File, _)-> during_boot(((set_how_virtualize_file(false,File)))).
:- doall((module_property(M,file(File)),module_property(M,class(CT)),memberchk(CT,[library,system]),(set_how_virtualize_file(false,File)))).
%:- doall((source_file(File),(set_how_virtualize_file(false,File)))).
%base_kb_dynamic(F,A):- ain(mpred_prop(M,F,A,prologHybrid)),kb_shared(F/A).
%:- doall((virtualize_ereq(F,A),base_kb_dynamic(F,A))).
:- endif.

:- discontiguous(baseKB:'$pldoc'/4).

in_dialect_pfc:- is_pfc_file. % \+ current_prolog_flag(dialect_pfc,cwc),!.

%is_pfc_module(SM):- clause_b(using_pfc(SM,_, SM, pfc_toplevel)),!.
%is_pfc_module(SM):- clause_b(using_pfc(SM,_, SM, pfc_mod)),!,baseKB:mtCanAssert(SM).
is_pfc_module(SM):- clause_b(mtHybrid(SM)).


:- pfc_lib:export(pfc_lib:is_pfc_file/0).
is_pfc_file:- current_prolog_flag(expect_pfc_file,always),!,must_or_rtrace(is_pfc_file0).
is_pfc_file:- current_prolog_flag(expect_pfc_file,never),!,must_or_rtrace(\+ is_pfc_file0).
is_pfc_file:- quietly(is_pfc_file0),!.

:- system:import(pfc_lib:is_pfc_file/0).
%:- header_sane:import(is_pfc_file/0).

:- pfc_lib:export(pfc_lib:is_pfc_file0/0).
is_pfc_file0:- (prolog_load_context(file,File);source_location(File,_W)),!,prolog_load_context(source, SFile)-> 
 is_pfc_filename(File,SFile).
is_pfc_file0:- notrace(current_source_file(FileL)),(FileL=File:_->is_pfc_file(File)).
 %is_pfc_file0:- \+ , prolog_load_context(module, M),M\==baseKB,is_pfc_module(M),!,clause_b(mtHybrid(M)).
:- system:import(pfc_lib:is_pfc_file0/0).

is_pfc_file(File):- is_pfc_filename(File,File).
% First checks to confirm there is nothing inhibiting
is_pfc_filename(File,_):- call(call,lmcache:mpred_directive_value(File, language, Lang)),!,(Lang==pfc;Lang==clif;Lang==fwd).
is_pfc_filename(File,_):- atom_concat(_,'.pfc.pl',File);atom_concat(_,'.clif',File);atom_concat(_,'.plmoo',File);atom_concat(_,'.pfc',File),!.
%is_pfc_filename(File,_):- check_how_virtualize_file(false,File),!,fail.
is_pfc_filename(File,_):- baseKB:how_virtualize_file(heads,File,0),!.
is_pfc_filename(File,File):-!,fail.
is_pfc_filename(_,File):- call(call,lmcache:mpred_directive_value(File, language, Lang)),!,(Lang==pfc;Lang==clif;Lang==fwd).
is_pfc_filename(_,File):- check_how_virtualize_file(heads,File),!.
is_pfc_filename(_,File):- check_how_virtualize_file(false,File),!,fail.
%is_pfc_filename(_,File):- atom_concat(_,'.pfc.pl',File);atom_concat(_,'.clif',File);atom_concat(_,'.plmoo',File);atom_concat(_,'.pfc',File),!.


:- fixup_exports.

sub_atom(F,C):- sub_atom(F,_,_,_,C).

only_expand(':-'(I), ':-'(M)):- !,in_dialect_pfc,fully_expand(I,M),!.
only_expand(I,OO):- quietly(must_pfc(I,M)),  
  % current_why(S),!,
  S= mfl4(_VarNameZ,Module, File, Line),source_location(File,Line),prolog_load_context(module,Module),
  conjuncts_to_list(M,O), !, %  [I]\=@=O,
  make_load_list(O,S,OO).

make_load_list([C|O],S,[baseKB:spft(C,S,ax), :- mpred_enqueue_w_mode(S,direct,C)|OO]):- clause_asserted(C),!, make_load_list(O,S,OO).
make_load_list([C|O],S,[C, baseKB:spft(C,S,ax), :- mpred_enqueue_w_mode(S,direct,C)|OO]):-  is_loadin(C),!,make_load_list(O,S,OO).
make_load_list(_,_,[]):-!.  
                 
is_loadin(C):- strip_module(C,M,CC),is_loadin(M,CC).
is_loadin(_,CC):- must_pfc_p(CC),!.
is_loadin(_,(_:-_)):-!.
is_loadin(M,CC):- functor(CC,F,A),show_call(kb_local(M:F/A)),break.


must_pfc_exp(P,PO):- (in_dialect_pfc;must_pfc_p(P)),fully_expand(P,PO),!.

%must_pfc(IM,'==>'(IM)):- (in_dialect_pfc;must_pfc_p(IM)),!.
must_pfc(IM,_):- is_never_pfc(IM),!,fail.
must_pfc(SM:P,SM:'==>'(P)):- !, (in_dialect_pfc;must_pfc_p(P)),!.
must_pfc(P,P):- (in_dialect_pfc;must_pfc_p(P)),!. % ,source_module(SM),!.

must_pfc_p(F):- \+ compound(F),!,atom(F),must_pfc_fa(F,0),!.
%must_pfc_p('-->'(_,_)):-!,fail.
must_pfc_p(M:_):- M==system,!,fail.
must_pfc_p(_:P):- !, must_pfc_p(P),!.
must_pfc_p(':-'(_,(CWC,_))):- atom(CWC),arg(_,v(bwc,fwc,awc,zwc),CWC),!.
must_pfc_p(':-'(_,(CWC,_))):- atom(CWC),arg(_,v(cwc),CWC),!,in_dialect_pfc.
must_pfc_p(':-'(Head,_)):- !, must_pfc_p(Head),!.
must_pfc_p('==>'(_,_)).
must_pfc_p('==>'(_)).
must_pfc_p('<==>'(_,_)).
must_pfc_p('<=='(_,_)).
must_pfc_p('<-'(_,_)).
must_pfc_p('<--'(_,_)).
must_pfc_p('->'(_,_)).
must_pfc_p('~'(_)).
must_pfc_p('===>'(_,_)).
% must_pfc_p('=>'(_,_)).
must_pfc_p(FAB):- compound_name_arity(FAB,F,A),must_pfc_fa(F,A),!.

must_pfc_fa(prologHybrid,_).
must_pfc_fa(F,A):- mpred_database_term(F,A,_),!.
must_pfc_fa(F,A):- clause_b(mpred_prop(M,F,A,_)),!, \+ clause_b(mpred_prop(M,F,A,prologBuiltin)).
must_pfc_fa(F,2):- sub_atom(F,'='),(atom_concat(_,'>',F);atom_concat('<',_,F)).


:- module_transparent(base_clause_expansion/2).

% module prefixed clauses for sure should be non pfc?
is_never_pfc(Var):- \+ callable(Var),!.
%is_never_pfc(_):- prolog_load_context(file,F),\+ prolog_load_context(source,F),atom_concat(_,'.pl',F),\+ atom_concat(_,'pfc.pl',F).
is_never_pfc(goal_expansion(_,_,_,_)).
is_never_pfc(':-'(_)).
is_never_pfc('?-'(_)).
is_never_pfc('-->'(_,_)):-!.
is_never_pfc(attr_unify_hook(_,_)):-!.
is_never_pfc(':-'(C,_)):- !,is_never_pfc(C).
is_never_pfc(M:P):- functor(P,F,A),clause_b(mpred_prop(M,F,A,prologBuiltin)),!.
is_never_pfc(_:C):- is_never_pfc(C).

% TODO Maybe find a better spot?  see t/sanity_base/hard_mt_04a.pfc
/*is_never_pfc(M:C):- \+ is_never_pfc(C), \+ current_module(M),
   is_pfc_file0,
   fileAssertMt(CMt),
   CMt:clause_b(mtHybrid(CMt)),
   CMt:ensure_abox(M),
   CMt:ain(genlMt(CMt,M)),!,fail.
*/


% base_clause_expansion(Var,Var):- current_prolog_flag(mpred_te,false),!.
base_clause_expansion(Var,Var):-var(Var),!.
base_clause_expansion( :- module(W,List), [:- writetln(module(W,List)), :- set_fileAssertMt(W)]):- in_dialect_pfc,!.
base_clause_expansion('?=>'(I), ':-'('?=>'(I))):- !.
base_clause_expansion(':-'(In),':-'(Out)):- in_dialect_pfc,fully_expand(In,Out),!.
base_clause_expansion(':-'(I),':-'(I)):- !.
base_clause_expansion(IM,':-'(mpred_ain(==>(IM),S))):- \+ callable(IM),!, get_source_uu(S).

base_clause_expansion(IM, ':-'(mpred_ain(==>(IM),S))):- atomic(IM),(sub_atom(IM,';');sub_atom(IM,'(')),!,get_source_uu(S).
base_clause_expansion(IN, ':-'(mpred_ain(ASSERT,S))):- must_pfc(IN,ASSERT),!,get_source_uu(S).
base_clause_expansion(NeverPFC, EverPFC):- is_never_pfc(NeverPFC),!,NeverPFC=EverPFC.
base_clause_expansion(In,Out):- in_dialect_pfc,fully_expand(In,Out),!.
base_clause_expansion(M:In,M:Out):- !,base_clause_expansion(In,Out).
%base_clause_expansion(In,Out):- fully_expand(In,Out),!.

/*


% Checks if **should** be doing base_expansion or not      
:- module_transparent(base_clause_expansion_fa/4).
base_clause_expansion_fa(_,_,F,A):- clause_b(mpred_prop(M,F,A,prologBuiltin)),!,fail.
base_clause_expansion_fa(I,O,F,A):- (needs_pfc(F,A) -> true ; base_kb_dynamic(F,A)),
  base_clause_expansion('==>'(I),O).

:- module_transparent(needs_pfc/2).
needs_pfc(F,_):- (clause_b(functorIsMacro(F));clause_b(functorDeclares(F))).
needs_pfc(F,A):- base_kb_dynamic(F,A).
needs_pfc(F,A):- clause_b(mpred_prop(M,F,_,prologHybrid)), \+ clause_b(mpred_prop(M,F,A,prologBuiltin)).

maybe_builtin(M : _ :-_):- atom(M),!.
maybe_builtin(M : _ ):- atom(M),!.
maybe_builtin(I) :- nonvar(I),get_unnegated_functor(I,F,A),
   \+ (clause_b(functorIsMacro(F));clause_b(functorDeclares(F));clause_b(mpred_prop(M,F,A,prologHybrid))),
   ain(prologBui sltin(F/A)).

*/

:- if(false).
%:- autoload([verbose(false)]).
:- statistics.
:- endif.

% :- ain(arity(functorDeclares, 1)).
% Load boot base file
%:- dynamic(isa/2).

%is_lm_mod(M):-atom_concat('logicmoo_i_',_,M).
%is_lm_mod(M):-atom_concat('common_logic_',_,M).
%is_lm_mod(M):-atom_concat('mpred_',_,M).
%is_lm_mod(M):-atom_concat('baseK',_,M).
is_lm_mod(M):-atom_concat('mud_',_,M).
make_exported(op(X,Y,Z),:-op(X,Y,Z)).
make_exported(Pred,:-export(Pred)).

term_expansion_UNUSED(:-module(M,List),Pos,ExportList,Pos):- nonvar(Pos),
  ((prolog_load_context(file,File),\+ prolog_load_context(source,File));is_lm_mod(M)),
   maplist(make_exported,List,ExportList).

%:- thread_local t_l:side_effect_ok/0.



pfc_clause_expansion(I,O):- 
  nonvar(I), I\==end_of_file,  
  base_clause_expansion(I,M),!,I\=@=M,
   ((
      maybe_should_rename(M,MO), 
      ignore(( \+ same_expandsion(I,MO), dmsg_pretty(pfc_clause_expansion(I)-->MO))),
      maybe_directive_to_clauses(MO,O),
      ignore(( O\==MO , (dmsg_pretty(directive_to_clauses(I)-->O)))))),!.

:- module_transparent(pfc_clause_expansion/2).
:- system:import(pfc_lib:pfc_clause_expansion/2).

%maybe_directive_to_clauses(:- ain(A),Clauses):- loader_side_effect_capture_only(ain(A),Clauses).
%maybe_directive_to_clauses(:- ain(A),Clauses):- loader_side_effect_capture_only(ain(A),Clauses).
maybe_directive_to_clauses(O,O):-!.

same_expandsion(I,O):-var(I),!,I==O.
same_expandsion(I,O):-var(O),!,I==O.
same_expandsion(_:I,MO):-!,same_expandsion(I,MO).
same_expandsion(MO,_:I):-!,same_expandsion(I,MO).
same_expandsion('==>'(I),MO):-!,same_expandsion(I,MO).
same_expandsion(I,'==>'(MO)):-!,same_expandsion(I,MO).
same_expandsion(I,[MO|_]):-!,same_expandsion(I,MO).
same_expandsion(I, (:-ain(MO,_))):-!,same_expandsion(I,MO).
same_expandsion(I, (:-ain(MO))):-!,same_expandsion(I,MO).
same_expandsion(I, (:-mpred_ain(MO))):-!,same_expandsion(I,MO).
same_expandsion(I, (:-mpred_ain(MO,_))):-!,same_expandsion(I,MO).
same_expandsion(I,O):-I==O.

% prolog:message(ignored_weak_import(Into, From:PI))--> { nonvar(Into),Into \== system,dtrace(dmsg_pretty(ignored_weak_import(Into, From:PI))),fail}.
% prolog:message(Into)--> { nonvar(Into),functor_safe(Into,_F,A),A>1,arg(1,Into,N),\+ number(N),dtrace(dmsg_pretty(Into)),fail}.

/*
:- multifile(user:clause_expansion/2).
user:clause_expansion(I,O):- pfc_clause_expansion(I,O).
*/

/*
:- multifile(clause_expansion/2).
clause_expansion(I,O):- pfc_clause_expansion(I,O).
*/


% term_expansion(I,P1,O,P2):- in_dialect_pfc,mpred_te(term,system,I,P1,O,P2).

module_uses_pfc(SM):- current_predicate(SM:'$uses_pfc_toplevel'/0).

:- multifile(pfc_goal_expansion/4).
:- dynamic(pfc_goal_expansion/4).
:- module_transparent(pfc_goal_expansion/4).
pfc_goal_expansion(I,P,O,PO):- 
 quietly(( 
     \+ source_location(_,_),
     callable(I),          
     var(P), % Not a file goal     
     \+ current_prolog_flag(xref,true), 
     \+ current_prolog_flag(mpred_te,false),
     '$current_typein_module'(CM),
     prolog_load_context(module,SM),
     ((SM \== CM) -> module_uses_pfc(SM); module_uses_pfc(CM)), 
     (I \= (CM : call_u(_))), (I \= call_u(_)))),
     fully_expand(I,M),
     % quietly
     ((
     O=CM:call_u(M),
     PO=P)).


saveBaseKB:- tell(baseKB),listing(baseKB:_),told.

%baseKB:'==>'(Consq) :- sanity( \+ input_from_file), ain('==>'(Consq)),!.
%baseKB:'==>'(Ante,Consq):- sanity( \+ input_from_file), mpred_why_body(Consq,Ante).

pfc_may_see_module(M):-clause_b('using_pfc'(_OM,_CM,M,pfc_mod)).
pfc_may_see_module(M):-clause_b(mtHybrid(M)).
pfc_may_see_module(baseKB).
pfc_may_see_module(M):-import_module(M,pfc_lib).

:- fixup_exports.


:- if(exists_source(library(logicmoo/retry_undefined))).
:- ensure_loaded(library(logicmoo/retry_undefined)).
:- install_retry_undefined(baseKB,kb_shared).

:- else.

:- endif.




:- multifile(system:goal_expansion/4).
:- module_transparent(system:goal_expansion/4).
:- system:import(pfc_goal_expansion/4).
system:goal_expansion(I,P,O,PO):- pfc_goal_expansion(I,P,O,PO).

:- multifile(system:clause_expansion/2).
:- module_transparent(system:clause_expansion/2).

system:clause_expansion(I,O):-
 % ((in_dialect_pfc;prolog_load_context(module,M),pfc_may_see_module(M))),
  pfc_clause_expansion(I,O).

% :- current_predicate(system:F/A),functor(PI,F,A),
% \+ predicate_property(system:PI,imported_from(_)).




%:- set_prolog_flag(read_attvars,false).

:- retractall(t_l:disable_px).


:- set_prolog_flag(subclause_expansion,true).
:- set_prolog_flag(mpred_te,true).
:- set_prolog_flag(retry_undefined, module).

:- baseKB:ensure_loaded('pfclib/system_autoexec.pfc').
:- set_prolog_flag(pfc_booted,true).

:- set_prolog_flag(retry_undefined, kb_shared).
:- set_prolog_flag(pfc_ready, true).

:-hook_database:export(pfc_lib:mpred_ain/1).
:-hook_database:export(pfc_lib:mpred_aina/1).
:-hook_database:export(pfc_lib:mpred_ainz/1).

