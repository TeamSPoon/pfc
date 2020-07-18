/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(( current_prolog_flag(xref,true) ;
   ('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod))))).
:- endif.
:- if(current_prolog_flag(xref,true);(prolog_load_context(source,File),prolog_load_context(file,File))).
:- module(pfc_mod,[]).
:- prolog_load_context(file,File),unload_file(File).
:- endif.
:- if( \+  current_prolog_flag(xref,true)).
:- use_module(library(logicmoo_utils)).
% :- 
:- retract(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod)),

   % Version 3.0
   /*
   absolute_file_name(library('pfc3.0/pfc_3_0_full'),FN,[access(read),file_type(prolog)]),
   open(FN,read,Input),
   atomic_list_concat([FN,'_local_',SM],FakeName),
   asserta(SM:'$does_use_pfc_mod'(M,CM,SM,FakeName)),
   system:load_files(FakeName,[module(SM),if(always),stream(Input),must_be_module(false),silent(false)]),
   */
   % Version 2.0
   SM:reexport(pfc_lib).


   maybe_ensure_abox(SM),
   assert(baseKB:'$using_pfc'(M,CM,SM,pfc_mod)),
   print_message(information,'chusing_pfc'(M,CM,SM,pfc_mod)).

:- \+ baseKB:'$using_pfc'(M,CM,SM,pfc_mod),
   '$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM)
   print_message(error,'lusing_pfc'(M,CM,SM,pfc_mod)),!.
:- endif.
