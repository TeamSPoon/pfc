/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(( current_prolog_flag(xref,true) ;
   ('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod))))).
:- endif.
:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
:- module(pfc_mod,[]).
:- prolog_load_context(file,File),unload_file(File).
:- endif.
:- pfc_lib:use_module(pfc_lib).
:- if( \+  current_prolog_flag(xref,true)).
:- must(retract(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod))),
   show_wdmsg(baseKB:'chusing_pfc'(M,CM,SM,pfc_mod)),
   (M==SM -> 
     (maybe_ensure_abox(SM),nop((M:ain(genlMt(SM,baseKB)))));
     show_wdmsg(baseKB:'lusing_pfc'(M,CM,SM,pfc_mod))),   
   assert(baseKB:'$using_pfc'(M,CM,SM,pfc_mod)),
   asserta(SM:'$does_use_pfc_mod'(M,CM,SM,pfc_mod)).
   %backtrace(200).
   
%:- set_prolog_flag(retry_undefined, kb_shared).
%:- set_prolog_flag(pfc_ready, true).
:- set_prolog_flag(expect_pfc_file,unknown).
:- endif.
