/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(( current_prolog_flag(xref,true) ;
   ('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'wusing_pfc'(M,CM,SM,pfc_header))))).
:- endif.
:- if(current_prolog_flag(xref,true)).
:- module(pfc_header,[]).
:- endif.
:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
:- prolog_load_context(file,File),unload_file(File).
:- endif.
:- if( \+  current_prolog_flag(xref,true)).
:- use_module(library(logicmoo_utils_all)).
:- must(retract(baseKB:'wusing_pfc'(M,CM,SM,pfc_header))),
   wdmsg(baseKB:'chusing_pfc'(M,CM,SM,pfc_header)),
   (M==SM -> 
     (SM:consult('pfc3.0/pfc_rt'),nop(maybe_ensure_abox(SM)),nop((M:ain(genlMt(SM,baseKB)))));
     wdmsg(baseKB:'lusing_pfc'(M,CM,SM,pfc_header))),   
   assert(baseKB:'$using_pfc'(M,CM,SM,pfc_header)),
   asserta(SM:'$does_use_pfc_mod'(M,CM,SM,pfc_header)).
   %backtrace(200).
   
%:- set_prolog_flag(retry_undefined, kb_shared).
%:- set_prolog_flag(pfc_ready, true).
:- set_prolog_flag(expect_pfc_file,unknown).
:- endif.

