/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(( current_prolog_flag(xref,true) ;
   ('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod))))).
:- endif.
:- module(pfc_mod,[use_pfc_mod/0]).
:- abolish(use_pfc_mod/0).
:- prolog_load_context(file,File),unload_file(File).
:- asserta(use_pfc_mod).


:- if( \+ current_prolog_flag(xref,true)).


:- if(\+ current_prolog_flag(lm_pfc_lean,_)).
:- set_prolog_flag(lm_no_autoload,true).
:- set_prolog_flag(lm_pfc_lean,true).
:- endif.

:- set_prolog_flag(debug_on_error,true).
:- set_prolog_flag(report_error,true).
:- set_prolog_flag(access_level,system).
:- reexport(pfc_lib).     
:- set_prolog_flag(mpred_te,true).
:- set_prolog_flag(verbose_load,true).

:- retract(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod)),
   (M==SM -> 
     (maybe_ensure_abox(SM),nop((M:ain(genlMt(SM,baseKB)))));
     wdmsg(baseKB:'lusing_pfc'(M,CM,SM,pfc_mod))),
   assert(baseKB:'using_pfc'(M,CM,SM,pfc_mod)).

:- set_prolog_flag(retry_undefined, kb_shared).



:- endif.
