/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'using_pfc'(M,CM,SM,pfc_toplevel)))).
:- endif.
:- module(pfc_toplevel,[use_pfc/0]).
% :- abolish(use_pfc/0).
% :- prolog_load_context(file,File),unload_file(File).
% :- asserta(use_pfc).

use_pfc.


:- if(\+ current_prolog_flag(lm_pfc_lean,_)).
:- set_prolog_flag(lm_no_autoload,false).
:- set_prolog_flag(lm_pfc_lean,false).
:- endif.

:- reexport(pfc).     
:- set_prolog_flag(mpred_te,true).
:- set_prolog_flag(verbose_load,true).
:- set_prolog_flag(debug_on_error,true).
:- set_prolog_flag(report_error,true).
:- set_prolog_flag(access_level,system).
:- statistics.

:- retract(baseKB:'wusing_pfc'(M,CM,SM,pfc_toplevel)),
   assert(baseKB:'using_pfc'(M,CM,SM,pfc_toplevel)),
   (M==SM -> 
     (ensure_abox(SM),ain(genlMt(SM,baseKB)));
     wdmsg(baseKB:'lusing_pfc'(M,CM,SM,pfc_toplevel))).

