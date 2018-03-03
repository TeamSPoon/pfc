/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(current_prolog_flag(xref,true)).

:- module(pfc_mod,[use_pfc_mod/0]).
use_pfc_mod.

:- else.

:- if(('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod)))).
:- endif.

:- if((prolog_load_context(file,X),prolog_load_context(source,X))).
 :- module(pfc_mod,[use_pfc_mod/0]).
 :- abolish(use_pfc_mod/0).
 :- prolog_load_context(file,File),unload_file(File).
 :- asserta(use_pfc_mod).
:- endif.

:- if(\+ current_prolog_flag(lm_pfc_lean,_)).
:- set_prolog_flag(lm_no_autoload,true).
:- set_prolog_flag(lm_pfc_lean,true).
:- wdmsg("WARNING: PFC_LEAN").
:- endif.


:- if(current_prolog_flag(pfc_version,2.2)).
:- reexport(pfc_lib_2_2).
:- else.
:- if(current_prolog_flag(pfc_version,1.2)).
:- reexport(pfc_lib_1_2).
:- else.
:- reexport(pfc_lib).
:- endif.
:- endif.

:- ensure_loaded(library(file_scope)).
:- set_prolog_flag_until_eof(debug_on_error,true).
:- set_prolog_flag_until_eof(report_error,true).
:- set_prolog_flag_until_eof(access_level,system).
:- set_prolog_flag_until_eof(verbose_load,true).

:- retract(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod)),
   (M==SM -> 
     (maybe_ensure_abox(SM),nop((M:ain(genlMt(SM,baseKB)))));
     wdmsg(baseKB:'lusing_pfc'(M,CM,SM,pfc_mod))),
   assert(baseKB:'using_pfc'(M,CM,SM,pfc_mod)).

:- retractall(t_l:disable_px).
:- set_prolog_flag(mpred_te,true).
:- baseKB:ensure_loaded('pfclib/system_autoexec.pfc').
:- set_prolog_flag(pfc_booted,true).
:- set_prolog_flag(pfc_ready, true).

:- statistics.

:- set_prolog_flag(retry_undefined, kb_shared).

:- endif.  % xref

