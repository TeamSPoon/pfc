/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(( current_prolog_flag(xref,true) ;
   ('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod))))).
:- endif.

:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
:- module(pfc_mod,[use_pfc_mod/0]).
:- abolish(use_pfc_mod/0).
:- prolog_load_context(file,File),unload_file(File).
:- asserta(use_pfc_mod).
:- endif.

% :- current_predicate(system:F/A),functor(PI,F,A),
% \+ predicate_property(system:PI,imported_from(_)).

:- if( \+ current_prolog_flag(xref,true)).


:- if(\+ current_prolog_flag(lm_no_autoload,_)).
:- set_prolog_flag(lm_no_autoload,true).
:- wdmsg("WARNING: PFC_NOAUTOLOAD").
:- endif.

:- if(\+ current_prolog_flag(lm_pfc_lean,_)).
:- set_prolog_flag(lm_pfc_lean,true).
:- wdmsg("WARNING: PFC_LEAN").
:- endif.

%:- set_prolog_flag(debug_on_error,true).
%:- set_prolog_flag(report_error,true).
:- baseKB:'wusing_pfc'(_M,_CM,SM,pfc_mod),SM:reexport(pfc_lib).
:- set_prolog_flag(mpred_te,true).

:- must(retract(baseKB:'wusing_pfc'(M,CM,SM,pfc_mod))),
   show_wdmsg(baseKB:'chusing_pfc'(M,CM,SM,pfc_mod)),
   (M==SM -> 
     (maybe_ensure_abox(SM),nop((M:ain(genlMt(SM,baseKB)))));
     show_wdmsg(baseKB:'lusing_pfc'(M,CM,SM,pfc_mod))),   
   assert(baseKB:'using_pfc'(M,CM,SM,pfc_mod)).
   
:- baseKB:ensure_loaded('pfclib/system_autoexec.pfc').
:- set_prolog_flag(pfc_booted,true).

:- set_prolog_flag(retry_undefined, kb_shared).
:- set_prolog_flag(pfc_ready, true).

:- endif.
%:- statistics.

