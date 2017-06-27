/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- module(pfc_toplevel,['$uses_pfc_toplevel'/0]).
'$uses_pfc_toplevel'.
:- current_predicate(M:'$uses_pfc_toplevel'/0), reexport(M:pfc).
:- reexport(pfc).     
:- set_prolog_flag(mpred_te,true).
:- set_prolog_flag(verbose_load,true).
:- set_prolog_flag(debug_on_error,true).
:- set_prolog_flag(report_error,true).


