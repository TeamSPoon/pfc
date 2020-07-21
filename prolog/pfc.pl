/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if(set_prolog_flag(pfc_version,2.0)).
:- endif.
:- if(\+ current_prolog_flag(xref,true)).

:- if(('$current_source_module'(M),
      M:use_module( library(logicmoo_utils)),
      M:use_module( library(pfc_iri_resource)),
      M:reexport(library(pfc_lib)),
      % M:include_into_module(library('pfc2.0/pfc_2_0_includes'),M),
      add_pfc_to_module(M))).
:-else. % add_pfc_to_module
% Bad!
   :- if(('$current_typein_module'(TM),'$current_source_module'(SM),'context_module'(CM),Info = ('FAILED'(TM,SM,CM,pfc_mod)),
         dmsg(Info),throw(Info))).
   :- endif.
:- endif. % add_pfc_to_module
:- endif. % \+ current_prolog_flag(xref,true)

:- if((prolog_load_context(source,File),prolog_load_context(file,File),unload_file(File))).
:- module(pfc_mod,
  [hello_there_xref/0]).
%! hello_there_xref is det.
% 
%  This is only seen by XREF 
%
hello_there_xref.
:- endif. % Sourced directly

:- if(current_prolog_flag(xref,true)).
:- rexport(library('pfc_lib')).
:- else.
%:- pldoc_http:import(prolog_edit:edit/1).
%:- check:list_undefined.
:- endif.
