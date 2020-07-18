/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/

:- if((current_prolog_flag(pfc_version,2.0),reexport(pfc_lib_2_0))).
:- endif.

:- if(\+ current_prolog_flag(xref,true)).

:- if(('$current_source_module'(SM),
       SM:use_module(library(logicmoo_utils)),
       SM:use_module(library(pfc_iri_resource)),
       add_pfc_to_module(SM))).
:-else. % add_pfc_to_module
% Bad!
   :- if(('$current_typein_module'(TM),'$current_source_module'(SM),'context_module'(CM),Info = ('FAILED'(TM,SM,CM,pfc_mod)),
         dmsg(Info),throw(Info))).
   :- endif.
:- endif. % add_pfc_to_module
:- endif. % \+ current_prolog_flag(xref,true)

:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
:- module(pfc_mod,[]).
:- prolog_load_context(file,File),unload_file(File).
:- endif. % Sourced directly

:- if(current_prolog_flag(xref,true)).
:- include(library('pfc3.0/pfc_3_0_full')).
:- else.
:- check:list_undefined.
:- endif.

