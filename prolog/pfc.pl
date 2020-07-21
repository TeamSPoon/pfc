/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
/*:- if(current_prolog_flag(xref,true)).

% All XRef sees:
:- module(pfc_mod,[hello_there_xref/0]).

:- rexport(library(pfc_lib)).

%! hello_there_xref is det.
% 
%  This is only seen by XREF 
%
hello_there_xref.

:- else.  % \+ current_prolog_flag(xref,true)
*/
:- if(('$current_source_module'(M),
      M:use_module( library(logicmoo_utils)),
      M:use_module( library(pfc_iri_resource)),
      add_pfc_to_module(M))).
/*
:-else. % add_pfc_to_module
% Bad!
   :- if(('$current_typein_module'(TM),'$current_source_module'(SM),'context_module'(CM),Info = ('FAILED'(TM,SM,CM,pfc_mod)),
         dmsg(Info),throw(Info))).
*/
:- endif. % add_pfc_to_module

:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
 :- module(pfc_mod,[]).
:- endif. 

%  Makes this load multiple times (per use_module)
:- prolog_load_context(file,File),unload_file(File).

%:- endif. % current_prolog_flag(xref,true)
