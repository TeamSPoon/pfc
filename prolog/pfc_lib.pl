:- if(('$current_source_module'(SM),'context_module'(M),'$current_typein_module'(CM),asserta(baseKB:'using_pfc'(M,CM,SM,pfc_lib)))).
:- endif.

:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
:- module(pfc_lib,[]).
:- occurs:use_module(library(occurs),[sub_term/2]).
/*
:- use_module(library(random)).
:- use_module(library(error)).
:- use_module(library(threadutil)).
:- use_module(library(edit)).
:- autoload_all.
*/
:- endif.

% :- set_prolog_flag(pfc_version,2.2).

:- if(current_prolog_flag(pfc_version,2.2)).
:- include(pfc_lib_2_2).
:- else.
:- if(current_prolog_flag(pfc_version,1.2)).
:- include(pfc_lib_1_2).
:- else.
:- if((current_prolog_flag(pfc_version,Was),Was\==2.0)).
:- baseKB:use_module(library(pfc)).
:- else.
% this is 2.0
:- set_prolog_flag(pfc_version,2.0).
:- include(pfc_lib_2_0).
:- endif.
:- endif.
:- endif.

