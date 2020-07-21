/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if((\+ current_prolog_flag(xref,true), ('$current_source_module'(SM),context_module(CM),'$current_typein_module'(TM),
  (Info='using_pfc'(SM,TM,CM,pfc_mod)), /*writeln(Info),*/asserta(baseKB:Info)))).
:- endif.
:- module(pfc_mod, [hello_there_xref/0, add_pfc_to_module/3]).
:- set_module(class(library)).
:- use_module(library(logicmoo_utils)).
%:- use_module(library(pfc_iri_resource)).


add_pfc_to_module(SM,TM,CM):- 
   Info = 'using_pfc'(SM,TM,CM,pfc_load),
   '$current_typein_module'(CTM),
   '$current_source_module'(CSM),
   %'context_module'(CCM),
   '$set_typein_module'(TM),
   '$set_source_module'(SM),   
   %dmsg(add_pfc_to_module(Info,CSM,CTM)), 
   %include_pfc_res(Module,PfcInclFile),
   %asserta(Module:'$does_use_pfc'(Module,PfcInclFile,Info)),
   % Version 2.0
   %SM:use_module( library(logicmoo_utils)),
   %SM:use_module( library(pfc_iri_resource)),
   SM:reexport(library(pfc_lib)),
   wdmsg(add_pfc_to_module(Info)),
   maybe_ensure_abox(SM),
   asserta(baseKB:Info),
   '$set_typein_module'(CTM),
   '$set_source_module'(CSM),!,
   !.

%! hello_there_xref is det.
% 
%  This is seen by XREF 
%
hello_there_xref.

:- dynamic(lmcache:pfc_mod_filename/1).
:- volatile(lmcache:pfc_mod_filename/1).
:- dynamic(lmcache:pfc_decl_filename/1).
:- volatile(lmcache:pfc_decl_filename/1).

:- lmcache:pfc_mod_filename(File) -> true ;
   prolog_load_context(file,File), asserta(lmcache:pfc_mod_filename(File)).

:- module_transparent(pfc_load_file/2).
% for loading wildcards
pfc_load_file(Module:Spec, Options):- fail, 
   \+ exists_source(Spec),
   findall(SpecO,(logicmoo_util_filesystem:filematch(Module:Spec,SpecO),exists_file(SpecO)),SpecOList),!,
   SpecOList\==[], !, 
   forall(member(SpecO,SpecOList),load_files(Module:SpecO, Options)),!.

:- multifile(user:prolog_load_file/2).
:- dynamic(user:prolog_load_file/2).      

%! prolog_load_file( ?ModuleSpec, ?Options) is semidet.
%
% Hook To [user:prolog_load_file/2] For PFC Modules
% Prolog Load File.
%
user:prolog_load_file(ModuleSpec, Options):- pfc_load_file(ModuleSpec, Options),!.
user:prolog_load_file(ModuleSpec, Options):-
  '$current_typein_module'(TM),
  strip_module(ModuleSpec,Module,Spec),
  (exists_source(Spec, Path)->true;Path=Spec),    
  (lmcache:pfc_mod_filename(Path);(atom(Path),sub_string(Path, _, _, _, '.pfc'));lmcache:pfc_decl_filename(Path)),
  % wdmsg(pfc_load_file(sm=Module,tm=TM,path=Path,opts=Options)),
  select(if(not_loaded),Options,Removed),!,
  TM:load_files(Module:Spec,[if(always)|Removed]).
%user:prolog_load_file(_,_):- get_lang(pl),!,fail.
%user:prolog_load_file(_,_):- set_file_lang(pl),set_lang(pl),fail.


:- if(current_prolog_flag(xref,true)).
:- reexport(library(pfc_lib)).
:- endif.

:- retract(baseKB:'using_pfc'(SM,TM,CM,pfc_mod)) -> add_pfc_to_module(SM,TM,CM); true.





%:- if((prolog_load_context(file,File),unload_file(File))). 
%:- endif.

%:- if((prolog_load_context(source,File),prolog_load_context(file,File))).
%:- endif.
%:- endif. % Sourced directly
%:- pldoc_http:import(prolog_edit:edit/1).
%:- check:list_undefined.
