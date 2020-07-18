/*   
  LogicMOO Base FOL/PFC Setup
% Dec 13, 2035
% Douglas Miles

*/
:- if((prolog_load_context(source,File), \+ prolog_load_context(file,File))).
:- if((use_module(library(logicmoo_utils)))).
:- endif.
:- if((reexport(library(logicmoo_utils)))).
:- endif.
:- if(\+ current_prolog_flag(xref,true)).
:- if(('$current_typein_module'(TM),'$current_source_module'(SM),'context_module'(CM),Info = (baseKB:'using_pfc'(TM,SM,CM,pfc_header)),
   dmsg(Info), 

   % Version 3.0
   absolute_file_name(library('pfc3.0/pfc_3_0_full'),FN,[access(read),file_type(prolog)]),
   open(FN,read,Input), atomic_list_concat([FN,'_local_',SM],FakeName),
   asserta(SM:'$does_use_pfc_lib'(FakeName,Info)),
   SM:load_files(FakeName,[module(SM),if(always),stream(Input),must_be_module(false),reexport(true),silent(false)]),

   % Version 2.0
   % SM:reexport(pfc_lib_2_0),

   maybe_ensure_abox(SM),
   asserta(Info))).

% All good!
 :-else.
   :- if(('$current_typein_module'(TM),'$current_source_module'(SM),'context_module'(CM),Info = (baseKB:'FAILED'(TM,SM,CM,pfc_header)),
      dmsg(Info))).

      :- '$current_typein_module'(TM2),'$current_source_module'(SM2),'context_module'(CM2),
         print_message(error,failed_pfc_load(TM2,SM2,CM2,pfc_header)).

   :-endif. % FAILED
:- endif. % maybe_ensure_abox
:- endif. % \+ XREF

:- endif.

