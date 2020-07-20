
% ===================================================
fixundef_call(G):- format(string(Out),'% Need   ~q.~n',[:- G]), wdmsg(Out), (ground(G)->call(G) ; true).

module_of_pred(F/A,M,File):- current_module(M),
  current_predicate(M:F/A), functor(P,F,A), \+ predicate_property(M:P,imported_from(_)),!,
  ignore(source_file(M:P,File)).

fixundef([]):-!.                                                       
fixundef([H|T]):- fixundef(H),fixundef(T).
fixundef(((M1:F2/A2) - Refs)):- !, %  clause_property(Ref,module(M1)), %  clause_property(Ref,predicate(P1)),
   P2 = F2/A2,fixundef(undef(M1:P2,Refs)).

fixundef(Info):-    
   Info = undef(M1:P2,_Refs),
   (module_of_pred(P2,M2,File2) ->
     maplist(fixundef_call,[M2:export(M2:P2),M1:import(M2:P2),M1:autoload(File2,[P2])]);
     (format(string(Out),'% ~q~n',[undef(M1:P2)]),wdmsg(Out),assert_if_new(fixundef_later(Info)))).

fixundef_later:- forall(retract(fixundef_later(M1P2)),fixundef(M1P2)),check:list_undefined.

:- dynamic message_hook/3.
:- multifile message_hook/3.
:- module_transparent message_hook/3.

user:message_hook(check(undefined_procedures,List),_Type,_Warn):-
   once(fixundef(List)),
   fail.
% ===================================================

:- include(library('pfc2.0/mpred_at_box.pl')).
:- include(library('pfc2.0/mpred_justify.pl')).
:- include(library('pfc2.0/mpred_core.pl')).
%:- include(library('pfc2.0/mpred_gvars.pl')).
:- include(library('pfc2.0/mpred_expansion.pl')).
:- include(library('pfc2.0/mpred_loader.pl')).
:- include(library('pfc2.0/mpred_database.pl')).
:- include(library('pfc2.0/mpred_listing.pl')).
%:- include(library('pfc2.0/mpred_prolog_file.pl')).
:- include(library('pfc2.0/mpred_terms.pl')).

:- fixup_exports.


