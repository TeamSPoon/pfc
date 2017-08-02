
%:- mpred_unload_file.
:- set_fileAssertMt(baseKB).

% asserting mpred_sv(p,2) causes p/2 to be treated as a mpred_sv, i.e.
% if p(foo,1)) is a fact and we assert_db p(foo,2), then the forrmer assertion
% is retracted.
% prologSingleValued(Pred)
:-kb_local(baseKB:mpred_sv/2).
arity(mpred_sv,2).
mpred_sv(Pred,Arity)==> arity(Pred,Arity),hybrid_support(Pred,Arity),singleValuedInArg(Pred,Arity).

:- dynamic(mpred_sv_shared/1).
mpred_sv_shared(Pred,Arity)==>{kb_local(Pred/Arity)},mpred_sv(Pred,Arity).
mpred_sv_shared(mpred_sv,2).
mpred_sv_shared(singleValuedInArg,2).
mpred_sv_shared(singleValuedInArgDefault,3).

prologSingleValued(Pred), arity(Pred,Arity), \+ singleValuedInArg(Pred,_) ==> singleValuedInArg(Pred,Arity).

% prologSingleValued(Pred),arity(Pred,Arity) ==> hybrid_support(Pred,Arity).
% mdefault(((prologSingleValued(Pred),arity(Pred,Arity))==> singleValuedInArg(Pred,Arity))).
% singleValuedInArg(singleValuedInArg,2).

% TODO might we say this?
% Not really due to not every SingleValued pred have a cardinatity of 1 .. some might have no instances
% ((singleValuedInArg(Pred,N)/ ( \+ singleValuedInArgDefault(Pred,N,_))) ==> singleValuedInArgDefault(Pred,N,isMissing)).


arity(singleValuedInArgDefault, 3).
prologHybrid(singleValuedInArgDefault(prologSingleValued,ftInt,ftTerm)).

((singleValuedInArg(Pred,_))==>(prologSingleValued(Pred))).

(singleValuedInArgDefault(SingleValued,ArgN,S1)/ground(S1) ==> singleValuedInArg(SingleValued,ArgN)).

((singleValuedInArg(F, N)/must(atom(F))), arity(F,A), 
  ( \+ singleValuedInArgDefault(F, N, Q_SLOT),
   {functor(P,F,A),arg(N,P,P_SLOT),replace_arg(P,N,Q_SLOT,Q)}))
       ==> (( P ==> 
          {dif:dif(Q_SLOT,P_SLOT), call_u(Q), ground(Q)}, \+Q, P)).













end_of_file.


:- if((fail,flag_call(runtime_debug == true) ;baseKB:startup_option(datalog,sanity);baseKB:startup_option(clif,sanity))).

:- ensure_loaded(pack(logicmoo_base/t/examples/pfc/'sanity_sv.pfc')).

:- endif.





% This would been fun! singleValuedInArgDefault(singleValuedInArgDefault,3,isMissing).

compilerDirective(somtimesBuggyFwdChaining,comment("Can sometimes be buggy when FwdChaining")).
compilerDirective(somtimesBuggyBackChaining,comment("Can sometimes be buggy when BackChaining")).
compilerDirective(somtimesBuggy,comment("Can sometimes be buggy")).

((somtimesBuggyFwdChaining==> ((
  ((singleValuedInArgDefault(P, 2, V), arity(P,2), argIsa(P,1,Most)) ==> relationMostInstance(P,Most,V)))))).


(somtimesBuggyFwdChaining==>
 ({FtInt=2},singleValuedInArgDefault(PrologSingleValued,FtInt,FtTerm),arity(PrologSingleValued,FtInt),
  argIsa(PrologSingleValued,1,Col)==>relationMostInstance(PrologSingleValued,Col,FtTerm))).

somtimesBuggyBackChaining ==> (((singleValuedInArgDefault(F, N, Q_SLOT)/is_ftNonvar(Q_SLOT), arity(F,A),
   {functor(P,F,A),replace_arg(P,N,Q_SLOT,Q),replace_arg(Q,N,R_SLOT,R)})
       ==> mdefault( Q <- ({ground(P)},~R/nonvar(R_SLOT))))).

(((singleValuedInArg(F, N), arity(F,A), \+ singleValuedInArgDefault(F, N, Q_SLOT),
   {functor(P,F,A),arg(N,P,P_SLOT),replace_arg(P,N,Q_SLOT,Q)})
       ==> (( P ==> 
          {dif:dif(Q_SLOT,P_SLOT), call_u(Q), ground(Q)}, \+Q, P)))).

sometimesBuggy==>((singleValuedInArgDefault(P, 2, V), arity(P,2), argIsa(P,1,Most)) <==> relationMostInstance(P,Most,V)).


