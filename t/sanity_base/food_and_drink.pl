/*

Joe is takin Sue on a date but he doesnt have enough money to buy them both food and drink

Joe wants food more than a drink.
Sue wants to get a drink and has no thoughts about food.

*/


cost(food,35.0).
cost(drink,15.0).

buyable(A):- cost(A,_).
person(P):- wants(P,_,_).

has(joe,money,40.0).

has(joe,food,0.0).
has(joe,drink,0.0).
has(sue,food,0.0).
has(sue,drink,0.0).

wants(joe,food,0.33).
wants(joe,drink,0.66).
wants(sue,drink,0.66).

% This rule helps us infer sue wants  food at .34
wants(Person,Type1,Amount):- 
  dif(Type1,Type2), 
  buyable(Type2),
  person(Person),
  wants(Person,Type2,Other),
  Amount #= 1.0 - Other.

wants_more(P,Thing1):- 
   dif(Thing1,Thing2),
   wants(P,Thing1,A1),
   wants(P,Thing2,A2),
   A1 #>= A2.


do_test :-
   dif(P1,P2),
   wants_more(P1,Thing1),
   wants_more(P2,Thing2),
   cost(Thing1,Cost1),
   cost(Thing2,Cost2),
   has(P1,money,Cash),
   Cash #>= Cost1+Cost2, 
   nl,
   write([
     orders_for(Thing1,P1),
     orders_for(Thing2,P2)]),nl.



wants_more_arity_2(P,Thing1):- 
   dif(Thing1,Thing2),
   pred(F1,wants),arg1(F1,P),arg2(F1,Thing1),arg3(F1,A1),
   pred(F2,wants),arg1(F2,P),arg2(F2,Thing2),arg3(F2,A2),
   A1>A2.



pred(ClNum,Prd):- clauzes(P,ClNum),functor(P,Prd,_).
arg1(ClNum,Arg):- clauzes(P,ClNum),arg(1,P,Arg).
arg2(ClNum,Arg):- clauzes(P,ClNum),arg(2,P,Arg).
arg3(ClNum,Arg):- clauzes(P,ClNum),arg(3,P,Arg).

clauzes(P,ClNum):- arity_was(F,A),functor(P,F,A),clause(P,true,ClNum).



:- do_test.







