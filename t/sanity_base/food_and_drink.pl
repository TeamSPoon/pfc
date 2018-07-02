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
wants(Person,Type,Amount):- 
  buyable(Type2),
  person(Person),
  wants(Person,Type2,Other),
  Type2\==Type2, 
  Amount is 1.0 - Other.

wants_more(P,Thing1):- 
   dif(Thing1,Thing2),
   wants(P,Thing1,A1),
   wants(P,Thing2,A2),
   A1>A2.

happy:-
   dif(P1,P2),
   wants_more(P1,Thing1),
   wants_more(P2,Thing2),
   cost(Thing1,Cost1),
   cost(Thing2,Cost2),
   has(P1,money,Cash),
   Cash #=< 
     Cost1+Cost2, 
   nl,
   write([
     orders_for(Thing1,P1),
     orders_for(Thing2,P2)]),nl.

   





