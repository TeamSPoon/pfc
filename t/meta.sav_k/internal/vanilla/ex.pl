:- dynamic p/1, b/1, q/2, r/1.

p( a ) :-  b( a ).
p( X ) :-  q( X, Y ),  r( Y ).

b( _ ).

q( X, X ).

r( b ).
