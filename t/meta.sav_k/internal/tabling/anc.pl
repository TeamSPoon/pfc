parent( a, b ).
parent( b, c ).
parent( c, d ).

%parent( b, d ).
%parent( c, e ).
%parent( d, f ).

anc( X, Y ) :-  anc( X, Z ), anc( Z, Y ).
anc( X, Y ) :-  parent( X, Y ).
