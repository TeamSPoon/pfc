p( X, Y ) :-  q( X ),  q( Y ).


q( a ) :- p( X, Y ).

q( b ).


% ?- p( X, Y ).  % expected:  p( b, b ),  p( a, a ),  p( a, b ),  p( b, a )
