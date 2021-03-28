%% This is example2.clp from Luke Simon's thesis, with some tweaks.

:- [ colp ].   % Load the metainterpreter



% A number.
:- dynamic num/1 .

num( 0 ).
num( s( N ) ) :-  num( N ).


% A stream of numbers.
:- dynamic stream/1 .
coinductive( stream( _ ) ).

stream( [ H | T ] ) :-  num( H ),  stream( T ).



% Similar to append/3.
:- dynamic append1/3 .
coinductive( append1( _, _, _ ) ).

append1( [], X, X ).
append1( [ H | T ], Y, [ H | Z ] ) :-  append1( T, Y, Z ).


% Similar to member/2.
:- dynamic( member1/2 ).
coinductive( member1( _, _ ) ).

member1( X, [ X | _ ] ).
member1( X, [ _ | T ] ) :-  member( X, T ).


% Ditto, but not coinductive
:- dynamic( member2/2 ).

member2( X, [ X | _ ] ).
member2( X, [ _ | T ] ) :-  member( X, T ).


% Drop some prefix of arg2 upto an "occurrence" of arg1 from arg2,
% yielding arg3.
% ("Occurrence" of X = something unifiable with X.)
:- dynamic( drop/3 ).

drop( H, [ H | T ] , T  ).
drop( H, [ _ | T ] , T1 ) :-  drop( H, T, T1 ).


% Are there infinitely many "occurrences" of arg1 in arg2?
:- dynamic( comember/2 ).
coinductive( comember( _, _ ) ).

comember( X, L ) :-  drop( X, L, L1 ),  comember( X, L1 ).
