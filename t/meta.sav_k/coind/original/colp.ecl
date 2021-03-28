%%%                                                                     %%%
%%% A meta-interpreter for co-logic programming.                        %%%
%%% This is just "colp.pro" by Luke Evans Simon, with a few tweaks.     %%%
%%%                                                                     %%%

%%% NOTE: The metainterpreter should be loaded together with an example,
%%%       see any of the *.clp files in this directory.
%%%       The following rules must be observed:
%%%        - All the predicates defined a program should be declared as dynamic
%%%          (e.g.,  ":- dynamic comember/2." ).
%%%        - All the built-in predicates used by a program should be listed in
%%%          the predicate builtin/1 
%%%          (e.g.,  "builtin( atomic( _ ) )." ).
%%%        - All the coinductive predicates of a program should be listed in
%%%          the predicate coinductive/1 
%%%          (e.g., "coinductive( comember( _, _ )." ).
%%%
%%%       A query should take the form
%%%         ?- query( (a, b, ... ) ).


:-dynamic coinductive/1 .
:-dynamic builtin/1 .


builtin( true ).
builtin( =( _, _ ) ).



% Execute a query.
query( Goal ) :- solve( [], Goal ).


%% Solve a goal, given this table of co-inductive hypotheses.
%% NOTE: if-then-else or disjunction not supported.

% General goal:

solve( Hypotheses, ( Goal1 , Goal2 ) ) :-       % a conjunction
        !,
        solve( Hypotheses, Goal1 ),
        solve( Hypotheses, Goal2 ).

solve( Hypotheses, Call ) :-                    % a single call
        solve_call( Hypotheses, Call ).


% A single call:

solve_call( _, Call ) :-
        builtin( Call ),
        Call .
            
solve_call( Hypotheses, Call ) :-
        coinductive( Call ),
        member( Call, Hypotheses ).

solve_call( Hypotheses, Call ) :-
        coinductive( Call ),
        clause( Call, Body ),
        solve( [ Call | Hypotheses ], Body ).

solve_call( Hypotheses, Call ) :-
        \+ builtin( Call ),
        \+ coinductive( Call ),
        clause( Call, Body ),
        solve( Hypotheses, Body ).


