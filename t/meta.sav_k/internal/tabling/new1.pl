%% Implements Gopal Gupta's new idea based on "commutative conjunction".
%% This is just an experimental, "proof of concept" interpreter, so it is very
%% inefficient.

:- ensure_loaded( '../general/top_level' ).
:- ensure_loaded( '../general/utilities' ).



builtin( \+( _ )            ).  % special treatment in solve/3
builtin( _ < _              ).
builtin( _ = _              ).
builtin( _ =< _             ).
builtin( _ > _              ).
builtin( _ >= _             ).
builtin( _ \= _             ).
builtin( _ is _             ).
builtin( atom( _ )          ).
builtin( call( _ )          ).
builtin( fail               ).
builtin( false              ).
builtin( member( _, _ )     ).
builtin( nl                 ).
builtin( once( _ )          ).  % special treatment in solve/3
builtin( read( _ )          ).
builtin( true               ).
builtin( var( _ )           ).
builtin( write( _ )         ).
builtin( write_term( _, _ ) ).
builtin( writeln( _ )       ).
builtin( set_print_depth( _, _ )   ).      % not a real built-in, see  top_level


%% Hooks for the top_level:

default_extension( '.pl' ).

hook_predicate( '' ).


:- dynamic rule/2.

initialise :-
        retractall( rule( _, _ ) ).

program_loaded :-
        transform_program.

query( Goals ) :-
        transform_body( Goals, GoalList - [] ),
        write( 'Query: ' ),  writeln( GoalList ),
        solve( GoalList, [] ).



%% Transform the program: each clause is converted so that its body is a d-list,
%% and then asserted in rule/2.
%% For example:
%%    anc( X, Y ) :- anc( X, Z ), p( Z, Y ).
%% will be stored as
%%    rule( anc( X, Y ), [ anc( X, Z ), p( Z, Y ) | End ] - End ).

transform_program :-
        current_predicate_in_module( interpreted, P / K ),
        mk_pattern( P, K, Head ),
        \+ builtin( Head ),
        clause_in_module( interpreted, Head, Body ),
        transform_body( Body, DList ),
%        writeln( asserting( rule( Head, DList ) ) ),
        assertz( rule( Head, DList ) ),
        fail.

transform_program.


%% transform_body( + (part of) clause body, - d-list ):
%% For the time being we don't handle disjunctions and conditionals.

transform_body( true, End - End ) :-
        !.

transform_body( (_ ; _), _ ) :-
        !,
        error( 'Cannot handle disjunctions yet' ).

transform_body( (_ -> _), _ ) :-
        !,
        error( 'Cannot handle conditionals yet' ).

transform_body( ((A , B), C), DL ) :-
        !,
        transform_body( (A , (B , C)), DL ).

transform_body( (A , B), DL ) :-
        !,
        transform_body( A, DLA - AEnd ),
        transform_body( B, DLB - BEnd ),
        AEnd = DLB,
        DL = DLA - BEnd.

transform_body( A, [ A | End ] - End ).



%% solve( + current goal, + current stack ):

solve( [], _ ) :-                                                     % success
        !,
        optional_trace( '.. success' ).

solve( [ G | Gs ], Stack ) :-
        builtin( G ),          % have to change if we are to coroutine built-ins
        !,
        optional_trace( '.. invoking builtin'( G ) ),
        call( G ),
        solve( Gs, Stack ).

solve( Goals, Stack ) :-
        append( PrefixOfVariants, [ Goal | Gs ], Goals ),
        \+ is_variant_of_ancestor( Goal, Stack ),
        append( Gs, PrefixOfVariants, NewGoals ),
        copy_term( Goal, OriginalGoal ),
        (
            optional_trace( '.. entering'( Goal ) )
        ;
            optional_trace( '.. failing'( Goal ) ),
            fail
        ),
        rule( Goal, Body - NewGoals ),           % i.e, Body = the new resolvent
        (
            optional_trace( '.. new resolvent'( Body ) )
        ;
            optional_trace( '.. retrying'( OriginalGoal ) ),
            fail
        ),
        solve( Body, [ OriginalGoal | Stack ] ).

solve( Goals, _ ) :-
        optional_trace( '.. failing: variants only'( Goals ) ),
        fail.



%% is_variant_of_ancestor( + goal, + stack ):
%% Is the goal a variant of something in the stack?

is_variant_of_ancestor( Goal, Stack ) :-
        member( G, Stack ),
        are_variants( G, Goal ),
        !.


%%%%%%%%
:- dynamic tracing/0.

optional_trace( X ) :-
        tracing,
        !,
        writeln( X ).

optional_trace( _ ).


legal_directive( trace   ).
legal_directive( notrace ).


execute_directive( trace ) :-
        assert( tracing ).

execute_directive( notrace ) :-
        retract( tracing ),
        !.
execute_directive( notrace ).
