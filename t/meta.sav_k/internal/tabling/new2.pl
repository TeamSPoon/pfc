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


:- dynamic rule/3.

initialise :-
        retractall( rule( _, _, _ ) ).

program_loaded :-
        transform_program.

query( Goals ) :-
        transform_body( Goals, GoalList - [] ),
        write( 'Query: ' ),  writeln( GoalList ),
        solve( GoalList, [] ).



%% Transform the program: each clause is converted so that its body is a d-list,
%% and then asserted in rule/3, together with a number unique for the predicate.
%% For example,
%%    anc( X, Y ) :- anc( X, Z ), p( Z, Y ).
%% will be stored as
%%    rule( anc( X, Y ), [ anc( X, Z ), p( Z, Y ) | End ] - End, 0 ).
%% (assuming this is the first clause of anc/2).

transform_program :-
        current_predicate_in_module( interpreted, P / K ),
        mk_pattern( P, K, Head ),
        \+ builtin( Head ),
        setval( clause_counter, 0 ),
        clause_in_module( interpreted, Head, Body ),
        transform_body( Body, DList ),
        getval( clause_counter, N ),
%        writeln( asserting( rule( Head, DList, N ) ) ),
        assertz( rule( Head, DList, N ) ),
        incval( clause_counter ),
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

% If the resolvent starts with a non-empty prefix of variant goals, but there
% is at least one "regular" goal, postpone the variants and execute the first
% "regular".  However, make sure that we do not execute built-ins until they are
% leftmost "of natural causes".
solve( Goals, Stack ) :-
        append( PrefixOfVariants, [ Goal | Gs ], Goals ),
        ( \+ is_variant_of_ancestor( Goal, Stack, _ )
        ,
          ( \+ builtin( Goal )
          ;
            PrefixOfVariants = []
          )
        ),
        !,
        append( Gs, PrefixOfVariants, NewGoals ),
        copy_term( Goal, OriginalGoal ),
        (
            true
        ;
            optional_trace( '.. failing'( Goal ) ),
            fail
        ),
        rule( Goal, Body - NewGoals, N ),        % i.e, Body = the new resolvent
        (
            optional_trace( '.. entering at clause'( Goal, [ N ] ) ),
            optional_trace( '.. new resolvent'( Body ) )
        ;
            optional_trace( '.. retrying'( OriginalGoal ) ),
            fail
        ),
        solve( Body, [ pair( OriginalGoal, [ N ] ) | Stack ] ).

% All the goals are variants: execute the first one that has clauses unexplored
% by variant ancestors, postponing those that precede it, but
% don't have such claues.
solve( Goals, Stack ) :-
        append( PrefixOfExhaustedVariants, [ Goal | Gs ], Goals ),
        (
            is_variant_of_ancestor( Goal, Stack, AncSet ),
            copy_term( Goal, Copy ),
            rule( Copy, _, N ),
            \+ is_in_set( N, AncSet )
        ),
        !,
        append( Gs, PrefixOfExhaustedVariants, NewGoals ),
        copy_term( Goal, OriginalGoal ),
        (
            true
        ;
            optional_trace( '.. failing variant'( Goal ) ),
            fail
        ),
        rule( Goal, Body - NewGoals, RN ),       % i.e, Body = the new resolvent
        \+ is_in_set( RN, AncSet ),
        add_to_set( RN, AncSet, NewSet ),
        (
            optional_trace( '.. entering variant at clause'( Goal, NewSet ) ),
            optional_trace( '.. new resolvent'( Body ) )
        ;
            optional_trace( '.. retrying variant'( OriginalGoal ) ),
            fail
        ),
        solve( Body, [ pair( OriginalGoal, NewSet ) | Stack ] ).

% Only variant calls, no unexplored clauses.
solve( Goals, _ ) :-
        optional_trace( '.. failing: exhausted variants only'( Goals ) ),
        fail.



%% is_variant_of_ancestor( + goal, + stack, - set of clause numbers ):
%% Is the goal a variant of something in the stack? If so, return the associated
%% set of clause numbers

is_variant_of_ancestor( Goal, Stack, N ) :-
        member( pair(G , N), Stack ),
        are_variants( G, Goal ),
        !.


%%%%%%%%
:- dynamic tracing/0.

optional_trace( X ) :-
        tracing,
        mk_variable_dictionary( X, VarDict ),
        bind_variables_to_names( VarDict ),
        writeln( X ),
        fail.

optional_trace( _ ).


legal_directive( trace   ).
legal_directive( notrace ).


execute_directive( trace ) :-
        assert( tracing ).

execute_directive( notrace ) :-
        retract( tracing ),
        !.
execute_directive( notrace ).
