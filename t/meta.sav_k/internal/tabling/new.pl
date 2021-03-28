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
        transform_body( Goals, _, GoalList - [] ),
        write( 'Query: ' ),  writeln( GoalList ),
        solve( GoalList, [], 0 ).



%% Transform the program: each clause is converted so that its body is a d-list,
%% and then asserted in rule/3, together with a number unique for the predicate.
%% Moreover, each literal is represented by "pair( original literal, size )",
%% where "size" is a variable, common to all the literals, that at runtime will
%% represent the size of the stack at the time the clause was invoked.

%% For example,
%%    anc( X, Y ) :- anc( X, Z ), p( Z, Y ).
%% will be stored as
%%    rule( pair( anc( X, Y ), Size ),
%%          [ pair( anc( X, Z ), Size ),  pair( p( Z, Y ), Size ) | End ] - End,
%%          0
%%        ).
%% (assuming this is the first clause of anc/2).

transform_program :-
        current_predicate_in_module( interpreted, P / K ),
        mk_pattern( P, K, Head ),
        \+ builtin( Head ),
        setval( clause_counter, 0 ),
        clause_in_module( interpreted, Head, Body ),
        transform_body( Body, SizeVar, DList ),
        getval( clause_counter, N ),
%        writeln( asserting( rule( pair( Head, SizeVar ), DList, N ) ) ),
        assertz( rule( pair( Head, SizeVar ), DList, N ) ),
        incval( clause_counter ),
        fail.

transform_program.


%% transform_body( + (part of) clause body, + size variable, - d-list ):
%% For the time being we don't handle disjunctions and conditionals.

transform_body( true, _, End - End ) :-
        !.

transform_body( (_ ; _), _, _ ) :-
        !,
        error( 'Cannot handle disjunctions yet' ).

transform_body( (_ -> _), _, _ ) :-
        !,
        error( 'Cannot handle conditionals yet' ).

transform_body( ((A , B), C), Size, DL ) :-
        !,
        transform_body( (A , (B , C)), Size, DL ).

transform_body( (A , B), Size, DL ) :-
        !,
        transform_body( A, Size, DLA - AEnd ),
        transform_body( B, Size, DLB - BEnd ),
        AEnd = DLB,
        DL = DLA - BEnd.

transform_body( A, Size, [ pair( A, Size ) | End ] - End ).



%% solve( + list of goals, + current stack, + the size of the stack ):
%% Solve the sequence of goals.
%% The stack holds triples of the form:
%%   pair( goal,
%%         set of clauses used by this goal or its variant ancestors,
%%         the size of the stack right after this goal was pushed
%%       )

solve( [], _, _ ) :-                                                   % success
        !,
        optional_trace( '.. success' ).

solve( [ pair( Goal, _ ) | Pairs ], Stack, Size ) :-
        builtin( Goal ),
        !,
        optional_trace( '.. invoking builtin'( Goal ) ),
        call( Goal ),
        solve( Pairs, Stack, Size ).


% If the resolvent starts with a non-empty prefix of variant goals, but there
% is at least one "regular" goal, postpone the variants and execute the first
% "regular".  However, make sure that we do not execute built-ins until they
% are  leftmost "of natural causes".
%
solve( Pairs, Stack, Size ) :-
        append( PrefixOfVariants, [ Pair | Ps ], Pairs ),
        ( \+ is_variant_of_ancestor( Pair, Stack, _ )
        , Pair = pair( Goal, _ )
        ,
          ( \+ builtin( Goal )
          ;
            PrefixOfVariants = []
          )
        ),
        !,
        append( Ps, PrefixOfVariants, NewPairs ),
        copy_term( Goal, OriginalGoal ),
        NSize is Size + 1,
        (
            true
        ;
            optional_trace( '.. failing'( Goal ) ),
            fail
        ),
        % in the following call Body gets instantiated to the new resolvent,
        % and all the pairs in the body get the right size:
        rule( pair( Goal, NSize ), Body - NewPairs, RN ),
        (
            optional_trace( '.. entering at clause'( Goal, [ RN ] ) ),
            optional_trace( '.. new resolvent'( Body ) )
        ;
            optional_trace( '.. retrying'( OriginalGoal ) ),
            fail
        ),
        solve( Body, [ triple( OriginalGoal, [ RN ], NSize ) | Stack ], NSize ).


% % If the current goal is not a variant, do the usual thing.
% % (Kept around for experimentation: subsumed by the previous rule.)
%
% solve( [ Pair | Pairs ], Stack, Size ) :-
%         \+ is_variant_of_ancestor( Pair, Stack, _ ),
%         !,
%         Pair = pair( Goal, _ ),
%         copy_term( Goal, OriginalGoal ),
%         NSize is Size + 1,
%         (
%             true
%         ;
%             optional_trace( '.. failing normal'( Goal ) ),
%             fail
%         ),
%         % in the following call Body gets instantiated to the new resolvent,
%         % and all the pairs in the body get the right size:
%         rule( pair( Goal, NSize) , Body - Pairs, RN ),
%         (
%             optional_trace( '.. entering normal at clause'( Goal, RN ) ),
%             optional_trace( '.. new resolvent'( Body ) )
%         ;
%             optional_trace( '.. retrying normal'( OriginalGoal ) ),
%             fail
%         ),
%         solve( Body, [ triple( OriginalGoal, [ RN ], NSize ) | Stack ], NSize ).


% All the goals are variants: execute the first one that has clauses unexplored
% by variant ancestors, postponing those that precede it, but
% don't have such clauses.
%
solve( Pairs, Stack, Size ) :-
        append( PrefixOfExhaustedVariants, [ Pair | Ps ], Pairs ),
        (
            is_variant_of_ancestor( Pair, Stack, AncSet ),
            Pair = pair( Goal, _ ),
            copy_term( Goal, Copy ),
            rule( pair( Copy, _ ), _, N ),
            \+ is_in_set( N, AncSet )
        ),
        !,
        append( Ps, PrefixOfExhaustedVariants, NewPairs ),
        copy_term( Goal, OriginalGoal ),
        NSize is Size + 1,
        (
            true
        ;
            optional_trace( '.. failing variant'( Goal ) ),
            fail
        ),
        % in the following call Body gets instantiated to the new resolvent,
        % and all the pairs in the body get the right size:
        rule( pair( Goal, NSize ), Body - NewPairs, RN ),
        \+ is_in_set( RN, AncSet ),
        add_to_set( RN, AncSet, NewSet ),
        (
            optional_trace( '.. entering variant at clause'( Goal, RN ) ),
            optional_trace( '.. new resolvent'( Body ) )
        ;
            optional_trace( '.. retrying variant'( OriginalGoal ) ),
            fail
        ),
        solve( Body, [ triple( OriginalGoal, NewSet, NSize ) | Stack ], NSize ).


% Only variant calls, no unexplored clauses.
solve( Pairs, _, _ ) :-
        optional_trace( '.. failing: exhausted variants only'( Pairs ) ),
%        optional_trace( '.. failing'( Pairs ) ),
        fail.



%% is_variant_of_ancestor( + goal pair, + stack, - set of clause numbers ):
%% Is the goal a variant of something in the stack? If so, return the associated
%% set of clause numbers

is_variant_of_ancestor( pair( Goal, Size ), Stack, ClauseNumbers ) :-
        member( triple( G, ClauseNumbers, S ), Stack ),
        S =< Size,                         % i.e., look only for real ancestors
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
