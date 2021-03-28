%%%                                                                          %%%
%%%  A meta-interpreter for tabled logic programming: see the description    %%%
%%%  below for more information.                                             %%%
%%%  Written by Feliks Kluzniak at UTD.                                      %%%
%%%                                                                          %%%
%%%  Last update: 16 February 2009.                                          %%%
%%%                                                                          %%%

%%% NOTE:
%%%
%%%    1. See ../general/top_level.ecl for a description of how to load
%%%       and run programs.
%%%
%%%    2. A tabled predicate should be declared as such in the program
%%%       file, e.g.,
%%%           :- tabled ancestor/2 .
%%%
%%%       To include files use the usual Prolog syntax:
%%%           :- [ file1, file2, ... ].
%%%
%%%       To produce a wallpaper trace use the trace directive. For example,
%%%           :- trace p/3, q/0, r/1.
%%%       will trace predicates p/3, q/0 and r/1.  If you want to trace
%%%       everything, use
%%%           :- trace all.
%%%       These directives are cumulative.
%%%
%%%    2. The program should contain no other directives. It may, however,
%%%       contain queries, which will be executed immediately upon reading.
%%%
%%%    3. If the program invokes a built-in predicate, that predicate must
%%%       be declared in the table builtin/1 below.  Every addition should
%%%       be considered carefully: some might require special treatment by
%%%       the metainterpreter.
%%%
%%%    4. The program may contain clauses that modify the definition of the
%%%       interpreter's predicate "essence_hook/2" (the clauses will be asserted
%%%       at the front of the predicate, and will thus override the default
%%%       definition for some cases).  The default definition is
%%%
%%%          essence_hook( T, T ).
%%%
%%%       This predicate is invoked _in certain contexts_ when:
%%%          - two terms are about to be compared (either for equality or to
%%%            check whether they are variants of each other);
%%%          - an answer is tabled;
%%%          - an answer is retrieved from the table.
%%%
%%%       The primary intended use is to suppress arguments that carry only
%%%       administrative information and that may differ in two terms that are
%%%       "semantically" equal or variants of each other. (Such, for example, is
%%%       the argument that carries the set of coinductive hypotheses in a
%%%       co-logic program translated into prolog).
%%%
%%%       For example, the presence of
%%%
%%%          essence_hook( p( A, B, _ ),  p( A, B ) ).
%%%
%%%       will result in "p( a, b, c )" and "p( a, b, d )" being treated as
%%%       identical, as each of them will be translated to "p( a, b )" before
%%%       comparison.
%%%
%%%       NOTE: This facility should be used with the utmost caution, as it
%%%             may drastically affect the semantics of the interpreted program
%%%             in a fashion that would be hard to understand for someone who
%%%             does not understand the details of the interpreter.

%%% LIMITATIONS: - The interpreted program should not contain cuts.
%%%              - Error detection is quite rudimentary.


/*******************************************************************************

General description
   -------------------

   A simple (and very inefficient) metainterpreter that attempts to emulate
   "top-down tabled programming", as described in

     [1] Hai-Feng Guo, Gopal Gupta:
         Tabled Logic Programming with Dynamic Ordering of Alternatives
         (17th ICLP, 2001)

     [2] Neng-Fa Zhou, Taisuke Sato, Yi-Dong Shen:
         Linear Tabling Strategies and Optimizations
         (TPLP 2008 (?))

   The interpreter follows -- somewhat loosely(*) -- the description in the
   latter paper, using the "lazy strategy", but without "semi-naive
   optimization".
   Moreover, "clusters" are detected dynamically, to achieve greater precision
   (a dependency graph among static calls can only be a rough approximation, a
   dependency graph among predicates is rougher still).

   The "lazy strategy" consists in eagerly tabling answers to the subgoals
   encountered during the evaluation of a query.

   [(*) The main difference with respect to the paper is that pioneers that are
        not topmost looping goals are not treated in a special manner, so more
        re-evaluation may occur.  In this program, the term "pioneer" is
        used to denote a "topmost looping pioneer".
   ]


   Nomenclature
   ------------

   Some predicates are "tabled", because the user has declared them to be such
   by using a directive.  E.g.,

       :- tabled p/2 .

   All calls to a tabled predicate that are present in the interpreted program
   are called "tabled calls".  Instances of such calls are called "tabled
   goals".  In general, we will use the term "call" to refer to a static entity
   in the program, and "goal" to refer to an instance of a call.  We will also
   avoid the conventional overloading of the term "goal" in yet another way: we
   will call a sequence (i.e., conjunction) of goals just that (unless we can
   refer to it as a "query" or a "resolvent").


   Limitations
   -----------

   The interpreted program must not contain cuts.  It also must not contain
   calls to built-in-predicates, except for the handful of predicates listed in
   builtin/1 below.  (This list can be easily extended as the need arises.  Some
   built-in predicates, however, cannot be added without modifying the
   interpreter, sometimes extensively: "!/0" is a good example.)


   Data structures
   ---------------

   The interpreter uses a number of tables that store information accumulated
   during a computation.  A computation consists in reading a program and
   executing a number of queries.  (A query is a sequence of goals.)

   The tables (implemented as dynamic predicates of Prolog) are:

   -- tabled( generic head )

           Contains an entry for each predicate that has been declared as
           tabled.  For instance, when the interpreter reads
               :- tabled p/2 .
           it stores the fact
               tabled( p( _, _ ) ).

   -- answer( goal, fact )

           Used to store results computed for tabled goals encountered during a
           computation.  Once present, these results are also used during
           further stages of the computation.

           Note that the fact is an instantiation of the goal.  If a tabled
           goal has no solutions, it will have no entry in "answer", even though
           it may have an entry in "completed" (see below).

           NOTE: Both the goal and the fact are filtered through
                 "essence_hook/2" before they are stored in the table.

           In general, a side-effect of each evaluation of a query will be the
           generation -- for each tabled goal encounted during the evaluation
           -- of a set of facts that form the goal's "least fixed point
           interpretation".  (Of course, if this set is not sufficiently small,
           the interpreter will not terminate successfully.)  The facts
           (which need not be ground!) are all entered into the table
           "answered", and the members of different sets are distinguished by
           their association with the appropriate goal: a fact in "answered"
           is a result that is valid only for a variant of the accompanying
           goal.

           The need for annotating a fact with information about the
           corresponding goal might not be immediately obvious.  Consider the
           following example (which is simplistic in that the computation itself
           is trivial):

               program:  p( A, A ).
                         p( a, a ).
                         p( a, b ).

               queries:  ?-  p( U, V ).
                         ?-  p( W, W ).
                         ?-  p( a, X ).
                         ?-  p( Y, b ).

           During "normal" execution of this Prolog program each of the queries
           would generate a different set of results; to wit:

               p( U, V )  would generate  p( U, U ), p( a, a ), p( a, b )
               p( W, W )  ..............  p( W, W ), p( a, a )
               p( a, X )  ..............  p( a, a ), p( a, a ), p( a, b )
               p( Y, b )  ..............  p( b, b ), p( a, b ).

           In other words, the set of results depends not only on the predicate,
           but also on the form of the goal. In particular, "p( b, b )" is a
           valid answer only for goals whose second argument is "b".

           If "p/2" is tabled, the proper contents of "answer" would be as
           follows (not necessarily in this order):

               answer( p( U, V ), p( U, U ) ).
               answer( p( U, V ), p( a, a ) ).
               answer( p( U, V ), p( a, b ) ).
               answer( p( W, W ), p( W, W ) ).
               answer( p( W, W ), p( a, a ) ).
               answer( p( a, X ), p( a, a ) ).
               answer( p( a, X ), p( a, b ) ).
               answer( p( Y, b ), p( b, b ) ).
               answer( p( Y, b ), p( a, b ) ).

           Please note that the repetition of "p( a, a )" for the goal
           "p( a, X )" will be avoided.  In general, entries in "answer" will
           not be variants of each other.

   -- number_of_answers

           This is a non-logical variable that  records the size of "answer".
           It is used for determining whether new answers have been generated
           during a phase of the computation.

   -- pioneer( goal, index )

           If the current goal is tabled, and its variants have not yet been
           encountered during the evaluation of the current query, the goal
           is called a "pioneer" and recorded in this table.  (An unique index
           is also stored.)
           If a variant goal is encountered subsequently, it will be treated
           as a "follower".
           The table is used to detect whether a tabled goal (when first
           encountered) is a pioneer or a follower.
           If a pioneer is determined not to be the "topmost looping goal" in a
           "cluster" of interdependent goals (see ref. [2]), then it loses the
           status of a pioneer.  This is because a pioneer is expected to
           compute the fixpoint (by tabling answers) for itself and its cluster
           before succeeding: the property is the reason why followers can query
           only "answer", and do not use their clauses.
           Note that no two entries in "pioneer" are variants of each other.
           NOTE: The goal is filtered through "essence_hook/2" before it is
                 stored in the table.
           This table is cleared each time the evaluation of a query terminates.

   -- pioneer_index

           This is a non-logical variable that holds the index to be used for
           the next entry in "pioneer".

   -- loop( pioneer goal, list of goals, index )

           A loop is discovered when the current goal is a variant of its
           ancestor.  If the ancestor is a pioneer, information about the
           pioneer ancestor and the tabled goals between the pioneer and
           the variant is stored in "loop".  (An unique index is also stored.)
           A number of "loop" entries may exist for a given pioneer: together,
           they describe a "cluster" (see ref. [2]).  Before returning any
           answers, a pioneer will compute its own fixpoint as well as
           the fixpoints of the goals in its cluster.
           When a goal loses its pioneer status (because it is determined to
           be a part of a larger loop), the associated entries in "loop" are
           removed.
           NOTE: The goal and goals are filtered through "essence_hook/2" before
                 they are stored in the table.
           This table is cleared each time the evaluation of a query terminates.

   -- loop_index

           This is a non-logical variable that holds the index to be used for
           the next entry in "loop".

   -- completed( goal )

           Indicates that the fixpoint for this tabled goal has been computed,
           and all the possible results for variants of the goal can be found
           in table "answer".
           NOTE: The goal is filtered through "essence_hook/2" before it is
                 stored in the table.

   -- tracing( goal )

           A goal that matches something in this table will show up on the
           wallpaper trace.  This table is empty by default, and filled only
           upon encountering "trace" directives when the interpreted program is
           being read.

           NOTE: The version of the goal that is filtered through
                 "essence_hook/2" is also stored in the table, so that both
                 versions are traced.

*******************************************************************************/


:- ensure_loaded( [ '../general/top_level',
                    '../general/utilities'
                  ]
                ).




% If a file name has no extension, add ".tlp"

default_extension( ".tlp" ).                              % invoked by top_level


%% Initialization of tables:

:- dynamic tabled/1 .
:- dynamic answer/2 .
:- dynamic pioneer/2 .
:- dynamic loop/3 .
:- dynamic completed/1 .
:- dynamic tracing/1.

:- setval( number_of_answers, 0 ).
:- setval( pioneer_index,     0 ).
:- setval( loop_index,        0 ).

initialise :-                                             % invoked by top_level
        retractall( tabled( _ )     ),
        retractall( answer( _, _ )  ),
        retractall( pioneer( _, _ ) ),
        retractall( loop( _, _, _ ) ),
        retractall( completed( _ )  ),
        retractall( tracing( _ )    ),
        setval( number_of_answers, 0 ),
        setval( pioneer_index,     0 ),
        setval( loop_index,        0 ).


program_loaded.                                           % invoked by top_level




%%%%%  Built-in predicates  %%%%
%%
%%  NOTE: Just adding "!" will not do the trick, the main metainterpreter would
%%        have to be modified substantially.
%%        Certain other built-ins may also require special treatment.

builtin( true               ).
builtin( false              ).
builtin( fail               ).
builtin( \+( _ )            ).  % special treatment in solve/3
builtin( once( _ )          ).  % special treatment in solve/3
builtin( (_ -> _ ; _)       ).  % special treatment in solve/3
builtin( (_ ; _)            ).  % special treatment in solve/3
builtin( (_ , _)            ).  % special treatment in solve/3
builtin( _ = _              ).
builtin( _ \= _             ).
builtin( _ > _              ).
builtin( _ >= _             ).
builtin( _ =< _             ).
builtin( _ < _              ).
builtin( _ is _             ).
builtin( atom( _ )          ).
builtin( var( _ )           ).
builtin( write( _ )         ).
builtin( writeln( _ )       ).
builtin( write_term( _, _ ) ).
builtin( nl                 ).
builtin( read( _ )          ).
builtin( set_flag( _, _ )   ).
builtin( member( _, _ )     ).
builtin( assert( _ )        ).  % special treatment in solve/3 (only facts!)
builtin( retractall( _ )    ).  % special treatment in solve/3 (only facts!)
builtin( set_print_depth( _, _ )   ).      % not a real built-in, see  top_level



%%%%  Hooks

%% Declarations of hook predicates (for the top level):

hook_predicate( essence_hook( _, _ ) ).


%% The default essence_hook:

:- dynamic   essence_hook/2.

essence_hook( T, T ).


%% extract_essence( + list of terms, - list of their essences):
%% Apply "essence_hook/2" to all the terms.

:- mode extract_essence( +, - ).

extract_essence(         [],         [] ).
extract_essence( [ T | Ts ], [ E | Es ] ) :-
        once( essence_hook( T, E ) ),
        extract_essence( Ts, Es ).




%%%%%  Administration  %%%%%

:- op( 1000, fy, tabled ).    % allow  ":- tabled p/k ."
:- op( 1000, fy, trace  ).    % allow  ":- trace  p/k ."



%% The legal directives (check external form only).  (Used by the top level.)

legal_directive( (tabled _)  ).
legal_directive( (trace _)   ).
legal_directive( (dynamic _) ).


%% Check and process the legal directives (invoked by top_level)

execute_directive( tabled PredSpecs ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( tabled( Pattern ) ),
            fail
        ;
            true
        ).

execute_directive( (trace all) ) :-
        !,
        will_trace( [ _ ] ).

execute_directive( (trace PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        will_trace( Patterns ).

execute_directive( (dynamic PredSpecs) ) :-
        (dynamic PredSpecs)@interpreted.


%% will_trace( + list of patterns ):
%% Store the patterns in tracing/1:

will_trace( Patterns ) :-
        member( Pattern, Patterns ),
        assert( tracing( Pattern ) ),
        once( essence_hook( Pattern, EssenceOfPattern ) ),
        assert( tracing( EssenceOfPattern ) ),
        fail.

will_trace( _ ).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%  The meta-interpreter  %%%%%


%% Execute a query.

:- mode query( + ).

query( Goals ) :-                                         % invoked by top_level
        solve( Goals, [], 0 ),
        retractall( pioneer( _, _ )  ),
        retractall( loop( _, _ , _ ) ),
        setval( pioneer_index, 0 ),
        setval( loop_index,    0 ).




%% solve( + sequence of goals, + stack, + level ):
%% Solve the sequence of goals, maintaining information about the current chain
%% of ancestors (stack).  The level is the level of recursion, and is used only
%% for tracing.
%%
%% Please note that the following invariant must be maintained:
%%    A pioneer is
%%    (a) either an active goal (i.e., the current goal, or present in the
%%        chain of ancestors);
%%    (b) or marked as completed.

:- mode solve( +, +, + ).


% Note that even during the computation of \+/1 a whole set of answers
% may become tabled.

solve( \+ Goal, Stack, Level ) :-
        !,
        NLevel is Level + 1,
        optional_trace( 'Entering normal: ', \+ Goal, Level ),
        (
            \+ solve( Goal, Stack, NLevel ),
            optional_trace( 'Success normal: ', \+ Goal, Level )
        ;
            optional_trace( 'Failure normal: ', \+ Goal, Level ),
            fail
        ).


% Note that even during the computation of once/1 a whole set of answers
% may become tabled.

solve( once( Goal ), Stack, Level ) :-
        !,
        NLevel is Level + 1,
        optional_trace( 'Entering normal: ', once( Goal ), Level ),
        (
            once( solve( Goal, Stack, NLevel ) ),
            optional_trace( 'Success normal: ', once( Goal ), Level )
        ;
            optional_trace( 'Failure normal: ', once( Goal ), Level ),
            fail
        ).


% A conditional.

solve( (Cond -> Then ; _Else), Stack, Level ) :-
        solve( Cond, Stack, Level ),
        !,
        solve( Then, Stack, Level ).

solve( (_Cond -> _Then ; Else), Stack, Level ) :-
        !,
        solve( Else, Stack, Level ).


% A disjunction without a conditional.

solve( (Goals ; _), Stack, Level ) :-
        solve( Goals, Stack, Level ).

solve( (_ ; Goals), Stack, Level ) :-
        !,
        solve( Goals, Stack, Level ).


% A conjunction.

solve( (Goals1 , Goals2), Stack, Level ) :-
        !,
        solve( Goals1, Stack, Level ),
        solve( Goals2, Stack, Level ).


% assert

solve( assert( Clause ), _, _ ) :-
        !,
        (
            \+ is_good_clause( Clause )
        ->
            error( [ "Bad clause argument: ", assert( Clause ) ] )
        ;
            true
        ),
        assert( Clause )@interpreted.


% retractall

solve( retractall( C ), _, _ ) :-
        !,
        retractall( C )@interpreted.


% Some other supported built-in.

solve( BuiltIn, _, _ ) :-
        builtin( BuiltIn ),
        !,
        call( BuiltIn ).


% A "normal" (i.e., not tabled) goal.

solve( Goal, Stack, Level ) :-
        \+ tabled( Goal ),
        !,
        optional_trace( 'Entering normal: ', Goal, Level ),
        (
            solve_by_rules( Goal, Stack, Level ),
            optional_trace( 'Success normal: ', Goal, Level )
        ;
            optional_trace( 'Failure normal: ', Goal, Level ),
            fail
        ).


% A tabled goal that has been completed: all the results are in "answer".

solve( Goal, _, Level ) :-
        is_completed( Goal ),
        !,
        optional_trace( 'Entering completed: ', Goal, Level ),
        (
            get_answer( Goal ),
            optional_trace( 'Success completed: ', Goal, Level )
        ;
            optional_trace( 'Failure completed: ', Goal, Level ),
            fail
        ).


% A tabled goal that has a variant among its ancestors.
% See the comment to variant_of_ancestor for a more detailed description of
% the actions taken.
% Only the existing (most likely incomplete) results from "answer" are
% returned before failure.

solve( Goal, Stack, Level ) :-
        variant_of_ancestor( Goal, Stack ),
        !,
        optional_trace( 'Entering variant: ', Goal, Level ),
        (
            get_answer( Goal ),
            optional_trace( 'Success variant: ', Goal, Level )
        ;
            optional_trace( 'Failure variant: ', Goal, Level ),
            fail
        ).


% A pioneer goal is solved by rules, producing results that are stored in
% "answer": after this is done, "answer" is used to pass on the results.
%
% Moreover, the answer set asociated with the goal is extended to the least
%  fixed point and its cluster is marked as complete.
%
% (Note that a pioneer but may cease to be one when some descendant goal finds
%  a variant ancestor that is also an ancestor of the pioneer.
%  See variant_of_ancestor/2.)

solve( Goal, Stack, Level ) :-
        \+ is_a_variant_of_a_pioneer( Goal ),
        !,
        add_pioneer( Goal ),
        optional_trace( 'Adding pioneer: ', Goal, Level ),
        store_all_solutions_by_rules( Goal, Stack, Level ),
        (
            is_a_variant_of_a_pioneer( Goal )      % might have lost its status!
        ->
            compute_fixed_point( Goal, Stack, Level ),
            complete_cluster( Goal )
        ;
            true
        ),
        get_answer( Goal ).


% A tabled goal that is not completed, not a pioneer on entry, and has no
% variant among its ancestors.  Something is wrong!

solve( Goal, Stack, _ ) :-
        fatal_error( 'IMPOSSIBLE!', [ Goal| Stack ] ).




%% store_all_solutions_by_rules( + goal, + stack, + level ):
%% Invoke solve_by_rules/2 until there are no solutions left, storing
%% the results in "answer".

:- mode store_all_solutions_by_rules( +, +, + ).

store_all_solutions_by_rules( Goal, Stack, Level ) :-
        copy_term( Goal, OriginalGoal ),
        solve_by_rules( Goal, Stack, Level ),
        memo( OriginalGoal, Goal ),
        fail.

store_all_solutions_by_rules( _, _, _ ).



%% solve_by_rules( + goal, + stack, + level ):
%% Solves the goal by using rules (i.e., clauses) only.

:- mode solve_by_rules( +, +, + ).

solve_by_rules( Goal, Stack, Level ) :-
        copy_term( Goal, OriginalGoal ),
        NLevel is Level + 1,
        use_clause( Goal, Body ),
        solve( Body, [ OriginalGoal | Stack ], NLevel ).

%
use_clause( Goal, Body ) :-
        (
            functor( Goal, P, K ),
            current_predicate( P/K )@interpreted
        ->
            clause( Goal, Body )@interpreted
        ;
            warning( [ 'Calling an undefined predicate: ', Goal ] ),
            fail
        ).





%% compute_fixed_point( + goal, + stack, + level ):
%% Solve the goal by rules until no more answers are produced, then succeed
%% _without_ instantiating the goal.

:- mode compute_fixed_point( +, +, + ).

compute_fixed_point( Goal, Stack, Level ) :-
        optional_trace( 'Computing fixed point for ', Goal, Level ),
        getval( number_of_answers, NAns ),
        compute_fixed_point_( Goal, Stack, Level, NAns ).

%
:- mode compute_fixed_point_( +, +, +, + ).

compute_fixed_point_( Goal, Stack, Level, _ ) :-
        store_all_solutions_by_rules( Goal, Stack, Level ),     % all solutions
        fail.

compute_fixed_point_( _, _, _, NAns ) :-
        getval( number_of_answers, NAns ),                      % no new answers
        !.

compute_fixed_point_( Goal, Stack, Level, NAns ) :-
        getval( number_of_answers, NA ),
        NA =\= NAns,                                            % new answers,
        compute_fixed_point_( Goal, Stack, Level, NA ).         %   so iterate



%% variant_of_ancestor( + goal, + list of goals ):
%% Succeeds if the goal is a variant of some member of the list.
%%
%% SIDE EFFECT: If successful, then intermediate pioneer goals will lose their
%%              status as pioneers, and the associated entries in "loop" will
%%              be removed.  Moreover, if the variant ancestor is a pioneer,
%%              the entire prefix of the list upto (and including) the variant
%%              ancestor will be added to the cluster of that ancestor (by
%%              storing it in "loop"), after filtering out goals that are not
%%              tabled.

:- mode variant_of_ancestor( +, + ).

variant_of_ancestor( Goal, List ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        append( Prefix, [ G | _ ], List ),                % i.e., split the list
        once( essence_hook( G, EssenceOfG ) ),
        are_variants( EssenceOfGoal, EssenceOfG ),
        !,
        keep_tabled_goals( Prefix, TabledPrefix ),
        (
            member( M, TabledPrefix ),
            rescind_pioneer_status( M ),
            fail
        ;
            true
        ),
        (
            is_a_variant_of_a_pioneer( G )
        ->
            add_loop( G, TabledPrefix )
        ;
            true
        ).


%% keep_tabled_goals( + list of goals, - list of goals ):
%% Filter away goals that are not tabled.

:- mode keep_tabled_goals( +, - ).

keep_tabled_goals( [], [] ).

keep_tabled_goals( [ G | Gs ], [ G | TGs ] ) :-
        tabled( G ),
        !,
        keep_tabled_goals( Gs, TGs ).

keep_tabled_goals( [ _G | Gs ], TGs ) :-
        % \+ tabled( G ),
        keep_tabled_goals( Gs, TGs ).


%% rescind_pioneer_status( + goal ):
%% If the goal is tabled in "pioneer", remove the entry and the associated
%% cluster (i.e., entries in "loop").

:- mode rescind_pioneer_status( + ).

rescind_pioneer_status( Goal ) :-
        is_a_variant_of_a_pioneer( Goal ),
        once( essence_hook( Goal, EssenceOfGoal ) ),
        !,
        optional_trace( 'Removing pioneer: ', Goal, '?' ),
        remove_pioneer( EssenceOfGoal ),
        remove_loops( EssenceOfGoal ).

rescind_pioneer_status( _ ).


%% complete_cluster( + goal ):
%% If the goal has an associated cluster, make sure all the goals in the cluster
%% are marked as complete.  If there is no associated cluster, just mark the
%% goal as complete.
%% Recall that a cluster may consist of a number of "loops".

:- mode complete_cluster( + ).

complete_cluster( Goal ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        complete_goal( EssenceOfGoal ),
        complete_cluster_if_any( EssenceOfGoal ).

%
:- mode complete_cluster_if_any( + ).

complete_cluster_if_any( Goal ) :-
        loop( G, Gs, _ ),
        are_variants( G, Goal ),
        complete_goals( Gs ),
        fail.

complete_cluster_if_any( _ ).

%
:- mode complete_goals( + ).

complete_goals( Gs ) :-
        member( G, Gs ),
        complete_goal( G ),
        fail.

complete_goals( _ ).





%%-----  The tables: access and modification  -----


%% memo( + goal, + fact ):
%% If the table "answer" does not contain a variant of this fact paired with
%% a variant of this goal, then add the pair to the table, increasing
%% "number_of_answers".

:- mode memo( +, + ).

memo( Goal, Fact ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        once( essence_hook( Fact, EssenceOfFact ) ),
        memo_( EssenceOfGoal, EssenceOfFact ).

%
memo_( Goal, Fact ) :-
        answer( G, F ),
        are_variants( F, Fact ),
        are_variants( G, Goal ),
        !.

memo_( Goal, Fact ) :-
        % No variant pair in "answer",
        optional_trace( 'Storing answer: ', Fact, '?' ),
        assert( answer( Goal, Fact ) ),
        incval( number_of_answers ).



%% get_answer( +- goal ):
%% Get an instantiation (if any) tabled in "answer" for variants of this goal.
%% Sequence through all such instantiations on backtracking.

:- mode get_answer( ? ).

get_answer( Goal ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        answer( G, Ans ),
        are_variants( EssenceOfGoal, G ),
        EssenceOfGoal = G,         % make sure that variables are the right ones
        EssenceOfGoal = Ans .      % instantiate



%% complete_goal( + goal ):
%% Make sure the goal is marked as completed.
%%
%% NOTE: The assumption is that the goal has already been filtered through
%%       "essence_hook/2".

:- mode complete_goal( + ).

complete_goal( Goal ) :-
        is_completed( Goal ),
        !.

complete_goal( Goal ) :-
        % \+ is_completed( Goal ),
        optional_trace( 'Completing: ', Goal, '?' ),
        assert( completed( Goal ) ).



%% is_completed( + goal ):
%% Succeeds iff the goal is a variant of a goal that has been stored in
%% the table "completed".

:- mode is_completed( + ).

is_completed( Goal ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        completed( G ),
        are_variants( EssenceOfGoal, G ).



%% is_a_variant_of_a_pioneer( + goal ):
%% Succeeds if the goal is a variant of another goal that is tabled in
%% "pioneer".

:- mode is_a_variant_of_a_pioneer( + ).

is_a_variant_of_a_pioneer( Goal ) :-
        essence_hook( Goal, EssenceOfGoal ),
        pioneer( PG, _Index ),
        are_variants( EssenceOfGoal, PG ).



%% make_a_pioneer( + goal ):
%% Add an entry for this goal to "pioneer".

:- mode add_pioneer( + ).

add_pioneer( Goal ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        getval( pioneer_index, NewIndex ),
        incval( pioneer_index ),
        assert( pioneer( EssenceOfGoal, NewIndex ) ).



%% remove_pioneer( + goal ):
%% Remove the pioneer entry for this goal.
%%
%% NOTE: The assumption is that the goal has already been filtered through
%%       "essence_hook/2".

:- mode remove_pioneer( + ).

remove_pioneer( Goal ) :-
        pioneer( G, Index ),
        are_variants( G, Goal ),
        once( retract( pioneer( _, Index ) ) ).



%% add_loop( + goal, + list of goals ):
%% Add an entry to "loop".

:- mode add_loop( +, + ).

add_loop( Goal, Goals ) :-
        extract_essence( [ Goal | Goals ], [ EssenceOfGoal | EssenceOfGoals ] ),
        getval( loop_index, NextIndex ),
        incval( loop_index ),
        assert( loop( EssenceOfGoal, EssenceOfGoals, NextIndex ) ).



%% remove_loops( + goal ):
%% Remove all entries in "loop" that are associated with this goal.
%%
%% NOTE: The assumption is that the goal has already been filtered through
%%       "essence_hook/2".

:- mode remove_loops( + ).

remove_loops( Goal ) :-
        loop( G,_, Indx ),
        are_variants( G, Goal ),
        once( retract( loop( _, _, Indx ) ) ),
        fail.

remove_loops( _ ).





%%-----  Custom-tailored utilities  -----


%% optional_trace( + label, + goal, + level ):
%% If the goal matches one of the traced patterns, print out a trace line with
%% this label:

optional_trace( Label, Goal, Level ) :-
        tracing( Goal ),
        !,
        write( output, '[' ),
        write( output, Level ),
        write( output, '] ' ),
        write( output, Label ),
        write( output, Goal ),
        nl( output ).

optional_trace( _, _, _ ).



%% fatal_error( + message, + stack ):
%% Display the message and stack, then abort.

:- mode fatal_error( +, + ).

fatal_error( Message, Stack ) :-
        begin_error,
        writeln(    error, Message ),
        writeln(    error, '' ),
        writeln(    error, '*** The current stack:' ),
        show_stack( error, Stack ),
        end_error.

%
show_stack( Stream, Stack ) :-
        member( Call, Stack ),
        writeln( Stream, Call ),
        fail.

show_stack( _ ).
