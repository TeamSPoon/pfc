   % NOTICE: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %                                                                      %
   %  COPYRIGHT (2009) University of Dallas at Texas.                     %
   %                                                                      %
   %  Developed at the Applied Logic, Programming Languages and Systems   %
   %  (ALPS) Laboratory at UTD by Feliks Kluzniak.                        %
   %                                                                      %
   %  Permission is granted to modify this file, and to distribute its    %
   %  original or modified contents for non-commercial purposes, on the   %
   %  condition that this notice is included in all copies in its         %
   %  original form.                                                      %
   %                                                                      %
   %  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,     %
   %  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES     %
   %  OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, TITLE AND     %
   %  NON-INFRINGEMENT. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR        %
   %  ANYONE DISTRIBUTING THE SOFTWARE BE LIABLE FOR ANY DAMAGES OR       %
   %  OTHER LIABILITY, WHETHER IN CONTRACT, TORT OR OTHERWISE, ARISING    %
   %  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR       %
   %  OTHER DEALINGS IN THE SOFTWARE.                                     %
   %                                                                      %
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%                                                                          %%%
%%%  An interpreter for tabled logic programming with coinduction:           %%%
%%%  see the description below for more information.                         %%%
%%%  Written by Feliks Kluzniak at UTD (January-February 2009).              %%%
%%%                                                                          %%%
%%%  Last update: 30 November 2009                                           %%%
%%%                                                                          %%%
dra_version( Version ) :-
        name_chars( 'DRA ((c) UTD 2009) version 0.97 (beta), June 2011 (',
                    VCodes
                  ),
        lp_system( Sys ),
        name_chars( Sys, SysCode ),
        name_chars( ')', RParCode ),
        append( SysCode, RParCode, SPar ),
        append( VCodes, SPar, VersionCodes ),
        name_chars( Version, VersionCodes ).

%%% NOTE:
%%%
%%%    1. See ../general/top_level.ecl for a description of how to load
%%%       and run programs.
%%%       Please note that in Eclipse after loading this interpreter you
%%%       should issue
%%%            :- import dra.
%%%       if you don't want to keep writing
%%%            dra:prog( filename )
%%%       every time.
%%%
%%%    2. The interpreter supports a number of directives:
%%%
%%%       a) Tabled and coinductive predicates should be declared as such in
%%%          the program file, e.g.,
%%%              :- tabled       ancestor/2.
%%%              :- coinductive  comember/2.
%%%              :- coinductive1 comember/2.
%%%
%%%          "coinductive1" means that if there are coinductive hypotheses
%%%          with which a goal unifies, then the usual clauses will not be tried
%%%          after the hypotheses are exhausted (this is "new style"
%%%          coinduction).
%%%
%%%       b) To include files use the usual Prolog syntax:
%%%              :- [ file1, file2, ... ].
%%%
%%%       c) To declare predicates used in an interpreted program as dynamic,
%%%          use
%%%              :- dynamic p/k.
%%%
%%%       d) By default, a goal produces new (i.e., heretofore unknown) answers
%%%          before producing old ones.  To reverse this behaviour, use
%%%
%%%              :- old_first p/k.
%%%          or
%%%              :- old_first all.
%%%
%%%       e) To produce a wallpaper trace use the trace directive. For example,
%%%
%%%              :- trace p/3, q/0, r/1.
%%%
%%%          will trace predicates "p/3", "q/0" and "r/1".  If you want to trace
%%%          everything, use
%%%
%%%              :- trace all.
%%%
%%%          These directives are cumulative.
%%%
%%%       f) To print out subsets of the current answer table, use
%%%
%%%              :- answers( Goal, Pattern ).
%%%
%%%          this will print all tabled answers that are associated with a
%%%          variant of Goal and unifiable with Pattern.
%%%          To get a dump of the entire table, use just
%%%
%%%              :- answers( _, _ ).
%%%
%%%    2. The program should contain no other directives. It may, however,
%%%       contain queries, which will be executed immediately upon reading.
%%%
%%%    3. Just before the result of a query is reported, the interpreter
%%%       produces a printout with statistics accummulated since the previous
%%%       printout (or since the beginning, if this is the first printout during
%%%       this session with the interpreted program). The printout looks like
%%%       this:
%%%
%%%           [K steps, M new answers tabled (N in all)]
%%%
%%%       where K, M and N are some natural numbers. K is the number of
%%%       evaluated goals, M is the number of new additions to the answer table,
%%%       N is the current size of the answer table.
%%%
%%%    4. If the program invokes a built-in predicate, that predicate must
%%%       be declared in the table "builtin/1" (see file "dra_builtins.pl").
%%%       Every addition should be considered carefully: some built-ins might
%%%       require special treatment by the interpreter.
%%%
%%%    5. The program may contain clauses that modify the definition of the
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
%%%       co-logic program translated into Prolog: see "../coind/translate_clp".
%%%       Mind you, that translation need not be applied to programs executed by
%%%       this interpreter).
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
%%%
%%% LIMITATIONS: - The interpreted program should not contain cuts.
%%%              - Error detection is quite rudimentary.




/*******************************************************************************

   General description
   -------------------

   A simple (and very inefficient) interpreter that emulates "top-down tabled
   programming", as described in

     [1] Hai-Feng Guo, Gopal Gupta:
         Tabled Logic Programming with Dynamic Ordering of Alternatives
         (17th ICLP, 2001)

   There are two significant changes with respect to the description in the
   paper:

       - A tabled goal will never produce the same answer twice.

         More specifically: two answers will never be variants of each other.
         Please note that "goal" means a goal instance.

       - By default, new answers for a tabled goal will be produced before
         old answers.  The user can reverse the order by means of an "old_first"
         directive.

         Here, "new answer for a tabled goal" means an answer that has not yet
         been seen (and tabled) for a variant of the goal.

         The default behaviour is intended to help computations converge more
         quickly.  The user is given an option to change it, because some
         predicates may produce a very large (even infinite) set of answers on
         backtracking, and the application might not require those answers.

   The terminology has been modified under the influence of

     [2] Neng-Fa Zhou, Taisuke Sato, Yi-Dong Shen:
         Linear Tabling Strategies and Optimizations
         (TPLP 2008 (?))

   More specifically, "masters" are called "pioneers" (although in a sense
   somewhat different than in [2]: we use "pioneer" for "topmost looping goal"),
   and "strongly connected components" are called "clusters".

   Note that "clusters" are detected dynamically, to achieve greater precision
   (a dependency graph among static calls can only be a rough approximation, a
   dependency graph among predicates is rougher still).


   Nomenclature
   ------------

   Some predicates are "tabled", because the user has declared them to be such
   by using an appropriate directive, e.g.,

       :- tabled p/2 .

   All calls to a tabled predicate that are present in the interpreted program
   are called "tabled calls".  Instances of such calls are called "tabled
   goals".  In general, we will use the term "call" to refer to a static entity
   in the program, and "goal" to refer to an instance of a call.  We will also
   avoid the conventional overloading of the term "goal" in yet another way: we
   will call a sequence (i.e., conjunction) of goals just that (unless we can
   refer to it as a "query" or a "resolvent").

   Similarly, the user can declare a predicate to be "coinductive", by using
   another kind of directive, e.g.,

       :- coinductive  p/2 .
       :- coinductive1 q/3 .

   Calls and goals that refer to a coinductive predicate will also be called
   "coinductive".


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
   executing a number of queries.  A query is a sequence (i.e., conjunction) of
   goals.

   The tables (implemented as dynamic predicates of Prolog) are:


   -- coinductive( generic head )
   -- coinductive1( generic head )
   -- tabled( generic head )
   -- old_first( generic head )

           Each of these tables contains an entry for each predicate that has
           been declared as having the corresponding property (i.e., as
           coinductive, tabled etc.).  For instance, when the interpreter reads
               :- coinductive p/2 .
           it stores the fact
               coinductive( p( _, _ ) ).

           A "coinductive" declaration is deemed to supersede "coinductive1",
           and information about a predicate that has been so declared is stored
           both in coinductive/1 and coinductive1/1.

           These tables are cleared only before reading in a new program.


   -- answer( goal, fact )

           Used to store results computed for tabled goals encountered during a
           computation.  Once present, these results are also used during
           further stages of the computation.

           Note that the fact is an instantiation of the goal.  If a tabled goal
           has no solutions, it will have no entry in "answer", even though it
           may have an entry in "completed" (see below).

           (NOTE:
               1. In the actual implementation each fact in "answer" has the
                  form
                     answer( cgoal, goal, fact )
                  where "cgoal" is a copy of "goal" (no shared variables),
                  passed through essence_hook/2.
                  This is done to facilitate more effective filtering (via
                  unification) before a check is made for whether "goal" is a
                  variant of the goal for which we are seeking a tabled answer.

               2. This stuff has been removed to file dra_table_assert.pl
                  or dra_table_record.pl (only one of them is used,
                  depending on the logic programming system: see the main file
                  used to load the program.
           )

           This table is not cleared before the evaluation of a new query.

           Detailed comments:
           ..................
           In general, for each success of a tabled goal encountered during the
           evaluation of a query, the interpreter will make certain that the
           result, i.e., the successful instantiation of that goal (which need
           not be ground!) is stored in the table "answer", accompanied by a
           variant of the original version of the goal (i.e., as it appeared
           when it was first encountered).

           Before a query finally fails (after exhausting all the answers),
           tabled goals encountered during its evaluation will have computed
           their least fixed points, i.e., all the possible results for those
           goals will be stored in "answer".  (Of course, if this set of all
           answers is not sufficiently small, the interpreter will not terminate
           successfully.)

           Results stored in "answer" can be picked up during later evaluation
           but each of them is valid only for a variant of the accompanying
           goal.

           The need for associating a fact with information about the
           corresponding goal might not be immediately obvious.  Consider the
           following example (which is simplistic in that the computation itself
           is trivial):

               program:  :- tabled p/2.
                         p( A, A ).
                         p( a, b ).

               queries:  ?-  p( U, V ).
                         ?-  p( Y, b ).

           During "normal" execution of this Prolog program each of the queries
           would generate a different set of results; to wit:

               p( U, V )  would generate  p( U, U ), p( a, b );
               p( Y, b )  ..............  p( b, b ), p( a, b ).

           In other words, the set of results depends not only on the predicate,
           but also on the form of the goal.

           If these results were tabled without the corresponding goals, then
           the table would be:

               answer( p( U, U ) ).
               answer( p( a, b ) ).
               answer( p( b, b ) ).

           A subsequent invocation of p( U, V ) would then return all three
           results, i.e., also "p( b, b )"!

           The proper contents of "answer" should be as follows (though not
           necessarily in this order):

               answer( p( U, V ), p( U, U ) ).
               answer( p( U, V ), p( a, b ) ).
               answer( p( Y, b ), p( b, b ) ).
               answer( p( Y, b ), p( a, b ) ).

           Please note that two different entries in "answer" will not be
           variants of each other.

   -- number_of_answers

           This is a non-logical variable that records the size of "answer".  It
           is useful for determining whether new answers have been generated
           during a phase of the computation.

           This variable is not cleared before the evaluation of a new query.


   -- pioneer( goal, index )

           If the current goal is tabled, and it is not a variant of any of its
           ancestors, then the goal is called a "pioneer" and obtains an "index"
           (i.e., an unique identifier). Both the goal and its index are
           recorded in this table.

           The role of a pioneer is to compute the fixpoint (by tabling answers)
            for itself and its cluster before failing: this is why the results
           for its variant descendants can be obtained simply by querying
           "answer", without using their clauses (which prevents endless
           recursion).

           If a pioneer is later determined not to be the "topmost looping goal"
           in a "cluster" of interdependent goals (see ref. [2]), then it loses
           the status of a pioneer, and its role will be overtaken by the
           topmost goal in the cluster.  (This can happen if one of the
           descendants of a pioneer turns out to be a variant of one of its
           ancestors.)

           A pioneer also loses its status if its fixpoint has been computed: it
           then becomes a "completed" goal (and all its variants become
           completed).

           A pioneer "G" may also lose its status because another goal "G'",
           encountered after "G" succeeds without yet becoming completed, has
           become completed: if "G'" is a variant of "G", thne "G" becomes
           completed as well.

           When a pioneer loses its status, the associated entries in "pioneer",
           "loop" and "looping_alternative" (see below) are removed.  The
           associated entries in "result" are not removed. The unique index is
           not reused for other goals during the evaluation of the current
           query.

           This table is cleared before the evaluation of a new query.

           (NOTE: In the actual implementation each fact in "pioneer" has the
                  form
                     pioneer( cgoal, goal, index )
                  where "cgoal" is a copy of "goal" (no shared variables),
                  passed through essence_hook/2.
                  This is done to facilitate more effective filtering (via
                  unification) before a check is made for whether "goal" is a
                  variant of the goal for which we are checking whether it is
                  (still) a pioneer.
           )

   -- unique_index

           This is a non-logical variable that holds the index to be used for
           the next entry in "pioneer".  It is also used to generate unique
           indices for coinductive goals, which might need them to hold their
           own results in "result".

           The variable is cleared before the evaluation of a new query.


   -- result( index, fact )

           A tabled goal "G" that "started out" as a pioneer may have associated
           entries (marked with the unique index of "G") in "result".  This
           table records the instantiations of "G" that were returned as "G"
           succeeded.  By using the table, the interpreter prevents "G" from
           returning the same answer over and over again: in general, each
           tabled goal will not produce two results that are variants of each
           other.

           When a goal loses its pioneer status (because it is determined to be
           a part of a larger loop, or because it has become completed), the
           associated entries in "result" are not removed.  They are removed
           only when the goal finally fails.

           The table is also used by coinductive goals that are not pioneers.

           This table is cleared before the evaluation of a new query.


   -- loop( index, list of goals )

           A loop is discovered when the current tabled goal is a variant of one
           of its ancestors.  If the ancestor is a pioneer, the unique index of
           the pioneer ancestor and a list of the tabled goals between the
           pioneer and the variant are stored in "loop".

           A number of "loop" entries may exist for a given pioneer: together,
           they describe a "cluster" (i.e., a "strongly connected component",
           see ref. [1]).  Before finally failing upon backtracking, a pioneer
           will compute its own fixpoint as well as the fixpoints of the goals
           in its cluster.

           When a goal loses its pioneer status (because it is determined to be
           a part of a larger loop, or because it has become completed), the
           associated entries in "loop" are removed.

           This table is cleared before the evaluation of a new query.


   -- looping_alternative( index, clause )

           When a goal "G" is determined to be a variant descendant of a
           pioneer, the clause that is currently being used by the pioneer
           (i.e., the clause that led to "G") is stored in this table, together
           with the unique index of the pioneer.  "G" will then succeed only
           with answers that have been tabled so far, but the clause will be
           used again as backtracking brings the computation back to the
           pioneer.  (This is the essence of the "dynamic reordering of
           alternatives".)

           When a goal loses its pioneer status (because it is determined to be
           a part of a larger loop, or because it has become completed), the
           associated entries in "looping_alternative" are removed.

           This table is cleared before the evaluation of a new query.


   -- completed( goal )

           Indicates that this tabled goal is completed, i.e., its fixpoint has
           been computed, and all the possible results for variants of the goal
           can be found in table "answer".  Variants of a completed goal are
           completed as well.

           This table is not cleared before the evaluation of a new query.

           (NOTE: In the actual implementation each fact in "completed" has the
                  form
                     completed( cgoal, goal )
                  where "cgoal" is a copy of "goal" (no shared variables),
                  passed through essence_hook/2.
                  This is done to facilitate more effective filtering (via
                  unification) before a check is made for whether "goal" is a
                  variant of the goal for which we are checking whether it is
                  completed.
           )


   -- tracing( goal )

           A goal that matches something in this table will show up on the
           wallpaper trace.  This table is empty by default, and filled only
           by invocations of "trace" (most often in "trace" directives
           encountered when the interpreted program is being read).

   -- step_counter

           This is a non-logical variable that keeps track of the number of
           goals resolved during the evaluation of each query.  The final value
           is printed after the query terminates.

           The variable is cleared before the evaluation of a new query.

   -- old_table_size

           This is a non-logical variable that is used to store the value of
           "number_of_answers" before the evaluation of a query.  Used to
           produce automatic information about the growth of the table after the
           query terminates.

           The variable is reinitialized before the evaluation of a new query.


*******************************************************************************/


:- ensure_loaded( [ '../general/top_level',
                    '../general/utilities',
                    dra_builtins,
                    dra_coinductive_hypotheses,
                    dra_stack
                  ]
                ).



% If a file name has no extension, add ".tlp"

default_extension( '.tlp' ).                              % invoked by top_level


%% Initialization of tables:

:- dynamic (coinductive)/1 .
:- dynamic (coinductive1)/1 .
:- dynamic (tabled)/1 .
:- dynamic (old_first)/1 .
:- dynamic pioneer/3 .
:- dynamic result/2 .
:- dynamic loop/2 .
:- dynamic looping_alternative/2 .
:- dynamic completed/2 .
:- dynamic tracing/1.

:- setval( number_of_answers, 0 ).
:- setval( unique_index,      0 ).

initialise :-                                             % invoked by top_level
        reinitialise_answer,
        reinitialise_result,
        reinitialise_pioneer,
        reinitialise_loop,
        reinitialise_looping_alternative,
        reinitialise_completed,
        retractall( coinductive( _ )  ),
        retractall( coinductive1( _ ) ),
        retractall( tabled( _ )       ),
        retractall( old_first( _ )    ),
        retractall( tracing( _ )      ),
        setval( number_of_answers, 0 ),
        setval( unique_index,      0 ),
        setval( step_counter,      0 ),
        setval( old_table_size,    0 ),
        dra_version( Version ),
        writeln( Version ).


%% Checking consistency:

program_loaded :-                                         % invoked by top_level
        check_consistency.


%% check_consistency:
%% Produce a warning if predicates were declared but not defined (this may well
%% be due to a "tabled" directive giving the wrong arity), or if tabled/
%% coinductive predicates have been declared as "suppport".

check_consistency :-
        tabled( Head ),
        nonvar( Head ),
        functor( Head, P, K ),
        \+ current_predicate_in_module( interpreted, P / K ),
        warning( [ P/K, ' declared as tabled, but not defined' ] ),
        fail.

check_consistency :-
        coinductive1( Head ),
        nonvar( Head ),
        functor( Head, P, K ),
        \+ current_predicate_in_module( interpreted, P / K ),
        warning( [ P/K, ' declared as coinductive, but not defined' ] ),
        fail.

check_consistency :-
        support( Head ),
        tabled( Head ),
        functor( Head, P, K ),
        warning( [ P/K, ' declared as both tabled and \"support\"' ] ),
        fail.

check_consistency :-
        support( Head ),
        coinductive1( Head ),
        functor( Head, P, K ),
        warning( [ P/K, ' declared as both coinductive and \"support\"' ] ),
        fail.

check_consistency.



%%%%  Hooks

%% Declarations of hook predicates (for the top level):

hook_predicate( essence_hook( _, _ ) ).


%% The default essence_hook:

:- dynamic essence_hook/2.

essence_hook( T, T ).    % default, may be overridden by the interpreted program




%%%%%  Administration  %%%%%

:- op( 1010, fy, coinductive  ).    % allow  ":- coinductive p/k ."
:- op( 1010, fy, coinductive1 ).    % allow  ":- coinductive1 p/k ."
:- op( 1010, fy, tabled       ).    % allow  ":- tabled p/k ."
:- op( 1010, fy, old_first    ).    % allow  ":- old_first p/k ."
:- op( 1010, fy, trace        ).    % allow  ":- trace  p/k ."
:- op( 1010, fy, multifile    ).    % allow  ":- multifile  p/k ." (for Eclipse)



%% The legal directives (check external form only).  (Used by the top level.)

legal_directive( (coinductive _)  ).
legal_directive( (coinductive1 _) ).
legal_directive( (tabled _)       ).
legal_directive( (trace _)        ).
legal_directive( (dynamic _)      ).
legal_directive( (old_first _)    ).
legal_directive( (multifile _)    ).
legal_directive( answers( _, _ )  ).
legal_directive( answers          ).


%% Check and process the legal directives (invoked by top_level)

execute_directive( (tabled all) ) :-
        !,
        assert( tabled( _ ) ).

execute_directive( (tabled PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( tabled( Pattern ) ),
            fail
        ;
            true
        ).

execute_directive( (coinductive all) ) :-
        !,
        assert( coinductive1( _ ) ),
        assert( coinductive( _ ) ).

execute_directive( (coinductive PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( coinductive1( Pattern ) ),
            assert( coinductive( Pattern ) ),
            fail
        ;
            true
        ).

execute_directive( (coinductive1 all) ) :-
        !,
        assert( coinductive1( _ ) ).

execute_directive( (coinductive1 PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( coinductive1( Pattern ) ),
            fail
        ;
            true
        ).

execute_directive( (old_first all) ) :-
        !,
        asserta( old_first( _ ) ).

execute_directive( (old_first PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( old_first( Pattern ) ),
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
        dynamic_in_module( interpreted, PredSpecs).

execute_directive( (multifile _) ).    % ignore

execute_directive( answers( Goal, Pattern ) ) :-
        print_required_answers( Goal, Pattern ).


%% will_trace( + list of patterns ):
%% Store the patterns in tracing/1:

will_trace( Patterns ) :-
        member( Pattern, Patterns ),
        assert( tracing( Pattern ) ),
        fail.

will_trace( _ ).


%% print_required_answers( + goal, + pattern ):
%% Print the tabled answers that are associated with this goal and are unifiable
%% with this pattern.  If the goal is a variable, go through all the entries in
%% the table.

print_required_answers( Var, Pattern ) :-
        var( Var ),
        !,
        get_all_tabled_goals( Goals ),
        remove_variants( Goals, DifferentGoals ),
        sort( DifferentGoals, SortedDifferentGoals ),
        (
            member( Goal, SortedDifferentGoals ),      % iterate through members
            print_required_answers( Goal, Pattern ),
            nl,
            fail
        ;
            true
        ).

print_required_answers( Goal, Pattern ) :-
        copy_term2( Goal, OriginalGoal ),
        get_answer( Goal ),                            % iterate through answers
        Goal = Pattern,
        mk_variable_dictionary( OriginalGoal + Goal, VarDict ),
        bind_variables_to_names( VarDict ),
        write( OriginalGoal ),  write( ' :  ' ),  writeln( Goal ),
        fail.

print_required_answers( _, _ ).


%% remove_variants( + list, - reduced list ):
%% Remove each member of the list that is a variant of
%% a member that precedes it.  No need to preserve the order.

remove_variants( List, ReducedList ) :-
        remove_variants_( List, [], ReducedList ).

%
remove_variants_( [], Accumulator, Accumulator ).

remove_variants_( [ H | T ], Accumulator, RL ) :-
        member( M, Accumulator ),
        are_variants( H, M ),
        !,
        remove_variants_( T, Accumulator, RL ).

remove_variants_( [ H | T ], Accumulator, RL ) :-
        % H not a variant of a member of Accumulator
        remove_variants_( T, [ H | Accumulator ], RL ).








%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%  The interpreter  %%%%%


%% Execute a query.

% :- mode query( + ).

query( Goals ) :-                                         % invoked by top_level
        reinitialise_pioneer,
        reinitialise_result,
        reinitialise_loop,
        reinitialise_looping_alternative,
        setval( unique_index,      0    ),
        getval( number_of_answers, NAns ),
        setval( old_table_size,    NAns ),
        setval( step_counter,      0    ),
        (
            empty_hypotheses( Hyp ),
            empty_stack( Stack ),
            solve( Goals, Stack, Hyp, 0 ),
            print_statistics,
            setval( step_counter, 0 ),
            getval( number_of_answers, NAns2 ),
            setval( old_table_size, NAns2 )
        ;
            print_statistics,
            setval( step_counter, 0 ),
            getval( number_of_answers, NAns2 ),
            setval( old_table_size, NAns2 ),
            fail
        ).


%% Print information about the number of steps and the answer table.

print_statistics :-
        std_output_stream( Output ),
        getval( step_counter, NSteps ),
        getval( number_of_answers, NAns ),
        getval( old_table_size, OldNAns ),
        TableGrowth is NAns - OldNAns,
        write(  Output, '[' ),
        write(  Output, NSteps ),
        write(  Output, ' step' ),
        plural( Output, NSteps ),
        write(  Output, ', ' ),
        write(  Output, TableGrowth ),
        write(  Output, ' new answer' ),
        plural( Output, TableGrowth ),
        write(  Output, ' tabled (' ),
        write(  Output, NAns ),
        write(  Output, ' in all)' ),
        write(  Output, ']' ),
        nl(     Output ).

%
plural( _     , 1 ) :-  !.
plural( Output, N ) :-  N \= 1,  write( Output, 's' ).





%% solve( + sequence of goals,
%%        + stack,
%%        + coinductive hypotheses,
%%        + level
%%      ):
%% Solve the sequence of goals, maintaining information about the current chain
%% of tabled ancestors (stack) and the chain of coinductive ancestors
%% (coinductive hypotheses).  The level is the level of recursion, and is used
%% only for tracing.
%%
%% Each link in the chain of tabled ancestors is of the form
%%    triple( goal, index, clause )
%% where
%%    goal    is the (current instantiation of the) goal;
%%    index   is the unique index of the goal (every goal that is stacked starts
%%               out as a pioneer!)
%%    clause  is the clause that is currently used by the goal (it has been
%%               instantiated by matching with the goal in its original form,
%%               but does not share variables with the goal).
%%
%% NOTE: The set of coinductive hypotheses and the stack of tabled ancestors
%%       have been factored out (see files "dra_coinductive_hypotheses.pl" and
%%       "dra_stack.pl").  The representations may have changed (to enable
%%       faster access, so the comments in this file ("chain of ancestors" etc.)
%%       might no longer be quite accurate.

% :- mode solve( +, +, +, + ).


% A negation.

solve( \+ Goal, Stack, Hyp, Level ) :-
        !,
        NLevel is Level + 1,
        trace_entry( normal, \+ Goal, '?', Level ),
        (
            \+ solve( Goal, Stack, Hyp, NLevel ),
            trace_success( normal, \+ Goal, '?', Level )
        ;
            trace_failure( normal, \+ Goal, '?', Level ),
            fail
        ).


% One solution.

solve( once( Goal ), Stack, Hyp, Level ) :-
        !,
        NLevel is Level + 1,
        trace_entry( normal, once( Goal ), '?', Level ),
        (
            once( solve( Goal, Stack, Hyp, NLevel ) ),
            trace_success( normal, once( Goal ), '?', Level )
        ;
            trace_failure( normal, once( Goal ), '?', Level ),
            fail
        ).


% A conditional with an else.

solve( (Cond -> Then ; _Else), Stack, Hyp, Level ) :-
        solve( Cond, Stack, Hyp, Level ),
        !,
        solve( Then, Stack, Hyp, Level ).

solve( (_Cond -> _Then ; Else), Stack, Hyp, Level ) :-
        !,
        solve( Else, Stack, Hyp, Level ).


% A conditional without an else.

solve( (Cond -> Then), Stack, Hyp, Level ) :-
        solve( Cond, Stack, Hyp, Level ),
        !,
        solve( Then, Stack, Hyp, Level ).


% A disjunction without a conditional.

solve( (Goals ; _), Stack, Hyp, Level ) :-
        solve( Goals, Stack, Hyp, Level ).

solve( (_ ; Goals), Stack, Hyp, Level ) :-
        !,
        solve( Goals, Stack, Hyp, Level ).


% A conjunction.

solve( (Goals1 , Goals2), Stack, Hyp, Level ) :-
        !,
        solve( Goals1, Stack, Hyp, Level ),
        solve( Goals2, Stack, Hyp, Level ).


% call/1

solve( call( Goal ), Stack, Hyp, Level ) :-
        (
            ( var( Goal )                          % e.g., Eclipse
            ; Goal = interpreted : V,  var( V )    % e.g., Sicstus
            )
        ->
            error( [ 'A variable meta-call: ', call( Goal ) ] )
        ;
            solve( Goal, Stack, Hyp, Level )
        ).


% assert/1

solve( assert( Clause ), _, _, _ ) :-
        !,
        (
            \+ is_a_good_clause( Clause )
        ->
            error( [ 'Bad clause argument: ', assert( Clause ) ] )
        ;
            true
        ),
        incval( step_counter ),
        assert_in_module( interpreted, Clause ).


% retractall/1

solve( retractall( C ), _, _, _ ) :-
        !,
        incval( step_counter ),
        retractall_in_module( interpreted, C ).


% findall/3: note that this is not opaque to coinductive and tabled ancestors!

solve( findall( Template, Goal, Bag ), Stack, Hyp, Level ) :-
        !,
        NLevel is Level + 1,
        (
            % Sicstus prefixes the second argument of findall with the module
            % name, but it does not do that for nested findall...
            lp_system( sicstus ),
            Goal = interpreted: G
        ->
            true
        ;
            G = Goal
        ),
        findall( Template, solve( G, Stack, Hyp, NLevel ), Bag ).


% Some other supported built-in.

solve( BuiltIn, _, _, _ ) :-
        builtin( BuiltIn ),
        !,
        incval( step_counter ),
        call( BuiltIn ).


% A "support" predicate

solve( Goal, _, _, _ ) :-
        support( Goal ),
        !,
        incval( step_counter ),
        call_in_module( support, Goal ).


% A "normal" goal (i.e., not tabled, not coinductive).

solve( Goal, Stack, Hyp, Level ) :-
        \+ tabled( Goal ),
        \+ coinductive1( Goal ),
        !,
        incval( step_counter ),
        trace_entry( normal, Goal, '?', Level ),
        (
            NLevel is Level + 1,
            use_clause( Goal, Body ),
            solve( Body, Stack, Hyp, NLevel ),
            trace_success( normal, Goal, '?', Level )
        ;
            trace_failure( normal, Goal, '?', Level ),
            fail
        ).


% A goal that is coinductive, but not tabled.
% Apply the coinductive hypotheses first, then the clauses.
%
% NOTE: Now that we have both "coinductive" and "coinductive2" the logic gets a
%       little tricky.  If a goal is not "coinductive2", then it should activate
%       its clauses only if there are no unifiable ancestors (hypotheses). What
%       follows is an attempt to avoid too much duplication of code and
%       redundant invocations of the costly check for unifiable ancestors.

solve( Goal, Stack, Hyp, Level ) :-
        \+ tabled( Goal ),
        coinductive1( Goal ),
        !,
        incval( step_counter ),
        trace_entry( coinductive, Goal, '?', Level ),
        (
            \+ coinductive( Goal ),
            unify_with_coinductive_ancestor( Goal, Hyp )
        ->
            (
                trace_success( 'coinductive (hypothesis)', Goal, '?', Level )
            ;
                trace_failure( coinductive, Goal, '?', Level ),
                fail
            )
        ;
            % coinductive, or no unifiable ancestors
            (
                coinductive( Goal ),
                unify_with_coinductive_ancestor( Goal, Hyp ),
                trace_success( 'coinductive (hypothesis)', Goal, '?', Level )
            ;
                NLevel is Level + 1,
                use_clause( Goal, Body ),
                push_coinductive( Goal, Hyp, NHyp ),
                solve( Body, Stack, NHyp, NLevel ),
                trace_success( 'coinductive (clause)', Goal, '?', Level )
            ;
                trace_failure( coinductive, Goal, '?', Level ),
                fail
            )
        ).



% A tabled goal that has been completed: all the results are in "answer".

solve( Goal, _, _, Level ) :-
        is_completed( Goal ),
        !,
        incval( step_counter ),
        trace_entry( completed, Goal, '?', Level ),
        (
            get_all_tabled_answers( Goal, '?', completed, Level )
        ;
            trace_failure( completed, Goal, '?', Level ),
            fail
        ).


% A tabled goal that has a variant among its ancestors (and has not been
% completed).
% If the goal is not coinductive, only the existing (most likely incomplete)
% results from "answer" are  returned before failure.
% If the goal is also coinductive, return the results that arise from
% coinductive hypotheses, then the remaining results from "answer".
%
% NOTE: 1. There can be only one variant ancestor, so the question of which one
%          to use does not arise.
%
%       2. Ancestor pioneer goals between this goal and its variant ancestor
%          will lose their status as pioneers (and the associated entries in
%          "loop" and "looping_alternative" will be removed).
%
%       3. If the variant ancestor is a pioneer, then:
%             - the entire prefix of the list of goals upto (but not including)
%               the variant ancestor will be added to the cluster of that
%               ancestor (by storing it in "loop");
%             - a copy of the current clause invoked by the ancestor (which can
%               be found together with the ancestor on the stack) is added to
%               "looping_alternative" entries for that ancestor.
%
%       4. If this goal is coinductive, then we use "result" to avoid
%          duplicating results.

solve( Goal, Stack, Hyp, Level ) :-
        is_variant_of_ancestor( Goal, Stack,
                                triple( G, I, C ), InterveningTriples
                              ),
        !,
        incval( step_counter ),
        get_unique_index( Index ),
        trace_entry( variant, Goal, Index, Level ),
        % Rescind the status of intervening pioneers:
        suppress_pioneers_on_list( InterveningTriples, Level ),

        % Create a looping alternative if the variant ancestor is a pioneer:
        (
            is_a_variant_of_a_pioneer( G, I )
        ->
            extract_goals( InterveningTriples, InterveningGoals ),
            add_loop( I, InterveningGoals ),
            add_looping_alternative( I, C )
        ;
            true
        ),

        % The main action:
        (
            coinductive1( Goal )
        ->
            copy_term2( Goal, OriginalGoal ),
            (
                get_tabled_if_old_first( Goal, Index,
                                         'variant (coinductive)', Level
                                       )
            ;
                % results from coinductive hypotheses:
                unify_with_coinductive_ancestor( Goal, Hyp ),
                \+ is_answer_known( OriginalGoal, Goal ),    % postpone "old"
                memo( OriginalGoal, Goal, Level ),
                new_result_or_fail( Index, Goal ),           % i.e., note answer
                trace_success( 'variant (coinductive)', Goal, Index, Level )
            ;
                % other tabled results
                get_remaining_tabled_answers( Goal, Index, variant, Level )
            ;
                % wrap it up
                trace_failure( 'variant (coinductive)', Goal, Index, Level ),
                retractall( result( Index, _ ) ),
                fail
            )
        ;

            % Not coinductive, just sequence through tabled answers:
            (
                get_all_tabled_answers( Goal, Index, variant, Level )
            ;
                trace_failure( variant, Goal, Index, Level ),
                retractall( result( Index, _ ) ),
                fail
            )
        ).


% A pioneer goal is solved by program clauses, producing results that are stored
% in "answer".
% The goal succeeds as each new answer (i.e., an answer heretofore unknown for
% this goal) is produced, and tries to come up with more after backtracking.
% When the usual clauses are exhausted, clauses stored in the associated entries
% of "looping_alternative" will be used to produce more answers (but only those
% that have not yet been produced by the goal), until a fixed point is reached.
% The pioneer (and all the goals in its cluster) will then be marked as
% complete, and will cease to be a pioneer.
%
% Note that a pioneer may also lose its status when some descendant goal finds
% a variant ancestor that is also an ancestor of the pioneer.  See the case
% of "variant of ancestor" above.
%
% Note also that a goal might become completed after it succeeded (because
% another variant goal "on the right" has completed), so after backtracking it
% might not be necessary to continue the computation with the remaining clauses:
% the rest of the results should be picked up from the table, instead.

solve( Goal, Stack, Hyp, Level ) :-
        (
            coinductive1( Goal )
        ->
            push_coinductive( Goal, Hyp, NHyp )
        ;
            NHyp = Hyp
        ),
        incval( step_counter ),
        copy_term2( Goal, OriginalGoal ),
        add_pioneer( Goal, Index ),
        trace_entry( pioneer, Goal, Index, Level ),

        (
            get_tabled_if_old_first( Goal, Index, pioneer, Level )
        ;

            NLevel is Level + 1,
            use_clause( Goal, Body ),
            \+ is_completed( OriginalGoal ), % might well be, after backtracking
            copy_term2( (Goal :- Body), ClauseCopy ),
            push_tabled( OriginalGoal, Index, ClauseCopy, Stack, NStack ),
            solve( Body, NStack, NHyp, NLevel ),
            \+ is_answer_known( OriginalGoal, Goal ),   % postpone "old" answers
            memo( OriginalGoal, Goal, Level ),
            new_result_or_fail( Index, Goal ),          % i.e., note the answer
            trace_success( pioneer, Goal, Index, Level )
        ;

            % All the clauses have been exhausted, except for looping
            % alternatives (if any).  However, the goal may have become
            % completed (by a later variant), or it might have lost its pioneer
            % status (because it belongs to a larger loop).

            is_completed( Goal )                      % a variant has completed?
        ->
            trace_other( 'Removing completed pioneer', Goal, Index, Level ),
            rescind_pioneer_status( Index ),
            get_remaining_tabled_answers( Goal, Index, 'completed now', Level )
        ;

            is_a_variant_of_a_pioneer( Goal, Index )  % not lost pioneer status?
        ->
            (
                trace_other( 'Computing fixed point for', Goal, Index, Level ),
                compute_fixed_point( Goal, Index, Stack, Hyp, Level ),
                \+ new_result_or_fail( Index, Goal ),
                trace_success( pioneer, Goal, Index, Level )
            ;
                trace_other( 'Fixed point computed', Goal, Index, Level ),
                complete_goal( Goal, Level ),
                complete_cluster( Index, Level ),
                trace_other( 'Removing pioneer', Goal, Index, Level ),
                rescind_pioneer_status( Index ),
                get_remaining_tabled_answers( Goal, Index,
                                              'completed now', Level
                                            )
            ;
                retractall( result( Index, _ ) ),
                fail
            )
        ;

            (
                % No longer a pioneer and not completed, so just sequence
                % through the remaining available tabled answers.
                get_remaining_tabled_answers( Goal, Index,
                                              '(no longer a pioneer)', Level
                                            )
            ;
                trace_failure( '(no longer a pioneer)', Goal, Index, Level ),
                retractall( result( Index, _ ) ),
                fail
            )
        ).



%% get_tabled_if_old_first( + goal, + goal index,
%%                          + trace label, + trace level
%%                        ):
%% If the goal has been declared as "old_first", produce all the tabled answers,
%% remembering them in "result", then succeed; otherwise just fail.

% :- mode get_tabled_if_old_first( +, +, +, + ).

get_tabled_if_old_first( Goal, Index, Label, Level ) :-
        old_first( Goal ),
        get_all_tabled_answers( Goal, Index, Label, Level ),
        new_result_or_fail( Index, Goal ).     % i.e., make a note of the answer


%% get_all_tabled_answers( + goal, + goal index, + trace label, + trace level ):
%% Return (one by one) all the answers that are currently tabled for this goal.
%% (Each answer is returned by appropriately instantiating the goal.)

% :- mode get_all_tabled_answers( +, +, +, + ).

get_all_tabled_answers( Goal, Index, Label, Level ) :-
        get_answer( Goal ),
        trace_success( Label, Goal, Index, Level ).


%% get_remaining_tabled_answers( + goal,        + goal index,
%%                               + trace label, + trace level
%%                             ):
%% Return (one by one) all the answers that are currently tabled for this goal
%% but are not present in its "result" entries.
%% (Each answer is returned by appropriately instantiating the goal.)

% :- mode get_remaining_tabled_answers( +, +, +, + ).

get_remaining_tabled_answers( Goal, Index, Label, Level ) :-
        get_answer( Goal ),
        \+ is_result_known( Index, Goal ),
        trace_success( Label, Goal, Index, Level ).



%% use_clause( + goal, - body ):
%% Warn and fail if the goal invokes a non-existing predicate.  Otherwise
%% nondeterministically return the appropriately instantiated body of each
%% clause whose head matches the goal.

use_clause( Goal, Body ) :-
        (
            functor( Goal, P, K ),
            current_predicate_in_module( interpreted, P/K )
        ->
            clause_in_module( interpreted, Goal, Body )
        ;
            warning( [ 'Calling an undefined predicate: \"', Goal, '\"' ] ),
            fail
        ).



%% compute_fixed_point( + pioneer goal, + its index, + stack, + level ):
%% Solve the goal by associated rules from "looping_alternative", succeeding
%% with each new answer (and tabling it).  Fail when all the possible results
%% are exhausted.

% :- mode compute_fixed_point( +, +, +, +, + ).

compute_fixed_point( Goal, Index, Stack, Hyp, Level ) :-
        NLevel is Level + 1,
        (
            coinductive1( Goal )
        ->
            push_coinductive( Goal, Hyp, NHyp )
        ;
            NHyp = Hyp
        ),
        getval( number_of_answers, NAns ),
        compute_fixed_point_( Goal, Index, Stack, NHyp, NLevel, NAns ).

%
% :- mode compute_fixed_point_( +, +, +, +, +, + ).

compute_fixed_point_( Goal, Index, Stack, Hyp, Level, _ ) :-
        copy_term2( Goal, OriginalGoal ),
        get_looping_alternative( Index, (G :- Body) ),        % i.e., iterate
        \+ \+ G = Goal,
        copy_term2( (G :- Body), ClauseCopy ),
        G = Goal,
        push_tabled( OriginalGoal, Index, ClauseCopy, Stack, NStack ),
        solve( Body, NStack, Hyp, Level ),
        new_result_or_fail( Index, Goal ),
        memo( OriginalGoal, Goal, Level ).

compute_fixed_point_( Goal, Index, Stack, Hyp, Level, NAns ) :-
        getval( number_of_answers, NAnsNow ),
        NAnsNow \= NAns,                % i.e., fail if there are no new answers
        compute_fixed_point_( Goal, Index, Stack, Hyp, Level, NAnsNow ).



%% suppress_pioneers_on_list( + list of triples, + level for tracing ):
%% If any of the triples describe goals that are pioneers, make sure those goals
%% cease to be pioneers.

suppress_pioneers_on_list( Triples, Level ) :-
        member( triple( M, MI, _ ), Triples ),
        is_a_variant_of_a_pioneer( M, MI ),
        trace_other( 'Removing pioneer', M, MI, Level ),
        rescind_pioneer_status( MI ),
        fail.

suppress_pioneers_on_list( _, _ ).



%% rescind_pioneer_status( + index ):
%% Remove auxiliary table entries for the pioneer with this index.
%% Specifically, clean up "pioneer", "loop" and "looping_alternative".

% :- mode rescind_pioneer_status( + ).

rescind_pioneer_status( Index ) :-
        delete_pioneer( Index ),
        delete_loops( Index ),
        delete_looping_alternatives( Index ).


%% complete_cluster( + index of a pioneer goal, + level for tracing ):
%% If the goal has an associated cluster, make sure all the goals in the cluster
%% are marked as completed.
%% Recall that a cluster may consist of a number of "loops".

% :- mode complete_cluster( +, + ).

complete_cluster( Index, Level ) :-
        get_loop( Index, Gs ),                  % iterate over loops
        member( G, Gs ),                        % iterate over members of a loop
        complete_goal( G, Level ),
        fail.

complete_cluster( _, _ ).



%% extract_goals( + list of triples of goals, indices and clauses,
%%                - list of goals
%%              ):
%% Filter away the other info in each triple, return list of goals only.

% :- mode extract_goals( +, - ).

extract_goals( [], [] ).

extract_goals( [ triple( G, _, _ ) | Ts ], [ G | Gs ] ) :-
        extract_goals( Ts, Gs ).





%%-----  The tables: access and modification  -----

%% NOTE: See file dra_table_assert.pl or dra_table_record.pl for manipulation of
%%       the tables "answer", "result", "pioneer", "loop",
%%       "looping_alternative" and "completed".


%% get_unique_index( - ):
%% Produce a new unique index.

% :- mode get_unique_index( - ).

get_unique_index( Index ) :-
        getval( unique_index, Index ),
        incval( unique_index ).





%%-----  Custom-tailored utilities  -----


%% are_essences_variants( + term, + term ):
%% Are both the terms variants of each other after filtering through
%% essence_hook?

% :- mode are_essences_variants( +, + ).

are_essences_variants( T1, T2 ) :-
        once( essence_hook( T1, ET1 ) ),
        once( essence_hook( T2, ET2 ) ),
        are_variants( ET1, ET2 ).



%% trace_entry( + label, + goal, + goal index, + level ):
%% If the goal matches one of the traced patterns, print out a trace line about
%% entering the goal (at this level, with this label).
%% (The goal index is not always relevant: "?" is used for those cases.)

trace_entry( Label, Goal, Index, Level ) :-
        tracing( Goal ),
        !,
        write_level( Level ),
        std_output_stream( Output ),
        write( Output, 'Entering ' ),
        write_label_and_goal( Label, Goal, Index ),
        nl( Output ).

trace_entry( _, _, _, _ ).


%% trace_success( + label, + goal, + goal index, + level ):
%% If the goal matches one of the traced patterns, print out a trace line about
%% success of the goal (at this level, with this label).  Moreover, just before
%% backtracking gets back to the goal, print out a trace line about retrying the
%% goal.
%% (The goal index is not always relevant: "?" is used for those cases.)

trace_success( Label, Goal, Index, Level ) :-
        tracing( Goal ),
        !,
        std_output_stream( Output ),
        (
            write_level( Level ),
            write( Output, 'Success ' ),
            write_label_and_goal( Label, Goal, Index ),
            nl( Output )
        ;
            write_level( Level ),
            write( Output, 'Retrying ' ),
            write_label_and_goal( Label, Goal, Index ),
            nl( Output ),
            fail
        ).

trace_success( _, _, _, _ ).


%% trace_failure( + label, + goal, + goal index, + level ):
%% If the goal matches one of the traced patterns, print out a trace line about
%% failure of the goal (at this level, with this label).
%% (The goal index is not always relevant: "?" is used for those cases.)

trace_failure( Label, Goal, Index, Level ) :-
        tracing( Goal ),
        !,
        write_level( Level ),
        std_output_stream( Output ),
        write( Output, 'Failing ' ),
        write_label_and_goal( Label, Goal, Index ),
        nl( Output ).

trace_failure( _, _, _, _ ).


%% trace_other( + label, + goal, + goal index, + level ):
%% If the goal matches one of the traced patterns, print out a trace line about
%% this goal (at this level, with this label).
%% (The goal index is not always relevant: "?" is used for those cases.)

trace_other( Label, Goal, Index, Level ) :-
        tracing( Goal ),
        !,
        write_level( Level ),
        write_label_and_goal( Label, Goal, Index ),
        std_output_stream( Output ),
        nl( Output ).

trace_other( _, _, _, _ ).


%% Auxiliaries for tracing:

write_level( Level ) :-
        std_output_stream( Output ),
        write( Output, '[' ),
        write( Output, Level ),
        write( Output, '] ' ).

write_label_and_goal( Label, Goal, Index ) :-
        print_depth( Depth ),
        std_output_stream( Output ),
        write( Output, Label ),
        write( Output, ': ' ),
        write_goal_number( Index ),
        write_shallow( Output, Goal, Depth ).


write_goal_number( '?' ) :-
        !.

write_goal_number( Index ) :-
        std_output_stream( Output ),
        write( Output, '<' ),
        write( Output, Index ),
        write( Output, '> ' ).



%% optional_trace( + label, + goal, + term, + level ):
%% If the goal matches one of the traced patterns, print out a trace line with
%% this label, the goal and the term.

optional_trace( Label, Goal, Term, Level ) :-
        tracing( Goal ),
        !,
        print_depth( Depth ),
        write_level( Level ),
        std_output_stream( Output ),
        write(         Output, Label ),
        write_shallow( Output, Goal, Depth ),
        write(         Output, ' : ' ),
        write_shallow( Output, Term, Depth ),
        nl(            Output ).

optional_trace( _, _, _, _ ).



%% fatal_error( + message, + stack ):
%% Display the message and stack, then abort.

% :- mode fatal_error( +, + ).

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

%%------------------------------------------------------------------------------
