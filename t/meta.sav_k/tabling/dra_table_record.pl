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

%%%  Table-handling procedures for the "dra" interpreter.                    %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (March 2009)           .              %%%
%%%                                                                          %%%
%%%  Last update: 27 August 2009.                                            %%%
%%%                                                                          %%%

%% The tables are normally kept in asserted clauses, but for some systems this
%% is not convenient, because asserted clauses are compiled.
%% For example, this is so in SWI Prolog, which in addition does not assert
%% cyclic terms, so  for that system the "recorded" database is more
%% appropriate.
%% In order to facilitate such changes, routines for handling the table is
%% factored out of the main program.



%% >>>>>>>>>  This version for systems that use the recorded database. <<<<<<<<<


%------------------------------------------------------------------------------

%% ensure_recorded( + key, + item ):
%% Make sure that the item is recorded in the database.

ensure_recorded( Key, Item ) :-
        (
            recorded( Key, Item )
        ->
            true
        ;
            recordz( Key, Item )
        ).




%------------------------------------------------------------------------------

%% Each item recorded for table "answer" is of the form
%% "answer( Filter, Goal, Fact )", where "Filter" is the essence of a copy of
%% "Goal".
%% The item is recorded under the key "Goal" , i.e., effectively the key is the
%% principal functor of the goal.  A most general instance of the key is
%% additionally recorded under the key "answer_key".


%% Clear all known answers (and keys).

reinitialise_answer :-
        recorded( answer_key, Key, RefKey ),
        erase( RefKey ),
        recorded( Key, answer( _, _, _ ), RefAnswer ),
        erase( RefAnswer ),
        fail.

reinitialise_answer.


%% is_answer_known( + goal, + fact ):
%% Does the table "answer" contain a variant of this fact paired with a variant
%% of this goal?

% :- mode is_answer_known( +, + ).

is_answer_known( Goal, Fact ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recorded( Goal, answer( CopyEssence, G, F ) ),
        are_essences_variants( G, Goal ),
        are_essences_variants( F, Fact ),
        !.


%% memo( + goal, + fact, + level for tracing ):
%% If the table "answer" does not contain a variant of this fact paired with
%% a variant of this goal, then add the pair to the table, increasing
%% "number_of_answers".

% :- mode memo( +, +, + ).

memo( Goal, Fact, _ ) :-
        is_answer_known( Goal, Fact ),
        !.

memo( Goal, Fact, Level ) :-
        % \+ is_answer_known( Goal, Fact ),
        optional_trace( 'Storing answer: ', Goal, Fact, Level ),
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recordz( Goal, answer( CopyEssence, Goal, Fact ) ),
        most_general_instance( Goal, Key ),
        ensure_recorded( answer_key, Key ),
        incval( number_of_answers ).


%% get_answer( +- goal ):
%% Get an instantiation (if any) tabled in "answer" for variants of this goal.
%% Sequence through all such instantiations on backtracking.

% :- mode get_answer( ? ).

get_answer( Goal ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        once( essence_hook( Goal, EssenceOfGoal ) ),
        recorded( Goal, answer( CopyEssence, G, Ans ) ),
        once( essence_hook( G, EssenceOfG ) ),
        are_variants( EssenceOfGoal, EssenceOfG ),
        EssenceOfGoal = EssenceOfG,     % make sure variables are the right ones
        once( essence_hook( Ans, EssenceOfAns ) ),
        EssenceOfGoal = EssenceOfAns .  % instantiate


%% get_all_tabled_goals( - list of goals ):
%% Get all the goals that were tabled together with their answers.

get_all_tabled_goals( Goals ) :-
        findall( Goal,
                 (recorded( answer_key, Key ),
                  recorded( Key, answer( _, Goal, _ ) )
                 ),
                 Goals
               ).



%------------------------------------------------------------------------------

%% Each item recorded for table "result" is of the form "result( Fact )".
%% The item is recorded under the key "Index".  The index is additionally
%% recorded under the key "result_key".

%% reinitialise_result:
%% Clear the result table.
reinitialise_result :-
        recorded( result_key, Index, RefIndex ),
        erase( RefIndex ),
        recorded( Index, result( _ ), RefResult ),
        erase( RefResult ),
        fail.

reinitialise_result.


%% is_result_known( + index, + fact ):
%% Does the table "result" contain a variant of this fact associated with this
%% index?

% :- mode is_result_known( +, + ).

is_result_known( Index, Fact ) :-
        recorded( Index, result( F ) ),
        are_essences_variants( F, Fact ),
        !.


%% new_result_or_fail( + index, + fact ):
%% If the table "result" already contains a variant of this fact associated with
%% this index, then fail.  Otherwise record the fact in the table and succeed.

% :- mode new_result_or_fail( +, + ).

new_result_or_fail( Index, Fact ) :-
        \+ is_result_known( Index, Fact ),
        recordz( Index, result( Fact ) ),
        ensure_recorded( result_key, Index ).



%-------------------------------------------------------------------------------

%% Each item recorded for table "pioneer" is of the form
%% "pioneer( Filter, Goal, Index )" (where "Index" is unique and "Filter" is the
%% essence of a copy of "Goal".
%% The item is recorded under the key "Goal" , i.e., effectively the key is the
%% principal functor of the goal.  A most general instance of the goal is
%% additionally  recorded under the key "pioneer_key".
%% Moreover, to speed up delete_pioneer/1, the key is recorded also as
%% "pioneer_goal( Key )" under the key "Index".


%% reinitialise_pioneer:
%% Clear the table of pioneers.

reinitialise_pioneer :-
        recorded( pioneer_key, Key, RefIndex ),
        erase( RefIndex ),
        recorded( Key, pioneer( _, _, _ ), RefResult ),
        erase( RefResult ),
        fail.

reinitialise_pioneer.


%% is_a_variant_of_a_pioneer( + goal, - index ):
%% Succeeds if the goal is a variant of a goal that is tabled in "pioneer";
%% returns the index of the relevant entry in table "pioneer".

% :- mode is_a_variant_of_a_pioneer( +, - ).

is_a_variant_of_a_pioneer( Goal, Index ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recorded( Goal, pioneer( CopyEssence, G, Index ) ),
        are_essences_variants( Goal, G ),
        !.


%% add_pioneer( + goal, - index ):
%% Add an entry for this goal to "pioneer", return the unique index.

% :- mode add_pioneer( +, - ).

add_pioneer( Goal, Index ) :-
        get_unique_index( Index ),
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recordz( Goal, pioneer( CopyEssence, Goal, Index ) ),
        most_general_instance( Goal, Key ),
        ensure_recorded( pioneer_key, Key ),
        recordz( Index, pioneer_goal( Key ) ).


%% delete_pioneer( + index ):
%% Remove the entry in "pioneer" associated with this index.

% :- mode delete_pioneer( + ).

delete_pioneer( Index ) :-
        recorded( Index, pioneer_goal( Key ), RefIndex ),
        erase( RefIndex ),
        recorded( Key, pioneer( _, _, Index ), RefPioneer ),
        erase( RefPioneer ).



%-------------------------------------------------------------------------------

%% Each item recorded for table "loop" is of the form "loop( Goals )".
%% The item is recorded under the key "Index", where "Index" is the index
%% associated with the loop.
%% The index is additionally recorded under the key "loop_key".


%% reinitialise_loop:
%% Clear the table of pioneers.

reinitialise_loop :-
        recorded( loop_key, Index, RefIndex ),
        erase( RefIndex ),
        delete_loops( Index ),
        fail.

reinitialise_loop.


%% delete_loops( + index ):
%% Remove all the entries in "loop" that are associated with this index.

delete_loops( Index ) :-
        recorded( Index, loop( _ ), RefLoop ),
        erase( RefLoop ),
        fail.

delete_loops( _ ).


%% add_loop( + index, + list of goals ):
%% Add an entry to "loop".

% :- mode add_loop( +, + ).

add_loop( _, [] ) :-                                % empty loops are not stored
        !.

add_loop( Index, Goals ) :-                         % neither are duplicates
        get_loop( Index, Gs ),
        are_variants( Goals, Gs ),
        !.

add_loop( Index, Goals ) :-
        recordz( Index, loop( Goals ) ),
        ensure_recorded( loop_key, Index ).


%% get_loop( + index, - Goals ):
%% Get an entry from table "loop" that is associated with this index;
%% another such entry (if it exists) on backtracking etc.

get_loop( Index, Gs ) :-
        recorded( Index, loop( Gs ) ).



%-------------------------------------------------------------------------------

%% Each item recorded for table "looping_alternative" is of the form
%% "looping_alternative( Clause )".
%% The item is recorded under the key "Index", where "Index" is the index
%% associated with the looping_alternative.
%% The index is additionally recorded under the key "looping_alternative_key".


%% reinitialise_looping_alternative:
%% Clear the table of pioneers.

reinitialise_looping_alternative :-
        recorded( looping_alternative_key, Index, RefIndex ),
        erase( RefIndex ),
        delete_looping_alternatives( Index ),
        fail.

reinitialise_looping_alternative.


%% delete_looping_alternatives( + index ):
%% Remove all the entries in "loop" that are associated with this index.

delete_looping_alternatives( Index ) :-
        recorded( Index, looping_alternative( _ ), RefLoop ),
        erase( RefLoop ),
        fail.

delete_looping_alternatives( _ ).


%% add_looping_alternative( + index, + Clause ):
%% Add and entry to "looping_alternative".

% :- mode add_looping_alternative( +, + ).

add_looping_alternative( Index, Clause ) :-          % duplicates are not stored
        get_looping_alternative( Index, C ),
        are_variants( Clause, C ),
        !.

add_looping_alternative( Index, Clause ) :-
        recordz( Index, looping_alternative( Clause ) ),
        ensure_recorded( looping_alternative_key, Index ).


%% get_looping_alternative( + index, - clause ):
%% Get an entry from table "looping_alternative" that is associated with this
%% index; another such entry (if it exists) on backtracking etc.

get_looping_alternative( Index, Clause ) :-
        recorded( Index, looping_alternative( Clause ) ).



%-------------------------------------------------------------------------------

%% Each item recorded for table "completed" is of the form
%% "completed( Filter, Goal )", where "Filter" is the essence of a copy of
%% "Goal".
%% The item is recorded under the key "Goal" , i.e., effectively the key is the
%% principal functor of the goal.  A most general instance of the goal is
%% additionally recorded under the key "completed_key".


%% reinitialise_completed:
%% Clear the table of completed goals.

reinitialise_completed :-
        recorded( completed_key, Key , RefIndex ),
        erase( RefIndex ),
        recorded( Key, completed( _, _ ), RefResult ),
        erase( RefResult ),
        fail.

reinitialise_completed.


%% is_completed( + goal ):
%% Succeeds iff the goal is a variant of a goal that has been stored in
%% the table "completed".

% :- mode is_completed( + ).

is_completed( Goal ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recorded( Goal, completed( CopyEssence, G ) ),
        are_essences_variants( Goal, G ).


%% complete_goal( + goal, + index for tracing ):
%% Make sure the goal is marked as completed.

% :- mode complete_goal( +, + ).

complete_goal( Goal, _ ) :-
        is_completed( Goal ),
        !.

complete_goal( Goal, Level ) :-
        % \+ is_completed( Goal ),
        trace_other( 'Completing', Goal, '?', Level ),
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        recordz( Goal, completed( CopyEssence, Goal ) ),
        most_general_instance( Goal, Key ),
        ensure_recorded( completed_key, Key ).

%-------------------------------------------------------------------------------
