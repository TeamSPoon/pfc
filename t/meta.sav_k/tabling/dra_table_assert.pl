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
%%%  Last update: 25 August 2009.                                            %%%
%%%                                                                          %%%

%% The tables are normally kept in asserted clauses, but for some systems this
%% is  not convenient, because asserted clauses are compiled.
%% For example, this is so in SWI Prolog, which in addition does not assert
%% cyclic terms, so  for that system the "recorded" database is more
%% appropriate.
%% In order to facilitate such changes, routines for handling the table is
%% factored out of the main program.



%% >>>>>>>>>  This version for systems that use assert/1. <<<<<<<<<

:- dynamic answer/3 .


%% Clear all known answers.

reinitialise_answer :-
        retractall( answer( _, _, _ ) ).


%% is_answer_known( + goal, + fact ):
%% Does the table "answer" contain a variant of this fact paired with a variant
%% of this goal?

% :- mode is_answer_known( +, + ).

is_answer_known( Goal, Fact ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        answer( CopyEssence, G, F ),
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
        assert( answer( CopyEssence, Goal, Fact ) ),
        incval( number_of_answers ).


%% get_answer( +- goal ):
%% Get an instantiation (if any) tabled in "answer" for variants of this goal.
%% Sequence through all such instantiations on backtracking.

% :- mode get_answer( ? ).

get_answer( Goal ) :-
        once( essence_hook( Goal, EssenceOfGoal ) ),
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        answer( CopyEssence, G, Ans ),
        once( essence_hook( G, EssenceOfG ) ),
        are_variants( EssenceOfGoal, EssenceOfG ),
        EssenceOfGoal = EssenceOfG,     % make sure variables are the right ones
        once( essence_hook( Ans, EssenceOfAns ) ),
        EssenceOfGoal = EssenceOfAns .  % instantiate


%% get_all_tabled_goals( - list of goals ):
%% Get all the goals that were tabled together with their answers.

get_all_tabled_goals( Goals ) :-
        findall( Goal, answer( _, Goal, _ ), Goals ).



%------------------------------------------------------------------------------

%% reinitialise_result:
%% Clear the table of results.

reinitialise_result :-
        retractall( result( _, _ ) ).


%% is_result_known( + index, + fact ):
%% Does the table "result" contain a variant of this fact associated with this
%% index?

% :- mode is_result_known( +, + ).

is_result_known( Index, Fact ) :-
        result( Index, F ),
        are_essences_variants( F, Fact ),
        !.


%% new_result_or_fail( + index, + fact ):
%% If the table "result" already contains a variant of this fact associated with
%% this index, then fail.  Otherwise record the fact in the table and succeed.

% :- mode new_result_or_fail( +, + ).

new_result_or_fail( Index, Fact ) :-
        \+ is_result_known( Index, Fact ),
        assert( result( Index, Fact ) ).



%-------------------------------------------------------------------------------

%% reinitialise_pioneer:
%% Clear the table of pioneers.

reinitialise_pioneer :-
        retractall( pioneer( _, _, _ ) ).

%% is_a_variant_of_a_pioneer( + goal, - index ):
%% Succeeds if the goal is a variant of a goal that is tabled in "pioneer";
%% returns the index of the relevant entry in table "pioneer".

% :- mode is_a_variant_of_a_pioneer( +, - ).

is_a_variant_of_a_pioneer( Goal, Index ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        pioneer( CopyEssence, G, Index ),
        are_essences_variants( Goal, G ),
        !.


%% add_pioneer( + goal, - index ):
%% Add an entry for this goal to "pioneer", return the unique index.

% :- mode add_pioneer( +, - ).

add_pioneer( Goal, Index ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        get_unique_index( Index ),
        assert( pioneer( CopyEssence, Goal, Index ) ).


%% delete_pioneer( + index ):
%% Remove the entry in "pioneer" associated with this index.

% :- mode delete_pioneer( + ).

delete_pioneer( Index ) :-
        retract( pioneer( _, _, Index )).



%-------------------------------------------------------------------------------

%% reinitialise_loop:
%% Clear the table of pioneers.

reinitialise_loop :-
        retractall( loop( _, _ ) ).


%% add_loop( + index, + list of goals ):
%% Add an entry to "loop".

% :- mode add_loop( +, + ).

add_loop( _, [] ) :-                                % empty loops are not stored
        !.

add_loop( Index, Goals ) :-                         % neither are duplicates
        loop( Index, Gs ),
        are_variants( Goals, Gs ),
        !.

add_loop( Index, Goals ) :-
        assert( loop( Index, Goals ) ).


%% delete_loops( + index ):
%% Remove all the entries in "loop" that are associated with this index.

delete_loops( Index ) :-
        retractall( loop( Index, _ ) ).


%% get_loop( + index, - Goals ):
%% Get an entry from table "loop" that is associated with this index;
%% another such entry (if it exists) on backtracking etc.

get_loop( Index, Gs ) :-
        loop( Index, Gs ).



%-------------------------------------------------------------------------------

%% reinitialise_looping_alternative:
%% Clear the table of pioneers.

reinitialise_looping_alternative :-
        retractall( looping_alternative( _, _ ) ).


%% add_looping_alternative( + index, + Clause ):
%% Add and entry to "looping_alternative".

% :- mode add_looping_alternative( +, + ).

add_looping_alternative( Index, Clause ) :-          % duplicates are not stored
        looping_alternative( Index, C ),
        are_variants( Clause, C ),
        !.

add_looping_alternative( Index, Clause ) :-
        assert( looping_alternative( Index, Clause ) ).


%% delete_looping_alternatives( + index ):
%% Remove all the entries in "loop" that are associated with this index.

delete_looping_alternatives( Index ) :-
        retractall( looping_alternative( Index, _ ) ).


%% get_looping_alternative( + index, - clause ):
%% Get an entry from table "looping_alternative" that is associated with this
%% index; another such entry (if it exists) on backtracking etc.

get_looping_alternative( Index, Clause ) :-
        looping_alternative( Index, Clause ).



%-------------------------------------------------------------------------------

%% reinitialise_completed:
%% Clear the table of completed goals.

reinitialise_completed :-
        retractall( completed( _, _ ) ).


%% is_completed( + goal ):
%% Succeeds iff the goal is a variant of a goal that has been stored in
%% the table "completed".

% :- mode is_completed( + ).

is_completed( Goal ) :-
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        completed( CopyEssence, G ),
        are_essences_variants( Goal, G ).


%% complete_goal( + goal, + index for tracing ):
%% Make sure the goal is marked as completed.

% :- mode complete_goal( +, + ).

complete_goal( Goal, _ ) :-
        is_completed( Goal ),
        !.

complete_goal( Goal, Level ) :-
        % \+ is_completed( Goal ),
        copy_term2( Goal, Copy ),
        once( essence_hook( Copy, CopyEssence ) ),
        trace_other( 'Completing', Goal, '?', Level ),
        assert( completed( CopyEssence, Goal ) ).

%-------------------------------------------------------------------------------
