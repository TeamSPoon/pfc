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

%%%  A goal table implemented by an open list.                               %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (February 2009).                      %%%
%%%                                                                          %%%
%%%  Last update: 30 March 2009.                                             %%%
%%%                                                                          %%%

:- ensure_loaded( utilities ).
:- ensure_loaded( olist ).


%%% In this implementation the goal table is just an open list.


%%------------------------------------------------------------------------------
%% empty_goal_table( +- goal table ):
%% Create an empty goal table, or check that the provided table is empty.

empty_goal_table( Table ) :-
        empty_olist( Table ).


%%------------------------------------------------------------------------------
%% goal_table_member( + goal, + goal table ):
%% Check whether any instantiations of the goal are in the table: if there are,
%% unify the goal with the first one (backtracking will unify it with each of
%% them in turn).
%%
%% NOTE: Use essence hook before comparison!

goal_table_member( Goal, Table ) :-
        once( essence_hook( Goal, Essence ) ),
        olist_member_reversed( G, Table ),
        once( essence_hook( G, Essence ) ).


%%------------------------------------------------------------------------------
%% is_a_variant_in_goal_table( + goal, + goal table ):
%% Succeed iff a variant of this goal is present in the table.
%% Do not modify the goal.
%%
%% NOTE: Use essence hook before comparison!

is_a_variant_in_goal_table( Goal, Table ) :-
        once( essence_hook( Goal, GoalEssence ) ),
        olist_member( Member, Table ),
        once( essence_hook( Member, MemberEssence ) ),
        are_variants( MemberEssence, GoalEssence ),
        !.


%%------------------------------------------------------------------------------
%% goal_table_add( + goal table, + goal ):
%% Add this goal to the table.

goal_table_add( Table, Goal ) :-
        olist_add( Table, Goal ).

%%------------------------------------------------------------------------------
