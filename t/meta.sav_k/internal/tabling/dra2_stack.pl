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

%%%  The "stack" data type for the "dra" interpreter.                        %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (March 2009)           .              %%%
%%%                                                                          %%%
%%%  Last update: 27 March 2009.                                             %%%
%%%                                                                          %%%

%%% The "stack" is the chain of tabled ancestors used by solve/4.  It is
%%% factored out as an abstract data type to facilitate changing to a more
%%% efficient representation.
%%%
%%% The requirements are as follows:
%%%
%%%       (a) It must be possible to check whether a tabled goal G and one of
%%%           its ancestors are variants. There can be at most one such
%%%           ancestor, call it A.
%%%
%%%       (b) We must be able to identify the "current clause" that was used by
%%%           A and that led to the creation of G.
%%%
%%%       (c) We must be able to identify all the tabled goals that are
%%%           descendants of A and ancestors of G (i.e., all tabled goals
%%%           "between" G and A).
%%%
%%%       NOTE: Before checking for variance the goals must be passed
%%%             through essence_hook/2.
%%%
%%%
%%% Information about an ancestor goal is kept in the form of a triple:
%%%    triple( goal, index, clause )
%%% where
%%%    goal    is the (current instantiation of the) goal;
%%%    index   is the unique index of the goal;
%%%    clause  is the clause that is currently used by the goal (it has been
%%%               instantiated by matching with the goal in its original form,
%%%               but does not share variables with the goal).
%%%
%%%
%%% The operations are:
%%%
%%%    empty_stack( - stack ):
%%%            Create an empty stack.
%%%
%%%    push_tabled( + goal, + index, + clause, + stack, - new stack ):
%%%            where the first three arguments are the constitutive elements of
%%%            a triple.
%%%            Push the triple goal onto the stack.
%%%
%%%    is_variant_of_ancestor( + goal,
%%%                            + stack,
%%%                            - the triple with the variant ancestor,
%%%                            - goals between goal and the variant ancestor
%%%                          )
%%%         Succeed if the tabled goal is a variant of some goal in the stack.
%%%         If successful, return the first such member and the list of
%%%         intervening triples.


% %%--------------  The minimal implementation:  --------------%%
% %%
% %% The stack is just a list of triples.
%
% :- mode empty_stack( - ).
%
% empty_stack( [] ).
%
%
% :- mode push_tabled( +, +, +, +, - ).
%
% push_tabled( Goal, Index, Clause, Stack,
%              [ triple( Goal, Index, Clause ) | Stack ]
%            ).
%
%
% :- mode is_variant_of_ancestor( +, +, -, - ).
%
% is_variant_of_ancestor( Goal, Stack, AncestorTriple, Prefix ) :-
%         append( Prefix, [ AncestorTriple | _ ], Stack ),      % split the list
%         AncestorTriple = triple( G, _, _ ),
%         are_essences_variants( Goal, G ),
%         !.


%%--------------  An implementation that uses goal_table:  --------------%%
%%
%% The goal table is used to speed up the check whether there is a variant
%% ancestor.  We still need a standard stack for getting the intermediate tabled
%% goals.  So the "stack" is represented by
%%    tstack( stack, goal table )


:- ensure_loaded( '../../general/goal_table_in_tree' ).


:- mode empty_stack( - ).

empty_stack( tstack( [], Table ) ) :-
        empty_goal_table( Table ).


:- mode push_tabled( +, +, +, +, - ).

push_tabled( StackedGoal, Index, Clause, tstack( Stack, Table ),
             tstack( [ triple( StackedGoal, Index, Clause ) | Stack ], Table )
           ) :-
        StackedGoal = goal( _, _, Goal ),
        goal_table_add( Table, Goal ).


:- mode is_variant_of_ancestor( +, +, -, - ).

is_variant_of_ancestor( Goal,
                        tstack( Stack, Table ),
                        AncestorTriple,
                        Prefix
                      ) :-
        is_a_variant_in_goal_table( Goal, Table ),           % preliminary check
        append( Prefix, [ AncestorTriple | _ ], Stack ),     % split the list
        AncestorTriple = triple( goal( _, _, G ), _, _ ),
        are_essences_variants( Goal, G ),
        !.

%-------------------------------------------------------------------------------
