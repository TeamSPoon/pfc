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

%%%  The "set of coinductive hypotheses" for the "dra" interpreter.          %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (March 2009)           .              %%%
%%%                                                                          %%%
%%%  Last update: 12 June 2009.                                              %%%
%%%                                                                          %%%

%%% The "set of coinductive hypotheses" contains those ancestors of the current
%%% goal that invoke coinductive predicates. It is used by solve/4, and factored
%%% out as an abstract data type to facilitate changing to a more efficient
%%% representation.
%%%
%%% The requirements are as follows:
%%%
%%%       (a) We must be able to check whether a coinductive goal G can be
%%%           unified with one of its ancestors.
%%%
%%%       (b) Ancestors that might be unifiable with G must be available in
%%%           reverse chronological order (i.e., the nearest ancestor first).
%%%
%%%       NOTE: Before checking for unifiability the goals must be passed
%%%             through essence_hook/2.
%%%
%%%
%%% The operations are:
%%%
%%%    empty_hypotheses( - stack of hypotheses ):
%%%         Create an empty stack for coinductive hypotheses.
%%%
%%%    push_coinductive( + goal, + stack of hypotheses , - new stack ):
%%%         Push the coinductive goal onto the stack.
%%%
%%%    unify_with_coinductive_ancestor( + goal, + stack of hypotheses ):
%%%         Fail if there is no unifiable coinductive ancestor on the stack. If
%%%         there is one, succeed after performing the unification with the
%%%         most recent such ancestor.  Upon failure undo the unification and
%%%         unify with the next such ancestor, and so on (in reverse
%%%         chronological order), failing after all unifiable ancestors are
%%%         exhausted.


% %%--------------  The minimal implementation:  --------------%%
% %%
% %% The set of coinductive hypotheses is just a list.
%
% % :- mode empty_hypotheses( - ).
%
% empty_hypotheses( [] ).
%
%
% % :- mode push_coinductive( +, +, - ).
%
% push_coinductive( Goal, Hyp, [ Goal | Hyp ] ).
%
%
% % :- mode unify_with_coinductive_ancestor( +, + ).
%
% unify_with_coinductive_ancestor( Goal, Hyp ) :-
%         once( essence_hook( Goal, Essence ) ),
%         member( G, Hyp ),
%         once( essence_hook( G, Essence ) ).


%%--------------  An implementation that uses goal_table:  --------------%%

:- ensure_loaded( '../general/goal_table_in_tree' ).


% :- mode empty_hypotheses( - ).

empty_hypotheses( Hyp ) :-
        empty_goal_table( Hyp ).


% :- mode push_coinductive( +, +, - ).

push_coinductive( Goal, Hyp, NewHyp ) :-
        goal_table_add( Hyp, Goal, NewHyp ).


% :- mode unify_with_coinductive_ancestor( +, + ).

unify_with_coinductive_ancestor( Goal, Hyp ) :-
        goal_table_member( Goal, Hyp ).

%-------------------------------------------------------------------------------
