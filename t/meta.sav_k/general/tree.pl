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

%%%  Operations on binary trees.                                             %%%
%%%                                                                          %%%
%%%  This particular version                                                 %%%
%%%   written by Feliks Kluzniak at UTD (May 2009).                          %%%
%%%                                                                          %%%
%%%  Last update: 16 May 2009.                                               %%%
%%%                                                                          %%%

:- ensure_loaded( higher_order ).


%%%
%%%  The format of a node is:
%%%       t( key, information, left subtree, right subtree )
%%%  or
%%%       empty.


%%------------------------------------------------------------------------------
%% empty_otree( +- tree ):
%% Create an empty tree, or check that the provided tree is empty.

empty_tree( empty ).


%%------------------------------------------------------------------------------
%% is_in_tree( + tree, + key, + comparison predicate, - information ):
%% If the entry for this key is present in the tree, succeed and return the
%% associated information; if it is not, fail.
%% "comparison predicate" is a binary predicate that succeeds if the first
%% argument is smaller than the second argument.  Any predicate that implements
%% a total ordering will do.

is_in_tree( Node, Key, LessPred, Info ) :-
        Node = t( K, I, L, R ),
        (
            Key = K
        ->
            Info = I
        ;
            apply( LessPred, [ Key, K ] )
        ->
            is_in_tree( L, Key, LessPred, Info )
        ;
            is_in_tree( R, Key, LessPred, Info )
        ).


%%------------------------------------------------------------------------------
%% tree_add( + tree,
%%           + key,
%%           + information,
%%           + comparison predicate,
%%           + modification predicate,
%%           - new tree
%%         ):
%% Make sure that the key is associated with this information in the tree.
%% If the entry for this key is already present, modify the existing
%% information.
%% "less predicate" is the name of a binary predicate that succeeds if the first
%% argument is smaller than the second argument.
%% "modification predicate" is a predicate of three arguments that will add
%% information from its second argument to its first argument, thus obtaining
%% the third argument.

tree_add( Node, Key, Info, LessPred, ModifyPred, NewNode ) :-
        (
            empty_tree( Node )
        ->
            NewNode = t( Key, Info, L, R ),
            empty_tree( L ),
            empty_tree( R )
        ;
            Node = t( K, I, L, R ),
            (
                Key = K
            ->
                apply( ModifyPred, [ I, Info, NewI ] ),
                NewNode = t( K, NewI, L, R )
            ;
                apply( LessPred, [ Key, K ] )
            ->
                NewNode = t( Key, I, NewL, R ),
                tree_add( L, Key, Info, LessPred, ModifyPred, NewL )
            ;
                NewNode = t( Key, I, L, NewR ),
                tree_add( R, Key, Info, LessPred, ModifyPred, NewR )
            )
        ).

%%------------------------------------------------------------------------------
