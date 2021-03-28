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

%%%  Simple, but useful operations on sets.                                  %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (February 2009).                      %%%
%%%                                                                          %%%
%%%  Last update: 30 March 2009.                                             %%%
%%%                                                                          %%%
%%%  NOTE: Different Prolog variables are treated as different items: this   %%%
%%%        is so by design!                                                  %%%
%%%                                                                          %%%
%%%        This implementation should only be used for smallish sets.        %%%
%%%        The cost of insertion or membership check is proportional to      %%%
%%%        the size of the set, the cost of set operations (union, equality  %%%
%%%        etc.) is quadratic in the size of the sets.                       %%%
%%%                                                                          %%%

%%% Sets are represented as unordered lists.


%%------------------------------------------------------------------------------
%% empty_set( +- set ) :
%% Create an empty set, or check that the given set is empty.

empty_set( set( [] ) ).


%%------------------------------------------------------------------------------
%% same_set_element( + item, + item ):
%% Succeeds iff the two items are identical
%% when treated as elements of a set.

same_set_element( A, B ) :-
        (
            ( var( A ) ; A \= set( _ )
            ; var( B ) ; B \= set( _ )
            )
        ->
            A == B
        ;
            equal_sets( A, B )
        ).


%%------------------------------------------------------------------------------
%% is_in_set( + item, + set ):
%% Is the item a member of the set?

is_in_set( Item, set( List ) ) :-
        once( is_in_set_( Item, List ) ).

%
is_in_set_( Item, [ H | _ ] ) :-
        same_set_element( Item, H ).

is_in_set_( Item, [ _H | T ] ) :-
        % \+ same_element( Item, _H ),
        is_in_set_( Item, T ).


%%------------------------------------------------------------------------------
%% from_set( + set, - member, - new set ):
%% Remove an arbitrary member from the set;
%% fail if the set is empty.

from_set( set( [ H | T ] ),  H, set( T ) ).


%%------------------------------------------------------------------------------
%% remove_from_set( + item, + set, - new set ):
%% Remove the given item from the set;
%% fail if the item is not a member.

remove_from_set( M, set( L ), set( NL ) ) :-
        once( remove_from_set_( M, L, NL ) ).

%
remove_from_set_( M, [ H | T ], T ) :-
        same_set_element( M, H ).

remove_from_set_( M, [ H | T ], [ H | NT ] ) :-
        % \+ same_set_element( M, H ).
        remove_from_set_( M, T, NT ).


%%------------------------------------------------------------------------------
%% add_to_set( + item, + set, - new set ):
%% Add the item to the set.
%%
%% WARNING: DO NOT INSTANTIATE THE ITEM WHILE IT IS IN SOME SET!

add_to_set( Item, Set, NewSet ) :-
        once( add_to_set_( Item, Set, NewSet ) ).

%
add_to_set_( Item, Set, Set ) :-
        is_in_set( Item, Set ).

add_to_set_( Item, set( L ), set( [ Item | L ] ) ).
        % \+ is_in_set( Item, set( L ) ).


%%------------------------------------------------------------------------------
%% sub_set( + set, + set ):
%% Succeed iff the first set is a subset of the second set.
%%
%% NOTE: In Eclipse the name "subset" is reserved for a built-in.

sub_set( set( L1 ), Set2 ) :-
        once( subset_( L1, Set2 ) ).

%
subset_( [], _ ).

subset_( [ H | T ], Set ) :-
        is_in_set( H, Set ),
        subset_( T, Set ).


%%------------------------------------------------------------------------------
%% equal_sets( + set, + set ):
%% Are the two sets equal?

equal_sets( A, B ) :-
        sub_set( A, B ),
        sub_set( B, A ).


%%------------------------------------------------------------------------------
%% set_union( + set, + set, - the union ):
%% Compute the union of two sets.

set_union( set( L1 ), S2, set( Union ) ) :-
        once( set_union_( L1, S2, Union ) ).

%
set_union_( [], set( L ), L ).

set_union_( [ H | T ], S, NS ) :-
        is_in_set( H, S ),
        set_union_( T, S, NS ).

set_union_( [ H | T ], S, [ H | NS ] ) :-
        % \+ is_in_set( H, S ),
        set_union_( T, S, NS ).


%%------------------------------------------------------------------------------
%% set_intersection( + set, + set, - the intersection ):
%% Compute the intersection of two sets.

set_intersection( set( L1 ), S2, set( Intersection ) ) :-
        once( set_intersection_( L1, S2, Intersection ) ).

%
set_intersection_( [], _, [] ).

set_intersection_( [ H | T ], S, NS ) :-
        \+ is_in_set( H, S ),
        set_intersection_( T, S, NS ).

set_intersection_( [ H | T ], S, [ H | NS ] ) :-
        % is_in_set( H, S ),
        set_intersection_( T, S, NS ).


%%------------------------------------------------------------------------------
%% set_difference( + set, + set, - the difference ):
%% Subtract the second set from the first.

set_difference( set( L1 ), S2, set( Difference ) ) :-
        once( set_difference_( L1, S2, Difference ) ).

%
set_difference_( [], _, [] ).

set_difference_( [ H | T ], S, NS ) :-
        is_in_set( H, S ),
        set_difference_( T, S, NS ).

set_difference_( [ H | T ], S, [ H | NS ] ) :-
        % \+ is_in_set( H, S ),
        set_difference_( T, S, NS ).


%%------------------------------------------------------------------------------
%% symmetric_set_difference( + set, + set,
%%                           - the symmetric difference
%%                         ):
%% Compute the symmetric difference of two sets.

symmetric_set_difference( A, B, SymmetricDiff ) :-
        set_difference( A, B, DiffAB ),
        set_difference( B, A, DiffBA ),
        set_union( DiffAB, DiffBA, SymmetricDiff ).


%%------------------------------------------------------------------------------
%% set_from_list( + list, - set ):
%% Form a set with all the elements of the list.
%%
%% WARNING: DO NOT INSTANTIATE THE ITEM WHILE IT IS IN SOME SET!

set_from_list( List, Set ) :-
        empty_set( Empty ),
        set_from_list_( List, Empty, Set ).

%
set_from_list_( []       , Set, Set  ).

set_from_list_( [ H | T ], Set, NSet ) :-
        add_to_set( H, Set, Set2 ),
        set_from_list_( T, Set2, NSet ).

%%------------------------------------------------------------------------------
