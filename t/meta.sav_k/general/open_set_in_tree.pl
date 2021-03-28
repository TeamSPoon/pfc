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

%%%  Simple, but useful operations on sets.  The sets are open, i.e.,        %%%
%%%  insertion is a destructive operation.                                   %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (February 2009).                      %%%
%%%                                                                          %%%
%%%  Last update: 20 February 2009.                                          %%%
%%%                                                                          %%%
%%%  NOTE: Terms that are variants are treated as the same item: this is     %%%
%%%        so because comparison of variables is unreliable.                 %%%
%%%                                                                          %%%
%%%        The cost of insertion or membership check can be logarithmic      %%%
%%%        in the size of the set, but can be proportional to the size if    %%%
%%%        the ordering in which elements are inserted is far from random.   %%%
%%%        The cost of set operations (union, equality etc.) can also be     %%%
%%%        logarithmic, but quadratic in the worst case.                     %%%
%%%                                                                          %%%


%%% Sets are represented as open binary trees.


%%------------------------------------------------------------------------------
%% empty_oset( +- open set ) :
%% Create an empty set, or check that the given set is empty.

empty_oset( V ) :-
        var( V ).


%%------------------------------------------------------------------------------
%% add_to_oset( + item, +- open set ):
%% Add the item to the set.

add_to_oset( Item, Set ) :-
        (
            var( Set )
        ->
            Set = t( Item, _, _ )
        ;
            % nonvar( Set ),
            Set = t( I, L, R ),
            (
                Item = I
            ->
                true
            ;
                Item @< I
            ->
                add_to_oset( Item, L )
            ;
                add_to_oset( Item, R )
            )
        ).


%%------------------------------------------------------------------------------
%% is_in_oset( + item, + open set ):
%% Is the given item a member of the set?

is_in_oset( Item, Set ) :-
        (
            var( Set )
        ->
            fail
        ;
            % nonvar( Set ),
            Set = t( I, L, R ),
            (
                Item = I
            ->
                true
            ;
                Item @< I
            ->
                is_in_oset( Item, L )
            ;
                is_in_oset( Item, R )
            )
        ).


%%------------------------------------------------------------------------------
%% generate_member_of_oset( + open set, - item ):
%% Nondeterministically generate members of the set.

generate_member_of_oset( Set, Item ) :-
        nonvar( Set ),
        Set = t( I, L, R ),
        (
            generate_member_of_oset( L, Item )
        ;
            Item = I
        ;
            generate_member_of_oset( R, Item )
        ).


%%------------------------------------------------------------------------------
%% equal_osets( + open set, + open set ):
%% Are the two sets equal?

equal_osets( S1, S2 ) :-
        symmetric_oset_difference( S1, S2, SD ),
        empty_oset( SD ).


%%------------------------------------------------------------------------------
%% oset_union( + open set, + open set, - open set ):
%% Compute the union of two sets.

oset_union( S1, S2, Result ) :-
        copy_items( S1, Result ),
        copy_items( S2, Result ).

%
copy_items( V, _ ) :-
        var( V ),
        !.

copy_items( t( I, L, R ), Result ) :-
        add_to_oset( I, Result ),
        copy_items( L, Result ),
        copy_items( R, Result ).


%%------------------------------------------------------------------------------
%% oset_intersection( + open set, + open set, - open set ):
%% Compute the intersection of two sets.

oset_intersection( S1, S2, Result ) :-
        copy_shared( S1, S2, Result ).

%
copy_shared( V, _, _ ) :-
        var( V ),
        !.

copy_shared( t( I, L, R ), S, Result ) :-
        (
            is_in_oset( I, S )
        ->
            add_to_oset( I, Result )
        ;
            true
        ),
        copy_shared( L, S, Result ),
        copy_shared( R, S, Result ).


%%------------------------------------------------------------------------------
%% oset_difference( + open set, + open set, - open set ):
%% Subtract the second set from the first.

oset_difference( S1, S2, Result ) :-
        copy_not_shared( S1, S2, Result ).

%
copy_not_shared( V, _, _ ) :-
        var( V ),
        !.

copy_not_shared( t( I, L, R ), S, Result ) :-
        (
            is_in_oset( I, S )
        ->
            true
        ;
            add_to_oset( I, Result )
        ),
        copy_not_shared( L, S, Result ),
        copy_not_shared( R, S, Result ).


%%------------------------------------------------------------------------------
%% symmetric_oset_difference( + open set, + open set, - open set ):
%% Compute the symmetric difference of two sets.

symmetric_oset_difference( S1, S2, Result ) :-
        oset_difference( S1, S2, Result ),
        oset_difference( S2, S1, Result ).


%%------------------------------------------------------------------------------
%% oset_to_list( + open set, - list ):
%% Create a list that contains all the elements of the set.

oset_to_list( Set, List ) :-
        to_list( Set, [], List ).

%
to_list( V, ListSoFar, ListSoFar ) :-
        var( V ),
        !.

to_list( t( I, L, R ), ListSoFar, List ) :-
        to_list( R, ListSoFar, ListWithRight ),
        to_list( L, [ I | ListWithRight ], List ).


%%------------------------------------------------------------------------------
%% list_to_oset( + list, - set ):
%% Create a set that contains all the elements from the list (without
%% duplicates, of course).

list_to_oset( List, Set ) :-
        empty_oset( Set ),
        list_to_oset_( List, Set ).

%
list_to_oset_( [], _ ).

list_to_oset_( [ H | T ], S ) :-
        add_to_oset( H, S ),
        list_to_oset_( T, S ).

%%------------------------------------------------------------------------------
