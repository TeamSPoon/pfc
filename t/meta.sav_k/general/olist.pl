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

%%%  Operations on "open" lists.                                             %%%
%%%                                                                          %%%
%%%  An open list is one whose final element is a variable. One can add      %%%
%%%  new elements at the end without copying the list: the downside is that  %%%
%%%  it is a destructive operation, i.e., the old list is modified.          %%%
%%%                                                                          %%%
%%%  This particular version                                                 %%%
%%%   written by Feliks Kluzniak at UTD (February 2009).                     %%%
%%%                                                                          %%%
%%%  Last update: 18 February 2009.                                          %%%
%%%                                                                          %%%


%%------------------------------------------------------------------------------
%% empty_olist( +- open list ):
%% Create an empty open list, or check that the provided open list is empty.

empty_olist( OL ) :-  var( OL ).


%%------------------------------------------------------------------------------
%% olist_member( +- item, + open list ):
%% Generate a member of the open list, or check that a given term is a member.

olist_member( M, OL ) :-
        nonvar( OL ),
        OL = [ H | T ],
        (
            M = H
        ;
            olist_member( M, T )
        ).


%%------------------------------------------------------------------------------
%% olist_member_reversed( +- item, + open list ):
%% Generate a member of the open list, or check that a given term is a member:
%% in the case of generation, proceed from the end of the list forwards.

olist_member_reversed( M, OL ) :-
        nonvar( OL ),
        OL = [ H | T ],
        (
            olist_member_reversed( M, T )
        ;
            M = H
        ).


%%------------------------------------------------------------------------------
%% olist_add( + open list, + item ):
%% Add this item at the end of the open list.

olist_add( OL, Item ) :-
        olist_end( OL, End ),
        End = [ Item | _ ].

%
% Get the end of an open list.

olist_end( End, End ) :-
        var( End ),
        !.

olist_end( [ _ | T ], End ) :-
        olist_end( T, End ).


%%------------------------------------------------------------------------------
%% olist_conc( + open list, + open list ):
%% The first open list becomes the concatenation of the two.

olist_conc( OL1, OL2 ) :-
        olist_end( OL1, End ),
        olist_conc_( End, OL2 ).

%
olist_conc_( End, End ) :-
        var( End ),
        !.

olist_conc_( End, [ H | T ] ) :-
        End = [ H | NewEnd ],
        olist_conc( NewEnd, T ).



%%------------------------------------------------------------------------------
%% olist_split( + open list, - open list, - open list ):
%% Splits a list into two parts that, when concatenated, would yield the
%% original list.

olist_split( OL1, OL2, OL3 ) :-
        empty_olist( OL1 ),
        empty_olist( OL2 ),
        empty_olist( OL3 ).

olist_split( OL, OL1, OL2 ) :-
        \+ empty_olist( OL ),
        (
            empty_olist( OL1 ),
            OL2 = OL
        ;
            OL  = [ H | T  ],
            OL1 = [ H | T1 ],
            olist_split( T, T1, OL2 )
        ).

%%------------------------------------------------------------------------------
