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

%%%  Operations on d-lists ("difference lists").                             %%%
%%%                                                                          %%%
%%%  A d-list is one whose final element is a variable, and the variable is  %%%
%%%  immediately accessible. One can add new elements at the end without     %%%
%%%  copying the list, in constant time: the downside is that it is          %%%
%%%  a destructive operation, i.e., the old list "disappears".               %%%
%%%  A d-list can be more efficient than an open list, because of constant-  %%%
%%%  time access to the end.  It can also be less convenient to use,         %%%
%%%  because needs a new "handle" on the modified list.                      %%%
%%%                                                                          %%%
%%%  This particular version                                                 %%%
%%%   written by Feliks Kluzniak at UTD (February 2009).                     %%%
%%%                                                                          %%%
%%%  Last update: 18 February 2009.                                          %%%
%%%                                                                          %%%


%%------------------------------------------------------------------------------
%% empty_dlist( +- d-list ):
%% Create an empty d-list, or check that the provided d-list is empty.

empty_dlist( End - End ) :-  var( End ).


%%------------------------------------------------------------------------------
%% dlist_member( +- item, + d-list ):
%% Generate a member of the d-list, or check that a given term is a member.

dlist_member( M, L - End ) :-
        L \== End,
        L = [ H | T ],
        (
            M = H
        ;
            dlist_member( M, T - End )
        ).


%%------------------------------------------------------------------------------
%% dlist_add( + item, + d-list, - new d-list ):
%% Add this item at the end of the d-list:

dlist_add( Item, L - [ Item | NewEnd ], L - NewEnd ).


%%------------------------------------------------------------------------------
%% dlist_conc( + d-list, + d-list, - d-list ):
%% Concatenate two dlists

dlist_conc( L1 - L2, L2 - End2, L1 - End2 ).



%%------------------------------------------------------------------------------
%% dlist_split( + d-list, - d-list, - d-list ):
%% Splits a list into two parts that, when concatenated, would yield the
%% original list.

dlist_split( DL, DL1, DL2 ) :-
        empty_dlist( DL  ),
        empty_dlist( DL1 ),
        empty_dlist( DL2 ).

dlist_split( DL, DL1, DL2 ) :-
        \+ empty_dlist( DL ),
        (
            empty_dlist( DL1 ),
            DL2 = DL
        ;
            DL  = [ H | T  ] - End ,
            DL1 = [ H | T1 ] - End1,
            dlist_split( T - End, T1 - End1, DL2 )
        ).

%%------------------------------------------------------------------------------
