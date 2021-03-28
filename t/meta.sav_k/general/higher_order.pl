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

%%%  Some "higher order" predicates for Prolog.                              %%%
%%%  This particular version was                                             %%%
%%%  written by Feliks Kluzniak at UTD (February 2009).                      %%%
%%%                                                                          %%%
%%%  Last update: 11 June 2009.                                              %%%
%%%                                                                          %%%

%%% NOTE: Throughout the file "predicate name" will be used either for
%%        the name of a predicate, or for a predicate with an incomplete
%%        list of arguments (a partially applied predicate): see apply/2.


%%------------------------------------------------------------------------------
%% apply( + predicate name (possibly with arguments), + list of arguments ):
%% Extend the list of arguments of the first argument with the second argument
%% and invoke the result.
%% For example, if we have
%%     sum( A, B, C ) :-  C is A + B.
%% then
%%     map( sum(5 ), [ 1, 2, 3 ], Result )
%% will bind Result to [ 6, 7, 8 ].

apply( PredNameArgs, Arguments ) :-
        PredNameArgs =.. [ PredName | Args ],
        append( Args, Arguments, AllArgs ),
        Literal =.. [ PredName | AllArgs ],
        call( Literal ).


%%------------------------------------------------------------------------------
%% map( + predicate name, + list, - mapped list ):
%% The predicate should implement a unary function, i.e.,
%%   - it should take two arguments, the first of which is an input argument,
%%     and the second of which is an output argument;
%%   - it should always succeed, and the first result should be "what we want".
%% The predicate is applied to input arguments from the list, and the
%% corresponding outputs are returned in the second list.
%%
%% Example:
%%          square( M, N ) :-  N is M * M.
%%
%%          ?- map( square, [ 1, 2, 3 ], Ans ).
%%
%%          Ans = [ 1, 4, 9 ].

map( _, [], [] ).

map( PredName, [ H | T ], [ NH | NT ] ) :-
        apply( PredName, [ H, NH ] ),
        map( PredName, T, NT ).


%%------------------------------------------------------------------------------
%% filter( + predicate name, + list, - filtered list ):
%% The predicate should take one argument.
%% The output list will contain only those elements of the input list for which
%% the predicate succeeds.

filter( _, [], [] ).

filter( PredName, [ H | T ], NL ) :-
        (
            apply( PredName, [ H ] )
        ->
            NL = [ H | NT ]
        ;
            NL = NT
        ),
        filter( PredName, T, NT ).


%%------------------------------------------------------------------------------
%% filter2( + predicate name, + list, - yes list, - no list ):
%% The predicate should take one argument.
%% The first output list will contain only those elements of the input list for
%% which the predicate succeeds; the second output list will contain only those
%% elements of the input list for which the predicate fails.

filter2( _, [], [], [] ) :-  !.

filter2( PredName, [ H | T ], [ H | Yes ], No ) :-
        apply( PredName, [ H ] ),
        !,
        filter2( PredName, T, Yes, No ).

filter2( PredName, [ H | T ], Yes, [ H | No ] ) :-
        % \+ apply( PredName, [ H ] ),
        filter2( PredName, T, Yes, No ).


%%------------------------------------------------------------------------------
%% fold( + predicate name,+ initial value, + list, - final value ):
%% The predicate should implement a binary function, i.e.,
%%   - it should take three arguments, the first two of which are input
%%     arguments, and the third of which is an output argument;
%%   - it should always succeed, and the first result should be "what we want".
%% If the list is empty, the initial value is returned; otherwise the predicate
%% is applied to the initial value and the first member of the list, and then
%% to the result and the third member, and so on.
%% For example, if "sum( A, B, C )" unifies "C" with the sum of "A" and "B",
%% then "fold( sum, 0, [1,2,3], S )" unifies "S" with "6".

fold( _, Initial, [], Initial ).

fold( PredName, Initial, [ H | T ], Result ) :-
        apply( PredName, [ Initial, H, R ] ),
        fold( PredName, R, T, Result ).

%%------------------------------------------------------------------------------
