

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


%%%                                                                          %%%
%%%  A vanilla interpreter for Prolog, with no cuts.                         %%%
%%%  Written by Feliks Kluzniak at UTD (April 2009).                         %%%
%%%                                                                          %%%
%%%  Last update: 30 April 2009.                                             %%%
%%%                                                                          %%%

%%% This is a trivial interpreter that can run itself.
%%% Try loading it together with ex.pl and then invoking
%%%     solve( solve( solve( solve( solve( p(X), S ), T ), U ), V ), W ).


:- dynamic solve/2, solve_nv/2, builtin/1.

%% solve( + goals, - state ):
%% Solve the goals, give up whenever state is set to 'error'.
%% (State should initially be an uninstantiated variable.)

solve( G, State ) :-
        State \== error,
        var( G ),
        write( 'A variable goal' ),  nl,
        State = error,
        fail.

solve( G, State ) :-
        State \== error,
        nonvar( G ),
        solve_nv( G, State ).


%% solve_nv( + goal, - state ):
%% Like solve/2, but now we know the first argument is not a variable.

solve_nv( (Cond -> Then ; Else), State ) :-
        State \== error,
        (
            solve( Cond, State )
        ->
            solve( Then, State )
        ;
            solve( Else, State )
        ).

solve_nv( (A ; B), State ) :-
        State \== error,
        A \= _ -> _,
        (
            solve( A, State )
        ;
            solve( B, State )
        ).

solve_nv( (A , B), State ) :-
        State \== error,
        solve( A, State ),
        solve( B, State ).

solve_nv( (Cond -> Then), State ) :-
        State \== error,
        solve( Cond, State ),
        solve( Then, State ).

solve_nv( Call, State ) :-
        State \== error,
        Call \= (_ ; _),
        Call \= (_ , _),
        Call \= (_ -> _),
        (
            builtin( Call )
        ->
            call( Call )
        ;
            clause( Call, Body ),
            solve( Body, State )
        ).

%
builtin( fail           ).
builtin( false          ).
builtin( true           ).
builtin( write( _ )     ).
builtin( nl             ).
builtin( var( _ )       ).
builtin( nonvar( _ )    ).
builtin( _  = _         ).
builtin( _ \= _         ).
builtin( _  == _        ).
builtin( _ \== _        ).
builtin( clause( _, _ ) ).
builtin( call( _ )      ).

%-------------------------------------------------------------------------------
