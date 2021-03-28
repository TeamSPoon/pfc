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

%%%  Some generally-useful utilities.                                        %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (January 2009).                       %%%
%%%                                                                          %%%
%%%  Last update: 28 August 2009.                                            %%%
%%%                                                                          %%%


:- ensure_loaded( set_in_list ).
:- ensure_loaded( higher_order ).
:- ensure_loaded( vardict_utilities ).
:- ensure_loaded( clause_verification ).
:- ensure_loaded( io_utilities ).
:- ensure_loaded( errors_and_warnings ).



%%------------------------------------------------------------------------------
%% check( + goal ) :
%%    Succeeds iff goal succeeds, but without instantiating any variables
%%    (side-effects may appear, though).

% :- mode check( + ).

check( Goal ) :-  \+ \+ call( Goal ) .



%%------------------------------------------------------------------------------
%% mk_ground( +- term ) :
%%    Instantiates all the unbound variables in the term as terms of
%%    the form ' V'( 0 ), ' V'( 0 ). ' V'( 0 ) etc.
%%    (Note: This is mainly for "safety". If the strange names of the functors
%%           are not needed, consider using:
%%              mk_ground( T ) :- numbervars( T, 0, _ ).
%%           on Prolog systems that support numbervars/3.
%%    )
%%
%% NOTE: The following implementation is no good for cyclic terms.

% :- mode mk_ground( ? ).

mk_ground( T ) :-  mk_ground_aux( T, 0, _ ).

%
% :- mode mk_ground_aux( ?, +, - ).

mk_ground_aux( V, N, N1 ) :-
        var( V ),
        !,
        V = ' V'( N ),
        N1 is N + 1.

mk_ground_aux( T, N, N ) :-
        atomic( T ),
        !.

mk_ground_aux( T, N, N1 ) :-
        % \+ var( T ), \+ atomic( T ),
        T =.. [ _Functor | Args ],
        mk_ground_auxs( Args, N, N1 ).

%
% :- mode mk_ground_auxs( +, +, - ).

mk_ground_auxs( []        , N, N  ).
mk_ground_auxs( [ T | Ts ], N, N2 ) :-
        mk_ground_aux( T, N, N1 ),
        mk_ground_auxs( Ts, N1, N2 ).


%%------------------------------------------------------------------------------
%% is_ground_var( + term ):
%% Is this term a variable that was ground by mk_ground/1?

is_ground_var( Var ) :-
        var( Var ),
        !,
        fail.

is_ground_var( ' V'( N ) ) :-
        integer( N ).


%%------------------------------------------------------------------------------
%% ground_term_variables( + term, - set of variables ):
%% Given a term grounded by mk_ground/1, produce the set of the grounded form of
%% variables occurring in the term.
%% (Note that the term may be a subset of a larger term grounded by mk_ground/1,
%%  so the variable numbers need not be contiguous.)

% :- mode ground_term_variables( +, - ).

ground_term_variables( T, S ) :-
        empty_set( S0 ),
        gtv_( T, S0, S ),
        !.

ground_term_variables( T, _ ) :-
        error( [ 'Bad call to ground_term_variables (term not ground): ', T ] ).

%
% :- mode gtv_( +, +, - ).

gtv_( V, _, _ ) :-
        var( V ),
        !,
        fail.

gtv_( T, S, NS ) :-
        is_ground_var( T ),
        !,
        add_to_set( T, S, NS ).

gtv_( T, S, S ) :-
        atom( T ),
        !.

gtv_( [ H | T ], S, NS ) :-
        !,
        gtv_( H,  S, S2 ),
        gtv_( T, S2, NS ).

gtv_( T, S, NS ) :-
        T =.. [ _ | Args ],
        gtv_( Args, S, NS ).


%%------------------------------------------------------------------------------
%% is_an_instance( + term, + term ) :
%%    Succeeds iff arg1 is an instance of arg2, but does not instantiate any
%%    variables.
%% NOTE: In Eclipse this loops on cyclic terms.

is_an_instance( T1, T2 ) :-
        check( T1 = T2 ),                     % quickly weed out obvious misfits
        copy_term( T2, CT2 ), subsumes_chk( CT2, T1 ).



%%------------------------------------------------------------------------------
%% mk_pattern( + an atom representing the name of a predicate,
%%             + an integer representing the arity of the predicate,
%%             - the most general pattern that matches all invocations of the
%%               predicate
%%           )
%% Given p/k, produce p( _, _, ... _ )  (of arity k)

% :- mode mk_pattern( +, +, - ).

% mk_pattern( P, K, Pattern ) :-
%        length( Args, K ),                           % Args = K fresh variables
%        Pattern =.. [ P | Args ].

mk_pattern( P, K, Pattern ) :-
        functor( Pattern, P, K ).



%%------------------------------------------------------------------------------
%% most_general_instance( + a term,
%%                        - a most general instance with the same main functor
%%                      ):
%% E.g., p( a, q( X, Y ) )  is transformed to  p( _, _ ).

% :- mode most_general_instance( +, - ).

most_general_instance( Term, Pattern ) :-
        functor( Term, Name, Arity ),
        functor( Pattern, Name, Arity ).



%%------------------------------------------------------------------------------
%% predspecs_to_patterns( + a conjunction of predicate specifications,
%%                        - list of most general instances of these predicates
%%                      ):
%% Given one or several predicate specifications (in the form "p/k" or
%% "p/k, q/l, ...") check whether they are well-formed: if not, raise a fatal
%% error; otherwise return a list of the most general instances that correspond
%% to the predicate specifications.

predspecs_to_patterns( Var, _ ) :-
        var( Var ),
        !,
        error( [ 'A variable instead of predicate specifications: \"',
                 Var,
                 '\"'
               ]
             ).

predspecs_to_patterns( (PredSpec , PredSpecs), [ Pattern | Patterns ] ) :-
        !,
        predspec_to_pattern( PredSpec, Pattern ),
        predspecs_to_patterns( PredSpecs, Patterns ).

predspecs_to_patterns( PredSpec, [ Pattern ] ) :-
        predspec_to_pattern( PredSpec, Pattern ).


%%------------------------------------------------------------------------------
%% predspec_to_pattern( + a predicate specification,
%%                      - a most general instance of this predicate
%%                    ):
%% Given a predicate specification (in the form "p/k") check whether it is
%% well-formed: if not, raise a fatal error; otherwise return a most general
%% instance that correspond to the predicate specification.

predspec_to_pattern( PredSpec, Pattern ) :-
        check_predspec( PredSpec ),
        PredSpec = P / K,
        mk_pattern( P, K, Pattern ).


%%------------------------------------------------------------------------------
%% check_predspec:
%% Raise an error if this is not a good predicate specification.
check_predspec( Var ) :-
        var( Var ),
        !,
        error( [ 'A variable instead of a predicate specification: \"',
                 Var,
                 '\"'
               ]
             ).

check_predspec( P / K ) :-
        atom( P ),
        integer( K ),
        K >= 0,
        !.

check_predspec( PredSpec ) :-
        error( [ 'An incorrect predicate specification: \"', PredSpec, '\"' ] ).


%%------------------------------------------------------------------------------
%% is_a_variable_name( + term ):
%% Is this the name of a variable?

is_a_variable_name( Term ) :-
        atom( Term ),
        name_chars( Term, [ FirstChar | _ ] ),
        name_chars( FirstCharAtom, [ FirstChar ] ),
        (
            FirstCharAtom = '_',
            !
        ;
            upper_case_letter( FirstCharAtom )
        ).

%
upper_case_letter( Atom ) :-  uc( Atom ),  !.

uc( 'A' ).  uc( 'B' ). uc( 'C' ).  uc( 'D' ).  uc( 'E' ).  uc( 'F' ).
uc( 'G' ).  uc( 'H' ). uc( 'I' ).  uc( 'J' ).  uc( 'K' ).  uc( 'L' ).
uc( 'M' ).  uc( 'N' ). uc( 'O' ).  uc( 'P' ).  uc( 'Q' ).  uc( 'R' ).
uc( 'S' ).  uc( 'T' ). uc( 'U' ).  uc( 'V' ).  uc( 'W' ).  uc( 'X' ).
uc( 'Y' ).  uc( 'Z' ).


%%------------------------------------------------------------------------------
%% between( + integer, +- integer, + integer ):
%% Succeed if arg1 =< arg2 < arg3.
%% If arg2 is a variable, generate the appropriate values

between( A, V, B ) :-
        integer( A ),
        integer( B ),
        (
            integer( V )
        ->
            A =< V,  V < B
        ;
            var( V )
        ->
            between_generate( A, V, B )
        ).

%
between_generate( A, A, B ) :-
        A < B.

between_generate( A, V, B ) :-
        A < B,
        NA is A + 1,
        between_generate( NA, V, B ).


%%------------------------------------------------------------------------------
%% member_reversed( +- item, + list of items ):
%% Like member/2, but the order of searching/generation is reversed.

member_reversed( M, [ _ | L ] ) :-
        member_reversed( M, L ).
member_reversed( M, [ M | _ ] ).


%%------------------------------------------------------------------------------
%% remove( + item, + list, - list sans item ) :
%% The item is in the list: remove the first occurrence.

remove( Item, List, ListSansItem ) :-
        append( Prefix, [ Item | Postfix ], List ),
        append( Prefix, Postfix, ListSansItem ),
        !.


%%------------------------------------------------------------------------------
%% write_shallow_with_eq( + output stream, + term, + maximum depth ):
%% Like write_shallow/3, but instead of relying on the underlying mechanism of
%% Prolog write equations for terms that are cyclical at a depth that does not
%% excceed the maximum depth.  This procedure is due to Ronald de Haan of TU
%% Dresden.

write_shallow_with_eq( OutputStream, Term, MaxDepth ) :-
        cyclic( Term, MaxDepth ),
        !,
        get_printable_term_equation( Term, Head, List ),
        write_term( OutputStream, Head, [] ),
        print_equations( OutputStream, List ).

write_shallow_with_eq( OutputStream, Term, MaxDepth ) :-
        % \+ cyclic( Term, MaxDepth ),
        mk_variable_dictionary( Term, VarDict ),
        bind_variables_to_names( VarDict ),
        write_shallow( OutputStream, Term, MaxDepth ).


%% Print the list of equations.

print_equations( _OutputStream, [] ) :-
        !.

print_equations( OutputStream, [ H | T ] ) :-
        write_term( OutputStream, H, [] ),
        print_equations( OutputStream, T ).

%%------------------------------------------------------------------------------
