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

%%%  Eclipse-specific predicates that ease compatibility problems.           %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (February 2009)                       %%%
%%%                                                                          %%%

:- ensure_loaded( utilities ).
:- ensure_loaded( higher_order ).
:- ensure_loaded( library( metutl ) ).
:- import subsumes_chk/2 from metutl.  % but no good for cyclic terms! :-(


%%------------------------------------------------------------------------------
%% Identify the system.

lp_system( eclipse ).


%%------------------------------------------------------------------------------
%% The standard streams.

std_input_stream(   input          ).
std_output_stream(  output         ).
std_error_stream(   error          ).
std_warning_stream( warning_output ).


%%------------------------------------------------------------------------------
%% getchar( + input stream, - character in the form of an atom ):
%% This is introduced because the built-in get_char/2 returns strings on
%% Eclipse and atoms on Sicstus.

getchar( Stream, Atom ) :-
        get_char( Stream, String ),
        atom_string( Atom, String ).


%%------------------------------------------------------------------------------
%% name_chars( +- atom or number,
%%             -+ list of characters (codes) that form its name
%%           ):
%% Used because Eclipse complains about name/2 being obsolete.

name_chars( Atomic, NameCharCodes ) :-
        (
            var( Atomic )
        ->
            NameCharCodes = [ First | _ ],
            string_list( NameString, NameCharCodes ),
            (
                is_digit_char( First )
            ->
                number_string( Atomic, NameString )
            ;
                atom_string( Atomic, NameString )
            )
        ;
            atom( Atomic )
        ->
            atom_string( Atomic, NameString ),
            string_list( NameString, NameCharCodes )
        ;
            number( Atomic )
        ->
            number_string( Atomic, NameString ),
            string_list( NameString, NameCharCodes )
        ;
            error( [ 'Bad argument type in ',
                     name_chars( Atomic, NameCharCodes ) ]
                 )
        ).

%
is_digit_char( C ) :-
        name_chars( 0, [ ZeroChar ] ),
        ZeroChar =< C,
        name_chars( 9, [ NineChar ] ),
        NineChar >= C.


%%------------------------------------------------------------------------------
%% clause_in_module( + module name, +- clause head, - clause body ):
%% Like clause/2, but from the named module.

clause_in_module( ModuleName, Head, Body ) :-
        clause( Head, Body ) @ ModuleName .


%%------------------------------------------------------------------------------
%% current_predicate_in_module( + module name, +- predicate specification ):
%% Like current_predicate/2, but from the named module.

current_predicate_in_module( ModuleName, PredSpec ) :-
        current_predicate( PredSpec ) @ ModuleName .


%%------------------------------------------------------------------------------
%% assert_in_module( + module name, + clause ):
%% Like assert/1, but into this module.

assert_in_module( Module, Clause ) :-
        assertz_in_module( Module, Clause ).


%%------------------------------------------------------------------------------
%% assertz_in_module( + module name, + clause ):
%% Like assertz/1, but into this module.

assertz_in_module( Module, Clause ) :-
        assertz( Clause ) @ Module .


%%------------------------------------------------------------------------------
%% retractall_in_module( + module name, + head pattern ):
%% Like retractall/1, but into this module.

retractall_in_module( Module, Head ) :-
        retractall( Head ) @ Module .


%%------------------------------------------------------------------------------
%% call_in_module( + module name, + head pattern ):
%% Like call/1, but into this module.

call_in_module( Module, Head ) :-
        call( Head ) @ Module .


%%------------------------------------------------------------------------------
%% export_from_module( + module name, + predicate specification ):
%% export/1 factored out here, because Sicstus does not like the "@".

export_from_module( Module, PredSpec ) :-
        export( PredSpec ) @ Module.


%%------------------------------------------------------------------------------
%% dynamic_in_module( + module name, + predicate specification ):
%% dynamic/1 factored out here, because Sicstus does not like the "@".

dynamic_in_module( Module, PredSpec ) :-
        dynamic( PredSpec ) @ Module.


%%------------------------------------------------------------------------------
%% compile_to_module( + module name, + file name ):
%% Compile the program in this file into this module.

compile_to_module( Module, FileName ) :-
        compile( FileName ) @ Module.


%%------------------------------------------------------------------------------
%% copy_term2( + term, - term ):
%% Same as copy_term/2, but safe for cyclic terms.
%% In the case of Eclipse we have to resort to assert/retract.

:- dynamic ' COPY_TERM'/1.

copy_term2( Term, Copy ) :-
        assert( ' COPY_TERM'( Term ) ),
        retract( ' COPY_TERM'( Copy ) ).


%%------------------------------------------------------------------------------
%% are_variants( + term, + term ) :
%%    Succeeds only if both arguments are variants of each other.
%%    Does not instantiate any variables.
%% NOTE: In Eclipse this loops on cyclic terms.

are_variants( T1, T2 ) :-
        check( T1 = T2 ),                     % quickly weed out obvious misfits
        copy_term( T2, CT2 ),
        variant( T1, CT2 ).


%%------------------------------------------------------------------------------
%% write_shallow( + output stream, + term, + maximum depth ):
%% Like write/2, but only to a limited print depth.

write_shallow( OutputStream, Term, MaxDepth ) :-
        write_term( OutputStream, Term, [ depth( MaxDepth ) ] ).


%%------------------------------------------------------------------------------
%% is_built_in( +- goal ):
%% Does this goal call a built-in predicate?  Or generate a built-in goal.

is_builtin( Goal ) :-
        (
            nonvar( Goal )
        ->
            functor( Goal, P, K ),
            current_built_in( P/K )
        ;
            current_built_in( P/K ),
            functor( Goal, P, K )
        ).


%%------------------------------------------------------------------------------
%% ordered_term_variables( + term, - list of variables ):
%% Produce the set of variables in this term in the order of their occurrence.
%% (term_variables/2 does it in that order in Sicstus, but in reverse order in
%%  Eclipse.)

ordered_term_variables( Term, Variables ) :-
        term_variables( Term, Vs ),
        reverse( Vs, Variables ).


%%------------------------------------------------------------------------------
%% expand_term( + term, - expanded term ):
%% In Eclipse this is called expand_clause/2.
%% NOTE: No attempt to make hooks compatible, good enough for processing DCGs.

expand_term( T, ET ) :-  expand_clause( T, ET ).


%%------------------------------------------------------------------------------
%% flush_output( + output stream ):
%% Flush out the buffer of the stream.

flush_output( OutputStream ) :-
        flush( OutputStream ).

%%------------------------------------------------------------------------------
