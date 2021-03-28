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
%%%  A translator for co-logic programming.                                  %%%
%%%  Written by Feliks Kluzniak at UTD (January 2009).                       %%%
%%%                                                                          %%%
%%%  Last update: 24 February 2009.                                          %%%
%%%                                                                          %%%
%%%  NOTE: Some of the code may be Eclipse-specific and may require          %%%
%%%        minor tweaking for other Prolog systems.                          %%%


%%% General description
%%% -------------------
%%%
%%% This translator transforms "co-logic programming" programs into
%%% straightforward logic programs that can be compiled/executed in any
%%% logic programming system that does not incorporate the "occur check"
%%% in normal unification.
%%%
%%% The transformed programs may cause errors if they invoke built-in predicates
%%% that cannot handle cyclic terms (e.g., copy_term/2).
%%%
%%% NOTE: A transformed program cannot contain variable literals or invocations
%%%       of "call/1".
%%%       A transformed program cannot contain negative literals, unless they
%%%       are invocations of simple builtins or of predicates that were declared
%%%       as "support".
%%%       (Full negation will be provided in a forthcoming version.)
%%%


%%% Usage
%%% -----
%%%
%%% To translate a program contained in file "filename.clp", invoke
%%%
%%%    tc( filename ).
%%%
%%% (Notice that one can, but need not write down the extension ".clp".
%%%  However, to translate a file with a different extension one has to write
%%%  the full file name, thus : 'Foo.ext' .)
%%%
%%% The translator will read the program and --- if there are no fatal
%%% errors --- will write the transformed program on "filename.pl".
%%%
%%% NOTE: If "filename.pl" exists, it will be overwritten without warning.
%%%
%%% NOTE: A program that works in the coinductive interpreter should work almost
%%%       in the same fashion after it is translated and loaded directly into
%%%       Eclipse. The only difference should be that the interpreter executes
%%%       queries somewhat differently (more or less as if they were entered
%%%       interactively at the top level).
%%%       Unlike the interpreter, the translator does not act upon directives
%%%       that include files (e.g., ":- [ filename ].": such directives are
%%%       simply copied to output.  This is done on purpose, to allow separate
%%%       translation: if the file names are given without extensions, and all
%%%       the included files are also translated, then the effect of directives
%%%       in the translated program will be to include the translated files
%%%       (because the default extension will be different when loaded into
%%%       Eclipse).
%%%       There are, however, two directives that must be recognized. The first
%%%       is the operator declaration (i.e., ":- op( ... )") (and this is
%%        dealt with by "read_terms/2" in "utilities".  The second is
%%%       ":- tabled ...", which we must allow in order to process programs
%%%       that take advantage of both coinduction and tabling.  The translator
%%%       automatically transforms the predicate specifications in
%%%       ":- tabled ..." (unless they refer to predicates declared as
%%%       "support").
%%%       Moreover, the translator issues appropriate "essence_hook" clauses
%%%       that allow the implementation of tabling to strip the additional
%%%       "administrative" argument from instances of tabled predicates.  In
%%%       order to do that, it stores information about these predicates in an
%%%       internal table called "tabled".


%%% Directives
%%% ----------
%%%
%%% Queries will undergo the same transformation as clause bodies and be output
%%% with the translated program.
%%% In general, directives will be just copied to the translated program (i.e.,
%%% without transformation. However, there are two kinds of exceptions.  The
%%% first is ":- tabled ..." and ":- op( ... )", discussed above.  The second is
%%% that the following directives will be interpreted directly by the translator
%%% (and not copied):
%%%
%%% 1.
%%%     :- coinductive PredSpec .
%%%
%%%  (where PredSpec is of the form "p/k", or "p/k, q/k, ...": the item that
%%%   precedes the slash is the name of a predicate, and the item that follows
%%%   the slash is a natural number denoting the arity of the predicate).
%%%
%%%  These directives are treated as declarations of coinductive predicates.
%%%
%%% 2.
%%%     :- top PredSpec.
%%%
%%%  These are treated as declarations of predicates that will be invoked
%%%  directly by the user or non-coinductive programs.  In the translated
%%%  program these predicates will be available also in their original form
%%%  (i.e., there will be no need to take the transformation into account by
%%%  providing an additional argument: see the description of the transformation
%%%  below).
%%%
%%% 3.
%%%     :- support PredSpec.
%%%
%%%  These are treated as declarations of predicates that should be treated as
%%%  "normal" logic programming predicates, and should, therefore, not be
%%%  subjected to transformation.  A declaration of this sort constitutes a
%%%  claim by the programmer that the "support" predicate will not invoke ---
%%%  directly or indirectly --- any coinductive predicates.
%%%
%%%  NOTE: 1. It is an error for a coinductive predicate to be declared as
%%%           "support".
%%%        2. It is not necessary to declare built-in predicates in this
%%%           fashion.
%%%
%%%
%%% Please note that the various declarations of predicates should precede their
%%% definitions.  (It is a fatal error if they do not.)


%%% The transformation
%%% ------------------
%%%
%%% A. Every "normal" predicate (i.e., one that has not been declared as
%%%    "coinductive" or "support") will:
%%%
%%%      1. have its name extended with an underscore;
%%%
%%%      2. receive an additional argument (at the end of the argument list):
%%%         the argument will carry around a data structure that contains the
%%%         set of coinductive hypotheses (in the first version the data
%%%         structure is just a list).
%%%
%%%    For example, the predicate
%%%
%%%            p( X, Y ) :-  q( X, Z ),  r( Z, Y ).
%%%            p( X, X ).
%%%
%%%    will be transformed to
%%%
%%%            p_( X, Y, Hyp ) :-  q_( X, Z, Hyp ),  r_( Z, Y, Hyp ).
%%%            p_( X, X, _   ).
%%%
%%%
%%% B. If a predicate has been declared as "top", an additional hook will be
%%%    provided to facilitate invocation.  For example, if the definition of
%%%    p/2 above were preceded by
%%%
%%%           :- top p/2.
%%%
%%%    then the translator would output also
%%%
%%%           p( X, Y ) :-  p_( X, Y, [] ).
%%%
%%%    N.B. This feature is the reason predicate names are extended with an
%%%         undescore.  Our example program might well contain also occurrences
%%%         of p/1, which --- if the names were not changed --- would get
%%%         transformed to occurrences of p/2, and those would clash with this
%%%         additional "convenience predicate".
%%%
%%%
%%% C. If a predicate has been declared as "support", none of its occurrences is
%%%    transformed.  (This applies also to built-in predicates, with the obvious
%%%    exception of "meta-predicates" such as ",/2", "once/1" etc., some of
%%%    whose arguments are interpreted as predicates and must undergo the
%%%    transformation.)
%%%
%%%
%%% D. If a predicate has been declared as "coinductive", the transformation
%%%    is a little more involved:
%%%
%%%      1. the definition will be preceded by an additional clause that
%%%         nondeterministically queries the set of coinductive hypotheses;
%%%
%%%      2. the other clauses will extend the set of coinductive hypotheses
%%%         with an appropriate instantiation of the the goal that invoked them
%%%         (in the original form of the program).
%%%
%%%    For example, if the definition of p/2 above were preceded by
%%%
%%%           :- coinductive p/2.
%%%
%%%    then the transformed form would be (assuming the set of hypotheses is
%%%    represented as a list):
%%%
%%%
%%%           p_( X, Y, Hyp ) :-
%%%                   member( p( X, Y ), Hyp ).
%%%
%%%           p_( X, Y, Hyp ) :-
%%%                   NewHyp = [ p( X, Y ) | Hyp ],
%%%                   q_( X, Z, NewHyp ),
%%%                   r_( Z, Y, NewHyp ).
%%%
%%%           p_( X, X, _ ).
%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- ensure_loaded( '../general/utilities' ).



%-----  Wrapper  -----


%% tc( + filename ):
%% Open "filename.clp". If successful, translate its contents, producing output
%% on "filename.pl".

tc( FileName ) :-
        open_streams( FileName, InputStream, OutputStream ),

        translate( InputStream, OutputStream ),

        close( InputStream  ),
        close( OutputStream ).

%
% :- mode open_streams( +, -, - ).

open_streams( FileName, InputStream, OutputStream ) :-
        ensure_filename_is_an_atom( FileName ),
        name_chars( FileName, FileNameChars  ),
        name_chars( '.clp',   InputExtensionChars ),
        ensure_extension( FileNameChars,     InputExtensionChars,
                          RootFileNameChars, InputFileNameChars
                        ),
        name_chars( '.pl',   OutputExtensionChars ),
        append( RootFileNameChars, OutputExtensionChars, OutputFileNameChars ),
        name( InputFileName,  InputFileNameChars  ),
        name( OutputFileName, OutputFileNameChars ),
        open( InputFileName,  read , InputStream   ),
        open( OutputFileName, write, OutputStream  ).



%% translate( + input stream, + output stream ):
%% Translate the program on the input stream, writing the translation onto
%% the output stream.
%%
%% For greater flexibility (though not necessarily efficiency) we read all the
%% terms from the input stream to memory first, then process them in memory,
%% then write them out.

% :- mode translate( +, + ).

translate( InputStream, OutputStream ) :-
        read_terms_with_vars( InputStream, Pairs ),
        verify_program_with_vars( Pairs ),
        initialise_tables,
        map( first, Pairs, Terms ),
        transform( Terms, '', ProcessedTerms ),
        write_declarations_as_comments( OutputStream ),
        write_top_predicates( OutputStream ),
        write_essence_hook( OutputStream ),
        write_clauses( ProcessedTerms, OutputStream ).

%
first( pair( A, _ ), A ).




%-----  The main translator  -----


:- op( 1000, fy, coinductive ).    % allow  ":- coinductive p/k ."
:- op( 1000, fy, support ).        % allow  ":- support p/k ."
:- op( 1000, fy, top ).            % allow  ":- top p/k ."

:- op( 1000, fy, tabled ).         % allow also  ":- tabled p/k ."


%% A translator directive will be remembered in a dedicated table,
%% e.g., ":- coinductive p/2" as "coinductive( p( _, _ ) )".
%%
%% A ":- tabled ..." directive will also be remembered in a dedicated table.
%%
%% Moreover, the table "defined" will contain the name of each predicate the
%% processing of whose definition has been started (and possibly finished).

:- dynamic (coinductive)/1.
:- dynamic (support)/1.
:- dynamic (top)/1.
:- dynamic (tabled)/1.
:- dynamic defined/1.


%% initialise_tables:
%% Initialise the translator (make sure that no garbage is left from a previous
%% invocation).

initialise_tables :-
        retractall( coinductive( _ ) ),
        retractall( support( _ )     ),
        retractall( top( _ )         ),
        retractall( tabled( _ )      ),
        retractall( defined( _ )     ).



%% Write_declarations_as_comments( + output stream ):
%% Output comments that list the declarations of coinductive and support
%% predicates.

% :- mode write_declarations_as_comments( + ).

write_declarations_as_comments( OutputStream ) :-
        writeln( OutputStream, '%% COINDUCTIVE PREDICATES:' ),
        coinductive( Pattern ),                   % i.e., sequence through these
        write_pred_spec_comment( Pattern, OutputStream ),
        fail.

write_declarations_as_comments( OutputStream ) :-
        writeln( OutputStream, '%% \"SUPPORT\" PREDICATES:' ),
        support( Pattern ),                       % i.e., sequence through these
        write_pred_spec_comment( Pattern, OutputStream ),
        fail.

write_declarations_as_comments( OutputStream ) :-
        nl( OutputStream ).

%
%:- mode write_pred_spec_comment( +, + ).

write_pred_spec_comment( Pattern, OutputStream ) :-
        functor( Pattern, P, K ),
        write(   OutputStream, '%%   ' ),
        writeln( OutputStream, P / K ).



%% write_top_predicates( + output stream ):
%% Output the top predicates.

%:- mode write_top_predicates( + ).

write_top_predicates( OutputStream ) :-
        top( Pattern ),                           % i.e., sequence through these
        Pattern =.. [ F | Args ],
        transform_predicate_name( F, NF ),
        once( append( Args, [ [] ], ExtendedArgs ) ),
        Call =.. [ NF | ExtendedArgs ],
        writeclause( OutputStream, (Pattern :- Call) ),
        fail.

write_top_predicates( OutputStream ) :-
        nl( OutputStream ).



%% write_essence_hook( + output stream ):
%% Output "essence_hook/2" clauses for those tabled predicates that have not
%% been declared as support.

write_essence_hook( OutputStream ) :-
        tabled( Pattern ),                       % i.e., sequence through tabled
        \+ support( Pattern ),
        Pattern =.. [ F | Args ],
        drop_last( Args, ArgsButLast ),
        PatternButLast =.. [ F | ArgsButLast ],
        writeclause( OutputStream, (:- dynamic essence_hook/2) ),
        (
            lp_system( sicstus )
        ->
            writeclause( OutputStream, (:- multifile( essence_hook/2) ) )
        ;
            true
        ),
        writeclause( OutputStream, essence_hook( Pattern, PatternButLast ) ),
        fail.

write_essence_hook( _ ).

%
% Note that the pattern is after transformation, so must contain at least the
% last argument!

drop_last( List, ListWithoutLast ) :-
        append( ListWithoutLast, [ _ ], List ),
        !.





%% transform( + list of terms,
%%            + most general instance of the current predicate,
%%            - list of processed terms
%%          ):
%% Process the terms, i.e., interpret translator directives and transform
%% other directives, queries and clauses.
%% Information about the current predicate is provided to assist in the
%% detection of the first clause of a coinductive predicate, which requires
%% special treatment; it also helps detect non-contiguous predicate definitions.

%:- mode transform( +, +, - ).

transform( [], _, [] ) :-
        !.

transform( [ (:- tabled PredSpecs) | Terms ],
           _,
           [(:- tabled NewPredSpecs) | NewTerms ]
         ) :-
        !,
        transform_pred_specs( PredSpecs, NewPredSpecs ),
        store_info_about_tabled( NewPredSpecs ),
        transform( Terms, '', NewTerms ).

transform( [ (:- Directive) | Terms ], _, NewTerms ) :-
        is_a_translator_directive( Directive ),
        !,
        process_translator_directive( Directive ),
        transform( Terms, '', NewTerms ).

transform( [ (:- Directive) | Terms ], _, [ (:- Directive) | NewTerms ] ) :-
        !,
        transform( Terms, '', NewTerms ).

transform( [ (?- Query) | Terms ], _, [ (?- NewQuery) | NewTerms ] ) :-
        !,
        transform_body( Query, [], NewQuery ),
        transform( Terms, '', NewTerms ).

transform( [ Clause | Terms ], CurrentPred,
           [ ExtraClause, NewClause | NewTerms ]
         ) :-
        get_clause_head( Clause, Head ),
        Head \= CurrentPred,
        coinductive( Head ),             % beginning a new coinductive predicate
        !,
        most_general_instance( Head, Pattern ),
        starting_new_predicate( Pattern ),
        transform_logical_atom( Pattern, HypVar, NewPattern ),
        ExtraClause = (NewPattern :- member( Pattern, HypVar )),
        transform_clause( Clause, NewClause ),
        transform( Terms, Pattern, NewTerms ).

transform( [ Clause | Terms ], CurrentPred, [ NewClause | NewTerms ] ) :-
        get_clause_head( Clause, Head ),
        Head \= CurrentPred,
        % \+ coinductive( Head ),        % beginning a new "normal" predicate
        !,
        most_general_instance( Head, Pattern ),
        starting_new_predicate( Pattern ),
        transform_clause( Clause, NewClause ),
        transform( Terms, Pattern, NewTerms ).

transform( [ Clause | Terms ], CurrentPred, [ NewClause | NewTerms ] ) :-
        % get_clause_head( Clause, Head ),
        % check( Head = CurrentPred ),              % i.e., not the first clause
        !,
        transform_clause( Clause, NewClause ),
        transform( Terms, CurrentPred, NewTerms ).



%% store_info_about_tabled( + predicate specifications ):
%% Remember the tabled predicates in order to be able to issue appropriate
%% "essence_hook/2" clauses.

store_info_about_tabled( PredSpecs ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        member( Pattern, Patterns ),               % i.e., sequence through list
        assert( tabled( Pattern ) ),
        fail.

store_info_about_tabled( _ ).


%% starting_new_predicate( + most general instance of a predicate ):
%% We are beginning to work on the definition of this predicate.
%% Check that there is no contiguity error, mark the predicate as defined.

%:- mode starting_new_predicate( + ).

starting_new_predicate( Pattern ) :-
        check_contiguity( Pattern ),
        assert( defined( Pattern ) ).


%% check_contiguity( + head of a clause ):
%% We have encountered what seems to be the first clause of a predicate.
%% If this predicate has already been defined, raise a fatal error.

%:- mode check_contiguity( + ).

check_contiguity( Head ) :-
        defined( Head ),
        !,
        functor( Head, P, K ),
        error( [ 'Clauses for predicate ', P/K, ' are not contiguous' ] ).

check_contiguity( _ ).




%% transform_pred_specs( + predicate specifications, - ditto transformed ):
%% Transform each p/k into p_/(k+1), unless p/k is declared as "support".

transform_pred_specs( (PredSpec , PredSpecs), (NewPredSpec , NewPredSpecs) ) :-
        !,
        transform_pred_spec( PredSpec, NewPredSpec ),
        transform_pred_specs( PredSpecs, NewPredSpecs ).

transform_pred_specs( PredSpec, NewPredSpec ) :-
        transform_pred_spec( PredSpec, NewPredSpec ).

%
transform_pred_spec( PredSpec, PredSpec ) :-
        predspec_to_pattern( PredSpec, Pattern ),      % also checks correctness
        support( Pattern ),
        !.

transform_pred_spec( P / K, NP / K1 ) :-
        transform_predicate_name( P, NP ),
        K1 is K + 1.


%% transform_clause( + clause, - transformed clause ):
%% Transform a clause.
%% See the main comment for a description of the transformation.

%:- mode transform_clause( +, - ).

transform_clause( (Head :- Body), NewClause ) :-
        coinductive( Head ),
        !,
        transform_logical_atom( Head, HypVar, NewHead ),
        transform_body( Body, NewHypVar, NewBody ),
        NewClause = (NewHead :- NewHypVar = [ Head | HypVar ], NewBody).

transform_clause( (Head :- Body), (NewHead :- NewBody) ) :-
        % \+ coinductive( Head ),
        !,
        transform_logical_atom( Head, HypVar, NewHead ),
        transform_body( Body, HypVar, NewBody ).

transform_clause( Fact, NewFact ) :-
        % Fact \= (_ :- _),
        transform_logical_atom( Fact, _, NewFact ).



%% transform_body( + body, + set of hypotheses, - new body ):
%% Transform the body of a clause.
%% NOTE: The set of hypotheses may be a variable that will be instantiated only
%%       when the transformed program is run.


transform_body( Var ) :-
        !,
        error( [ 'Variable literal: \"', Var, '\"' ] ).

transform_body( (Calls1 , Calls2), HypVar, (NewCalls1 , NewCalls2) ) :-
        !,
        transform_body( Calls1, HypVar, NewCalls1 ),
        transform_body( Calls2, HypVar, NewCalls2 ).

transform_body( (Calls1 ; Calls2), HypVar, (NewCalls1 ; NewCalls2) ) :-
        !,
        transform_body( Calls1, HypVar, NewCalls1 ),
        transform_body( Calls2, HypVar, NewCalls2 ).

transform_body( (If -> Then ; Else), HypVar, (NewIf -> NewThen ; NewElse) ) :-
        !,
        transform_body( If, HypVar, NewIf ),
        transform_body( Then, HypVar, NewThen ),
        transform_body( Else, HypVar, NewElse ).

transform_body( (If -> Then), HypVar, (NewIf -> NewThen) ) :-
        !,
        transform_body( If, HypVar, NewIf ),
        transform_body( Then, HypVar, NewThen ).


transform_body( Call, HypVar, NewCall ) :-
        transform_logical_atom( Call, HypVar, NewCall ).



%% transform_logical_atom( + logical atom,
%%                         + variable with set of hypotheses,
%%                         - transformed atom
%%                       ):
%% Transform this head or simple call.

%:- mode transform_logical_atom( +, ?, - ).

transform_logical_atom( \+ C, _, \+ C ) :-
        support( C ),
        !.

transform_logical_atom( \+ C, _, \+ C ) :-
        is_builtin( C ),
        C \= once( _ ),
        C \= call( _ ),
        !.

transform_logical_atom( \+ C, _, _ ) :-
        !,
        error( [ 'Negative literal: \"', \+ C, '\"' ] ).

transform_logical_atom( call( C ), _, _ ) :-
        !,
        error( [ 'Invocation of \"call/1\": \"', call( C ), '\"' ] ).

transform_logical_atom( once( Calls ), Hyp, once( NewCalls ) ) :-
        !,
        transform_body( Calls, Hyp, NewCalls ).

transform_logical_atom( Pred, _, Pred ) :-
        (support( Pred ) ; is_builtin( Pred )),
        !.

transform_logical_atom( Pred, HypVar, NewPred ) :-
        % \+ (support( Pred ) ; is_built_in( Pred )),
        Pred =.. [ Name | Args ],
        transform_predicate_name( Name, NewName ),
        once( append( Args, [ HypVar ], NewArgs ) ),
        NewPred =.. [ NewName | NewArgs ].


%% transform_predicate_name( + name, - new name ):
%% Transform the name of a predicate (by extending it with "_").

%:- mode transform_predicate_name( +, - ).

transform_predicate_name( Name, NewName ) :-
        concat_atoms( Name, '_', NewName ).




%%%%%  Translator directives


%% is_a_translator_directive( + directive ):
%% Is this one of the directives that are interpreted by the translator?

%:- mode is_a_translator_directive( + ).

is_a_translator_directive( (coinductive _) ).
is_a_translator_directive( (support     _) ).
is_a_translator_directive( (top         _) ).



%% process_translator_directive( + directive ):
%% Interpret a translator directive.

%:-  mode process_translator_directive( + ).

process_translator_directive( (coinductive PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        declare_coinductive( Patterns ).

process_translator_directive( (support PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        declare_support( Patterns ).

process_translator_directive( (top PredSpecs) ) :-
        predspecs_to_patterns( PredSpecs, Patterns ),
        declare_top( Patterns ).



%% declare_coinductive( + list of general instances ):
%% Store the general instances in "coinductive", warning about duplications.
%% An overlap with "support" is a fatal error.

declare_coinductive( Patterns ) :-
        member( Pattern, Patterns ),              % i.e., sequence through these
        check_declaration_order( Pattern, 'coinductive' ),
        (
            support( Pattern )
        ->
            overlap_error( Pattern )
        ;
            true
        ),
        (
            coinductive( Pattern )
        ->
            duplicate_warning( Pattern, 'coinductive' )
        ;
            assert( coinductive( Pattern ) )
        ),
        fail.

declare_coinductive( _ ).


%% declare_support( + list of general instances ):
%% Store the general instances in "support", warning about duplications.
%% An overlap with "coinductive" is a fatal error.

declare_support( Patterns ) :-
        member( Pattern, Patterns ),              % i.e., sequence through these
        check_declaration_order( Pattern, 'support' ),
        (
            coinductive( Pattern )
        ->
            overlap_error( Pattern )
        ;
            true
        ),
        (
            support( Pattern )
        ->
            duplicate_warning( Pattern, 'support' )
        ;
            assert( support( Pattern ) )
        ),
        fail.

declare_support( _ ).


%% declare_top( + list of general instances ):
%% Store the general instances in "top", warning about duplications.

declare_top( Patterns ) :-
        member( Pattern, Patterns ),             % i.e., sequence through these
        check_declaration_order( Pattern, 'top' ),
        (
            top( Pattern )
        ->
            duplicate_warning( Pattern, 'top' )
        ;
            assert( top( Pattern ) )
        ),
        fail.

declare_top( _ ).


%% duplicate_warning( + most general instance of a predicate,
%%                    + kind of declaration
%%                  ):
%% The predicate has been declared twice for this kind: raise a warning.

%:- mode duplicate_warning( +, + ).

duplicate_warning( Pattern, Kind ) :-
            functor( Pattern, P, K ),
            warning( [ 'Duplicate declaration of ', P / K,
                       ' as a \"', Kind, '\" predicate'
                     ]
                   ).


%% overlap_error( + most general instance of a predicate ):
%% The predicate has been declared as both "coinductive" and "support":
%% raise a fatal error.

%:- mode overlap_error( + ).

overlap_error( Pattern ) :-
            functor( Pattern, P, K ),
            error( [ P/K, ' declared both as \"coinductive\" and as \"support\"'
                   ]
                 ).


%% check_declaration_order( + the most general instance of a predicate,
%%                          + kind of declaration
%%                        ):
%% Raise a fatal error if the definition of this predicate has already been
%% seen.

%:- mode check_declaration_order( +, + ).

check_declaration_order( Pattern, Kind ) :-
        defined( Pattern ),
        !,
        functor( Pattern, P, K ),
        error( [ P/K, ' declared as \"', Kind, '\" after it has been defined' ]
             ).

check_declaration_order( _, _ ).

%-------------------------------------------------------------------------------
