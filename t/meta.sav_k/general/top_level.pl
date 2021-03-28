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
%%%  A simple (!) general top level for metainterpreters.                    %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (January 2009).                       %%%
%%%                                                                          %%%
%%%  Last update: 12 June 2009.                                              %%%
%%%                                                                          %%%
%%%  NOTE: This code runs on Sicstus and Eclipse.  It may require some       %%%
%%%        tweaking for other Prolog systems.                                %%%
%%%                                                                          %%%

%%% NOTES FOR USERS:
%%%
%%%    1. To use this top level, just include it in your the file that
%%%       contains the code for your metainterpreter:
%%%
%%%           :- ensure_loaded( '../general/top_level' ).
%%%
%%%       Then load the metainterpreter into your logic programming system.
%%%
%%%
%%%    2. To begin execution by loading a new program, invoke
%%%
%%%           prog( filename ).
%%%
%%%       If the filename has no extension, the default extension will be
%%%       used if provided (see the description of "default_extension" below).
%%%
%%%       As the file is loaded, directives and queries are executed on-the-fly
%%%       by invoking the metainterpreter (except the ":- op ..." directive,
%%%       which is interpreted directly). A query is evaluated to give all
%%%       solutions (it is as if the user kept responding with a semicolon):
%%%       to avoid that use the built-in predicate once/1 .
%%%
%%%       After the file is loaded (and all the directives and queries it
%%%       contains are executed), interactive mode is started.  This is very
%%%       much like the usual top-level loop, except that the associated
%%%       metainterpreter -- and not the underlying Logic Programming system --
%%%       is used to evaluate queries and directives.
%%%
%%%
%%%       To just enter interactive mode invoke
%%%
%%%           top
%%%
%%%       To exit interactive mode enter end of file (^D), or just write
%%%
%%%           quit.
%%%
%%%       (the former method appears not to work with tkeclipse).
%%%
%%%       NOTE: 1. In the interactive mode one cannot input more than one term
%%%                per line.
%%%
%%%             2. When a query succeeds, the bindings of variables should be
%%%                printed upto a certain maximum depth.  The default value is
%%%                given in print_depth/1 below.  The maximum depth can be
%%%                changed from the interpreted program by invoking
%%%
%%%                   set_print_depth( N )
%%%
%%%                where N is a positive integer.
%%%
%%%                Please note that on some Prolog implementations (e.g.,
%%%                Eclipse) this might not prevent a loop if the printed term
%%%                is cyclic (as will often happen for coinductive programs).
%%%
%%%                Note also that the foregoing does not apply to invocations of
%%%                builtins in the interpreted program.  It is up to the user to
%%%                apply the builtin appropriate for the host logic programming
%%%                system.  For example, in the case of Sicstus, use
%%%                "write_term( T, [ max_depth( 10 ) ] )" rather than just
%%%                "write( T )", especially if you expect T to be a cyclic term.
%%%
%%%
%%%    3. To include files (interactively or from other files) use
%%%       the usual Prolog syntax:
%%%
%%%           :- [ file1, file2, ... ].
%%%
%%%       Please note that there is a difference between "prog( file )" and
%%%       ":- [ file ].".  If the former is used, the metainterpreter is
%%%       (re)initialised before loading the file (see description of
%%%       initialise/0  below); if the latter is used, the file is just loaded.
%%%
%%%
%%%    4. The program that is read in must not contain variable literals.  It
%%%       may, however, contain invocations of call/1.
%%%
%%%
%%%    5. The interpreted program may contain declarations of "top" and
%%%       "support" predicates, in the form of directives:
%%%
%%%           :- top p/1, q/2.
%%%           :- support check_consistency/1.
%%%
%%%       The "top" declaration indicates predicates that will be called "from
%%%       the outside", so if they are not called in the program, there will be
%%%       no warning.
%%%       (This declaration is also recognized when translating coinductive
%%%        programs into Prolog: see "../coind/translate_colp".)
%%%
%%%       The "support" declaration means that the metainterpreter should treat
%%%       this predicate as a built-in, i.e., just let Prolog execute it.  This
%%%       can be useful for increasing the efficiency of interpreted programs
%%%       that make use of support routines that are written in "straight"
%%%       Prolog.  (Please note also that support predicates can use the full
%%%       range of built-in predicates available in the host logic programming
%%%       system.)
%%%
%%%       Predicates that are declared as "support" must be defined in other
%%%       files.  To compile and load such files, use
%%%
%%%           :- load_support( filename ).



%%% NOTES FOR AUTHORS OF METAINTERPRETERS:
%%%
%%%    6. The clauses read in by the top level are loaded into the module
%%%       "interpreted".  This is done to avoid conflicts with predicates
%%%       used in the metainterpreter (and the top level).  The metainterpreter
%%%       must access them by using the predicate imported from
%%%       "compatibility_utilties_...":
%%%           clause_in_module( interpreted, ... )
%%%
%%%       The predicates defined by these clauses are stored in the table
%%%       defined/1, in the form of patterns, e.g.,
%%%           defined( p( _, _ ) ).
%%%
%%%
%%%    7. The top level notes "support" declarations in the table "support".
%%%       For example,
%%%
%%%           :- support p/1, q/2.
%%%
%%%       will be stored as
%%%
%%%           support( p( _ ) ).
%%%           support( q( _, _ ) ).
%%%
%%%       The intended meaning is that "support" predicates do not make use
%%%       (directly or indirectly) of the special features provided by the
%%%       metainterpreter, so their invocations can be handled just by handing
%%%       them over to Prolog (which would presumably speed up the computation).
%%%
%%%       Please note that the support predicates (which should be defined in
%%%       files mentioned in ":- load_support( filename )." directives) are
%%%       compiled into the module "support" (unless they are defined within
%%%       other modules).
%%%
%%%
%%%    8. The metainterpreter should provide the following predicates
%%%       ("hooks") that will be called by the top level:
%%%
%%%          - builtin/1:
%%%                 Defines patterns for built-in predicates from the host
%%%                 system that can be invoked by the interpreted program.
%%%                 For example, to allow writeln/2, declare:
%%%                     builtin( writeln( _, _ ) ).
%%%
%%%          - default_extension/1:
%%%                 This predicate is optional.  If present, its argument
%%%                 should be an atom whose name is the extension string to be
%%%                 added to file names that do not already have an extension.
%%%                 (The string should begin with a period!)
%%%                 For example, a metainterpreter for coinductive logic
%%%                 programming might contain the following fact:
%%%                      default_extension( '.clp' ).
%%%
%%%          - initialise/0:
%%%                 This will be called before loading a new program,
%%%                 giving the metainterpreter an opportunity to
%%%                 (re)initialise its data structures.
%%%
%%%          - program_loaded/0:
%%%                 This will be called after a program has been read in from
%%%                 its file and stored in memory.  The interpreter can use
%%%                 the opportunity to check the program's consistency, to
%%%                 transform the program, etc.
%%%
%%%          - legal_directive/1:
%%%                 Whenever the top level encounters a directive
%%%                 (of the form ":- D."), it will call "legal_directive( D )".
%%%                 If the call succeeds, the interpreter will be given
%%%                 a chance to process the directive (see below), otherwise
%%%                 the directive will be ignored (with a suitable warning).
%%%
%%%          - execute_directive/1:
%%%                 Whenever the top level encounters a legal directive
%%%                 ":- D" (see above), it invokes "execute_directive( D )"
%%%                 to give the interpreter a chance to act upon the
%%%                 directive.
%%%
%%%          - query/1:
%%%                 This would be the main entry point of the metainterpreter.
%%%                 Whenever the top level encounters a query (of the form
%%%                 "?- Q."), it will display the query and then call
%%%                 "query( Q )".  Depending on the result, it will then
%%%                 display "No", or "Yes" (preceded by a display of bindings
%%%                 acquired by the variables occurring in "Q"); in the latter
%%%                 case it will also backtrack to obtain more solutions.
%%%
%%%
%%%    9. The metainterpreter can also define hooks of its own.  A hook
%%%       predicate should be declared in a fact of "hook_predicate/1".
%%%       For example,
%%%
%%%           hook_predicate( essence_hook( _, _ ) ).
%%%
%%%       declares that "essence_hook/2" is a metainterpreter hook.  A hook
%%%       predicate (essence_hook/2 in this case) should be dynamic.  When
%%%       the top level encounters a clause whose head matches a hook predicate
%%%       declaration, the clause is asserted at the front (!) of the predicate
%%%       (in the module of the running program, not in "interpreted").
%%%
%%%       NOTE: If the interpreter does not use hook predicates, it must contain
%%%             the definition
%%%                 hook_predicate( '' ).


:- ensure_loaded( utilities ).
:- ensure_loaded( program_consistency ).
:- ensure_loaded( output_equation ).

:- op( 1010, fy, top          ).     % allow  ":- top p/k ."
:- op( 1010, fy, support      ).     % allow  ":- support p/k ."
:- op( 1010, fy, load_support ).     % allow  ":- load_support filename ."

:- dynamic (support)/1.
:- dynamic (top)/1.
:- dynamic (defined)/1.


% If "p/k" has already been seen (and declared as dynamic), the fact is recorded
% as "known( p( _, _, ...) )" (with "k" arguments).
% (Unlike Sicstus, Eclipse requires a dynamic declaration before the first
%  assert.)

:- dynamic known/1 .


%% Default print depth.  (May be changed by the metainterpreter by invoking
%% set_print_depth( N ).)

:- dynamic print_depth/1 .

print_depth( 10 ).

%
set_print_depth( N ) :-
        integer( N ),
        N > 0,
        !,
        retract( print_depth( _ ) ),
        assert(  print_depth( N ) ).

set_print_depth( Strange ) :-
        error( [ 'The argument of set_print_depth/1 is not a positive integer',
                 ': \"', Strange, '\"'
               ]
             ).




%% prog( + file name ):
%% Initialise, then load a program from this file, processing directives and
%% queries.  After this is done, enter interactive mode.


prog( FileName ) :-
        setup,
        initialise,                              % provided by a metainterpreter
        process_file( FileName ),
        check_general_consistency,
        program_loaded,                          % provided by a metainterpreter
        top.

%
setup :-
        retractall( known( _ )   ),
        retractall( support( _ ) ),
        retractall( top( _ )     ),
        retractall( defined( _ ) ),
        erase_modules,
        create_modules.



%% NOTE: In Eclipse it is possible to use the module facility in a way that
%%       allows redeclaration of predicates that are built-ins, but that are
%%       not wanted (see below).  It is not obvious how to do it in Sicstus, so
%%       the interpreted program cannot define predicates whose names happen to
%%       clash with the names of built-ins. Hence in the Sicstus version
%%       the only modules that are created are "interpreted" and support.
%%
%% NOTE (Specific to Eclipse):
%%       In order to avoid name conflicts with the numerous built-in predicates
%%       of Eclipse, the only thing "interpreted" imports is the module
%%       "interface".  The module "interface" is created by the top-level from
%%       a declaration of built-ins allowed by the metainterpreter (and provided
%%       by the latter in table "builtin").  The difficulty is that Eclipse does
%%       not allow direct exportation of built-ins: this is solved by defining
%%       yet another module, called "interface_aux".
%%       The exact mechanics are best explained by means of an example:
%%
%%       1. Let the metainterpreter contain a declaration of only one built-in:
%%             builtin( writeln( _ ) ).
%%
%%       2. The top level will add the following clause to module
%%          "interface_aux" (which imports all the built-ins by default):
%%             xxx_writeln( X ) :-  writeln( X ).
%%
%%       3. "xxx_writeln/1" will be exported by "interface_aux".
%%
%%       4. Module "interface" will import only "interface_aux", and will be
%%          closed to default importation of built-ins.  It will define clause:
%%             writeln( X) :- xxx_writeln( X ).
%%
%%       5. "writeln/1" is now a user-defined predicate and can be exported from
%%          "interface".
%%
%%       6. "interpreted" will import only "interface", and will be closed to
%%          default importation of built-ins.  The interpreted program can use
%%          "writeln/1" and no other built-ins.  It can also define predicates
%%          whose names would normally clash with names of built-ins (e.g.,
%%          "connect/2", which might be useful in, say, a graph-processing
%%          application).
%%
%%       Please note that all this does not apply to "support".

%% erase_modules:
%% Erase the modules that might be there after interpreting the previous
%% program.

erase_modules :-
        erase_module( interpreted ),
        erase_module( support ),
        (
            lp_system( eclipse )
        ->
            erase_module( interface ),
            erase_module( interface_aux )
        ;
            true
        ).


%% create_modules:
%% Create the modules.
%% (In Sicstus this is a no-op: the module "interpreted" will be created
%%  dynamically with the first assertion.)

create_modules :-
        \+ lp_system( eclipse ),
        !.

create_modules :-
        lp_system( eclipse ),
        create_module( interface_aux ),
        create_module( interface  , [], [ interface_aux ] ),
        create_module( interpreted, [], [ interface     ] ),
        create_module( support ),
        fill_interface_modules.

%
fill_interface_modules :-
        builtin( Pattern ),
        functor( Pattern, F, K ),
        concat_atoms( 'xxx_', F, ExtF ),
        mk_pattern( ExtF, K, ExtPattern ),
        ExtPattern =.. [ _ | Args ],
        Pattern    =.. [ _ | Args ],     % i.e., unify arguments of the patterns
        assertz_in_module( interface_aux, (ExtPattern :- Pattern) ),
        assertz_in_module( interface,     (Pattern :- ExtPattern) ),
        export_from_module( interface_aux, ExtF / K ),
        export_from_module( interface    , F    / K ),
        fail.

fill_interface_modules.




%% process_file( + file name ):
%% Load a program from this file, processing directives and queries.

% :- mode process_file( + ).

process_file( FileName ) :-
        open_the_file( FileName, ProgStream ),
        process_input( ProgStream ),
        close( ProgStream ).

%
open_the_file( FileName, ProgStream ) :-
        ensure_filename_is_an_atom( FileName ),
        name_chars( FileName, FileNameChars ),
        (
            default_extension( Ext ),             % provided by metainterpreter?
            name_chars( Ext, ExtChars ),
            !
        ;
            ExtChars = []
        ),
        ensure_extension( FileNameChars, ExtChars, _, FullFileNameChars ),
        name_chars( FullFileName, FullFileNameChars ),
        open( FullFileName, read, ProgStream ).



%% process_input( + input stream ):
%% Read the stream, processing directives and queries and storing clauses.

% :- mode process_input( + ).

process_input( ProgStream ) :-
        repeat,
        readvar( ProgStream, Term, VarDict ),
        preliminary_processing( Term, VarDict, NewTerm, NewVarDict ),
        process_term( NewTerm, NewVarDict ),
        NewTerm = end_of_file,              % i.e., normally fail to repeat
        !.

%
preliminary_processing( Term, VarDict, NewTerm, NewVarDict ) :-
        expand_term( Term, NewTerm ),
        expand_variable_dictionary( NewTerm, VarDict, NewVarDict ),
        verify_program_item( NewTerm, NewVarDict ).




%% process_term( + term, + variable dictionary ):
%% Process a term, which should be a directive, a query, a program clause or
%% end_of_file.
%% The variable dictionary is used for printing out the results of a query.
%%
%% NOTE: The superficial correctness of this term as a program item has already
%%       been verified by "verify_program_item/2".

% :- mode process_term( +, + ).

process_term( end_of_file, _ ) :-  !.            % just ignore this

process_term( (:- [ H | T ]), _ ) :-             % include
        !,
        include_files( [ H | T ] ).

process_term( (:- op( P, F, Ops )), _ ) :-
        !,
        op( P, F, Ops ).

process_term( (:- Directive), _ ) :-
        !,
        process_directive( Directive ).

process_term( (?- Query), VarDict ) :-
        !,
        process_query( Query, VarDict ),
        !.                                            % no alternative solutions

process_term( Clause, VarDict ) :-
        get_clause_head( Clause, Head ),
        hook_predicate( Head ),               % metainterpreter's hook predicate
        !,
        check_not_builtin( Clause, VarDict ),      % fatal if redefining builtin
        contiguity_check( Clause ),
        asserta( Clause ).

process_term( Clause, VarDict ) :-
        check_not_builtin( Clause, VarDict ),      % fatal if redefining builtin
        ensure_dynamic( Clause ),
        contiguity_check( Clause ),
        assertz_in_module( interpreted, Clause ).


%% include_files( + list of file names ):
%% Process the files whose names are in the list.

% :- mode include_files( + ).

include_files( List ) :-
        member( FileName, List ),
        process_file( FileName ),
        fail.

include_files( _ ).


%% contiguity_check( + clause ):
%% Make sure that each predicate that is defined by a clause is stored in the
%% table "defined/1".
%% If the clause adds to the definition of a predicate that is present in
%% the table but is not the most recent entry (i.e., is not the predicate
%% defined by the previous clause), then issue a warning about non-contiguous
%% definitions.

contiguity_check( Clause ) :-
        get_clause_head( Clause, Head ),
        most_general_instance( Head, Pattern ),
        (
            once( defined( P ) ),  P = Pattern    % predicate as in last clause?
        ->
            true
        ;
            \+ defined( Pattern )
        ->
            asserta( defined( Pattern ) )
        ;
            functor( Pattern, P, K ),
            warning( [ 'Non-contiguous declaration of ', P/K ] )
        ).





%% ensure_dynamic( + clause ):
%% Make sure the predicate of this clause is dynamic.
%% known/1 is used to avoid multiple declarations.
%% (NOTE: This is specific to Eclipse.)

% :- mode ensure_dynamic( + ).

ensure_dynamic( Clause ) :-
        lp_system( eclipse ),
        get_clause_head( Clause, Head ),
        \+ known( Head ),
        most_general_instance( Head, Pattern ),
        assert( known( Pattern ) ),
        functor( Head, PredicateName, Arity ),
        dynamic_in_module( interpreted, PredicateName / Arity ),
        fail.

ensure_dynamic( _ ).



%% process_directive( + directive ):
%% Process a directive.

% :- mode process_directive( + ).

process_directive( (top all) ) :-
        !,
        assert( top( _ ) ).

process_directive( (top PredSpecs) ) :-
        !,
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( top( Pattern ) ),
            fail
        ;
            true
        ).

process_directive( (support PredSpecs) ) :-      % store in "support" table
        !,
        predspecs_to_patterns( PredSpecs, Patterns ),
        (
            member( Pattern, Patterns ),
            assert( support( Pattern ) ),
            fail
        ;
            true
        ).

process_directive( (load_support FileName) ) :-  % compile into module "support"
        !,
        compile_to_module( support, FileName ).

process_directive( Directive ) :-
        legal_directive( Directive ),            % provided by a metainterpreter
        !,
        execute_directive( Directive ).          % provided by a metainterpreter

process_directive( Directive ) :-                % unsupported directive
        % \+ legal_directive( Directive ),
        !,
        error( lines( [ 'Unknown directive:', [ (:- Directive), '.' ] ] ) ).


%% process_query( + query, + variable dictionary ):
%% Process a query, i.e., produce and display solutions until
%% no more can be found.

% :- mode process_query( +, + ).

process_query( Query, VarDict ) :-
        std_output_stream( Output ),
        write( Output, '-- Query: ' ),
        write( Output, Query ),
        writeln( Output, '.  --' ),
        execute_query( Query, Result ),
        show_result( Result, VarDict ),
        nl( Output ),
        Result = no.                             % i.e., backtrack if 'yes'.

%
% :- mode execute_query( +, + ).

execute_query( Query, yes ) :-
        query( Query ).                          % provided by a metainterpreter

execute_query( _, no ).


%% show_result( + yes or no, + variable dictionary ).
%% Write the bindings and "Yes", or just "No".
%% NOTE: the newline is not written here, as it is not wanted in top/0.

% :- mode show_result( +, + ).

show_result( yes, VarDict ) :-
        !,
        std_output_stream( Output ),
        show_bindings( VarDict ),
        write( Output, 'Yes' ).

show_result( no, _ ) :-
        std_output_stream( Output ),
        write( Output, 'No' ).


%% show_bindings( + variable dictionary ):
%% Use the variable dictionary to show the results of a query.
%% (Recall that the variable dictionary is in Eclipse format.)
%% This version uses Ronald de Haan's equation generator
%% (see output_equations.pl) to display cyclic terms.

% :- mode show_bindings( + ).

% OLD VERSION:
% show_bindings( Dict ) :-
%         std_output_stream( Output ),
%         print_depth( MaxDepth ),
%         member( [ Name | Var ], Dict ),
%         write( Output, Name ),
%         write( Output, ' = ' ),
%         write_shallow( Output, Var, MaxDepth ),
%         nl( Output ),
%         fail.
%
% show_bindings( _ ).

show_bindings( VarDict ) :-
        extract_vars_from_dict( VarDict, TopTerms ),  % instantiations, actually
        Parcel =.. [ '_parcel' | TopTerms ],          % a term with top "vars"
        get_equation( Parcel, Equations ),
        get_equation_with_variables( Equations, EquationList, HeadVar ),
        most_general_instance( Parcel, ParcelPattern ),
        remove( _ = ParcelPattern, EquationList, EquationListSansParcel ),
        % The above has instantiated ParcelPattern so that its arguments are now
        % the new versions of the instantiations of top variables: we must now
        % replace the old versions with the new ones:
        ParcelPattern =.. [ _ | NewTopTerms ],
        swap_terms( VarDict, NewTopTerms, NewVarDict ),
        % A variable dictionary for the new variables:
        mk_variable_dictionary( p( HeadVar, EquationListSansParcel ), AuxVarDict
                              ),
        % Create equations for the top variables:
        map( mk_eq, NewVarDict, TopEqs ),
        % Bind all uninstantiated variables to their names:
        bind_free_variables_to_names( NewVarDict ),         % names in query
        bind_free_variables_to_names( AuxVarDict ),         % names for new vars
        % A unified list of all the equations:
        append( TopEqs, EquationListSansParcel, AllEquations ),
        % We don't want equation of the form  "V = V":
        filter( non_trivial_eq, AllEquations, NontrivialEquations ),
        % Sort by variable name:
        sort( NontrivialEquations, SortedEquations ),
        std_output_stream( Output ),
        show_equations( SortedEquations, Output ),
        fail.              % We must undo all the bindings that we created here!

show_bindings( _ ).


%
swap_terms( [], [], [] ).

swap_terms( [ [ Name | _OldTerm ] | Pairs    ], [ NewTerm | NewTerms ],
            [ [ Name | NewTerm ]  | NewPairs ]
          ) :-
        swap_terms( Pairs, NewTerms, NewPairs ).


%
mk_eq( [ Name | Term ], Name = Term ).


%
non_trivial_eq( A = B ) :-  A \= B .


%
show_equations( Equations, Output ) :-
        member( Name = Term, Equations ),
        write( Output, Name ),
        write( Output, ' = ' ),
        write( Output, Term ),
        nl( Output ),
        fail.

show_equations( _, _ ).


%% check_not_builtin( + clause, + variable dictionary ):
%% Raise a fatal error if this clause attempts to redefine a built-in predicate.

check_not_builtin( Clause, VarDict ) :-
        get_clause_head( Clause, Head ),
        (
            lp_system( eclipse )
        ->
            builtin( Head )     % recall that in Eclipse we hid other built-ins
        ;
            is_builtin( Head )
        ),
        !,
        bind_variables_to_names( VarDict ),
        error( lines( [ 'An attempt to redefine a built-in predicate:',
                        [ Clause, '.' ]
                      ]
                    )
             ).

check_not_builtin( _, _ ).



%% top:
%% Interactive mode.  Each term that is not a directive or a query is treated
%% as an abbreviated query.  After displaying the results of each query read
%% characters upto the nearest newline: if the first character is ";",
%% backtrack to find alternative solutions.
%% Exit upon encountering end of file.
%% NOTE: When running on Sicstus, each term must come on a separate line: after
%%       reading the term the rest of the line is ignored, to facilitate
%%       interaction with the user when asking whether more answers are needed.

(top) :-
        std_input_stream( Input ),
        std_output_stream( Output ),
        repeat,
        (
            lp_system( eclipse )
        ->
            write( Output, ': ' )                    % a prompt
        ;
            true
        ),
        readvar( Input, Term, VarDict ),
        (
            lp_system( sicstus )
        ->
            getline( Input, _ )                      % skip the rest of the line
        ;
            true
        ),
        bare_to_query( Term, NTerm ),
        verify_program_item( NTerm, VarDict ),
        interactive_term( NTerm, VarDict ),
        ( NTerm = end_of_file ; NTerm = quit ),      % i.e., normally fails
        !.


%% bare_to_query( + term, - term ):
%% A term that is not end_of_file, quit, a directive, or a query is
%% translated to a query.  (So, for example, there will be no check for
%% singleton variables.)

bare_to_query( Term, Term ) :-
        (
            Term = end_of_file
        ;
            Term = quit
        ;
            Term = (:- _)
        ;
            Term = (?- _)
        ),
        !.

bare_to_query( Bare, (?- Bare) ).


%% interactive_term( + term, + variable dictionary ):
%% Process a term in interactive mode.
%% The variable dictionary is used for printing out the results of a query.

% :- mode interactive_term( +, + ).

interactive_term( end_of_file, _ ) :-  !.              % just ignore this

interactive_term( quit       , _ ) :-  !.              % just ignore this

interactive_term( (:- [ H | T ]), _ ) :-               % include
        !,
        include_files( [ H | T ] ).

interactive_term( (:- Directive), _ ) :-               % directive
        !,
        process_directive( Directive ).

interactive_term( (?- Query), VarDict ) :-             % query
        !,
        execute_query( Query, Result ),
        show_result( Result, VarDict ),
        satisfied_with_query( Result ),                % or backtrack to retry
        !.


%% satisfied_with_query( + answer ):
%% Give the user a chance to type ";" if the answer is "yes".

% :- mode satisfied_with_query( + ).

satisfied_with_query( yes ) :-
        std_output_stream( Output ),
        flush_output( Output ),
        user_accepts,
        !.

satisfied_with_query( no ) :-
        std_output_stream( Output ),
        nl( Output ),
        flush_output( Output ).


%% user_accepts:
%% Read input upto the nearest newline.
%% If the first character is a semicolon, fail.

user_accepts :-
        std_input_stream( Input ),
        std_output_stream( Output ),
        write( Output, '  (more?) ' ),
        flush_output( Output ),
        getline( Input, Line ),
        Line \= [ ';' | _ ].             % i.e., fail if 1st char is a semicolon

%-------------------------------------------------------------------------------
