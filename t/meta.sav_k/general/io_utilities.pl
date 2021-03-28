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

%%%  Utilities that have to do with input and output.                        %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (January 2009).                       %%%
%%%                                                                          %%%
%%%  Last update: 12 June 2009.                                              %%%
%%%                                                                          %%%


%% NOTE: requires proper compatibility_utilities_....


%%------------------------------------------------------------------------------
%% ensure_filename_is_an_atom( + filename ):
%% Verify that the filename is an atom.  If not, produce a fatal error.

ensure_filename_is_an_atom( FileName ) :-
        atom( FileName ),
        !.

ensure_filename_is_an_atom( FileName ) :-
        % \+ atom( FileName ),
        error( [ 'Illegal file name \"', FileName, '\" (not an atom).' ]
             ).



%%------------------------------------------------------------------------------
%% ensure_extension( + file name chars,
%%                   + extension chars,
%%                   - the root file name,
%%                   - file name, possibly extended
%%                 ):
%% If the file name has no extension, add the provided extension (which must
%% include the period; it can also be empty) and return the file name as the
%% root name; if the file name has an extension, don't change it, but extract
%% the root name.

% :- mode ensure_extension( +, +, -, - ).

ensure_extension( FileNameChars, _, RootFileNameChars, FileNameChars ) :-
        name_chars( '.', [ Dot ] ),
        append( RootFileNameChars, [ Dot | _ ], FileNameChars ), % has extension
        !.

ensure_extension( FileNameChars, ExtChars,
                  FileNameChars, FullFileNameChars
                ) :-
        append( FileNameChars, ExtChars, FullFileNameChars ).



%%------------------------------------------------------------------------------
%% read_terms_with_vars( + input stream,
%%                       - list of terms with variable dictionaries
%%                     ):
%% Like read_terms/2 (see below), but each item on the resulting list is of
%% the form "pair( term, variable dictionary )", where the variable dictionary
%% is of the format returned by readvar.

% :- mode read_terms_with_vars( +, - ).

read_terms_with_vars( InputStream, Terms ) :-
        readvar( InputStream, Term, VarDict ),
        read_terms_with_vars_( InputStream, pair( Term, VarDict ), Terms ).

%
read_terms_with_vars_( _, pair( end_of_file, _ ), [] ) :-
        !.

read_terms_with_vars_( InputStream, Pair, [ Pair | Pairs ] ) :-
        % Pair \= pair( end_of_file, _ ),
        process_if_op_directive( Pair ),
        readvar( InputStream, NextTerm, NextVarDict ),
        read_terms_with_vars_( InputStream,
                               pair( NextTerm, NextVarDict ), Pairs
                             ).

%
process_if_op_directive( pair( (:- op( P, F, Ops)), _ ) ) :-
        !,
        op( P, F, Ops ).

process_if_op_directive( _ ).


%%------------------------------------------------------------------------------
%% read_terms( + input stream, - list of terms ):
%% Given an open input stream, produce all the terms that can be read from it.
%%
%% NOTE: Operator declarations are interpreted on the fly, but not deleted from
%%       output.
%%       See also read_terms_with_vars/2 above.

% :- mode read_terms( +, - ).

read_terms( InputStream, Terms ) :-
        read( InputStream, Term ),
        read_terms_( InputStream, Term, Terms ).

%
read_terms_( _, end_of_file, [] ) :-
        !.

read_terms_( InputStream, Term, [ Term | Terms ] ) :-
        % term \= end_of_file,
        process_if_op_directive( Term ),
        read( InputStream, NextTerm ),
        read_terms_( InputStream, NextTerm, Terms ).



%%------------------------------------------------------------------------------
%% write_terms( + list of terms, + output stream ):
%% Given an open output stream, write onto it all the terms from the list,
%% one per line but without any other pretty-printing.

% :- mode write_terms( +, + ).

write_terms( Terms, OutputStream ) :-
        member( Term, Terms ),
        write( OutputStream, Term ),
        writeln( OutputStream, '.' ),
        fail.

write_terms( _, _ ).


%%------------------------------------------------------------------------------
%% write_clauses( + list of clauses, + output stream ):
%% Given an open output stream, write onto it all the clauses from the list.

% :- mode write_clauses( +, + ).

write_clauses( Clauses, OutputStream ) :-
        member( Clause, Clauses ),
        writeclause( OutputStream, Clause ),
        fail.

write_clauses( _, _ ).



%%------------------------------------------------------------------------------
%% write_list( +stream, +list ):
%% Output the items on this list to this stream.
%% There are no spaces between items on the list.
%% Strings are printed without quotes.

write_list( S, V ) :-
        var( V ),
        !,
        warning( [ 'Incorrect invocation of write_list/1: \"',
                   write_list( S, V ),
                   '\"'
                 ]
               ).

write_list( _S, [] ) :-
        !.

write_list( S, [ H | T ] ) :-
        !,
        write( S, H ),
        write_list( S, T ).

write_list( S, NotAList ) :-
        !,
        warning( [ 'Incorrect invocation of write_list/1: \"',
                   write_list( S, NotAList ),
                   '\"'
                 ]
               ).



%%------------------------------------------------------------------------------
%% getline( + input stream, - list of character atoms ) :
%%    Reads characters from this input stream upto (and including) the nearest
%%    newline.  The newline is not included in the list of characters that is
%%    returned.

% :- mode getline( +, - ).

getline( InputStream, Line ) :-
        getchar( InputStream, C ),
        getline_( InputStream, C, Line ).

%
% :- mode getline_( +, +, - ).

getline_( _InputStream, '\n', [] ) :-  !.

getline_( InputStream, C   , [ C | Cs ] ) :-
        getchar( InputStream, NC ),
        getline_( InputStream, NC, Cs ).


%%------------------------------------------------------------------------------
%% putline( + output stream, + list of character strings ) :
%%    Writes the characters to this stream and follows them with a newline.

% :- mode putline( +, + ).

putline( OutputStream, Cs ) :-
        putchars( OutputStream, Cs ),
        nl( OutputStream ).


%%------------------------------------------------------------------------------
%% putchars( + output stream, + list of character strings ) :
%%    Writes the characters to the current output stream.

% :- mode putchars( +, + ).

putchars( _OutputStream, [] ).

putchars( OutputStream, [ C | Cs ] ) :-
        put_char( OutputStream, C ),
        putchars( OutputStream, Cs ).

%%------------------------------------------------------------------------------
