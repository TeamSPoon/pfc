%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                    %
%  A general checker for Prolog programs.                            %
%                                                                    %
%  To use, call check_file( file name ).                             %
%                                                                    %
%  This wrapper, written by Abramo Bagnara in early June 2010, uses  %
%  clause_verification.pl to perform the checking.                   %
%                                                                    %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Lightly reformatted, commented and simplified by F.K.

%% This program could be improved to take into account modules and inclusion of
%% files.  DCGs are not properly checked, either.

:-  ensure_loaded( compatibility_utilities_swi ).
:-  ensure_loaded( clause_verification ).


%% Convert the variable dictionary from SWI format to SICStus format.

convert_vars( [], [] ).

convert_vars( [ Name = Var | T ], [ [ Name | Var ] | T1 ] ) :-
        convert_vars( T, T1 ).


%% Read a list of terms from this stream.

read_terms_from_stream( Stream, Terms ) :-
        read_term( Stream, Term, [ variable_names( Vars ) ] ),
        convert_vars( Vars, Vars1 ),
        (
            Term == end_of_file
        ->
            Terms = []
        ;
            Terms = [ pair( Term, Vars1 ) | Rest ],
            read_terms_from_stream( Stream, Rest )
        ).


%% Open and read a file of terms, check whether they are OK.

verify( File ) :-
        open( File, read, In ),
        read_terms_from_stream( In, Terms ),
        close( In ),
        verify_program_with_vars( Terms ).

%-------------------------------------------------------------------------------


