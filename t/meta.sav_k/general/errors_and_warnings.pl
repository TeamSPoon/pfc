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

%%%  Utilities for producing warning and error messages.                     %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (January 2009).                       %%%
%%%                                                                          %%%
%%%  Last update: 2 March 2009.                                              %%%
%%%                                                                          %%%


%%------------------------------------------------------------------------------
%% warning( + term ):
%% warning( + list of terms ):
%% Print this term or list of terms as a warning.
%% There are no spaces between items on the list.
%% Strings are printed without quotes.
%% NOTE: If the term is "lines/1", then the argument should be a non-empty list.
%%       Each of the top level items on the list is printed in a separate line.

warning( V ) :-
        var( V ),
        !,
        warning( [ 'Incorrect invocation of warning/1: \"',
                   warning( V ),
                   '\"'
                 ]
               ).

warning( [] ) :-
        !,
        begin_warning,
        end_warning.

warning( [ A | B ] ) :-
        !,
        std_warning_stream( WS ),
        begin_warning,
        write_list( WS, [ A | B ] ),
        write( WS, ' ' ),
        end_warning.

warning( lines( [ FirstLine | OtherLines ]  ) ) :-
        !,
        begin_warning,
        std_warning_stream( WS ),
        warning_line( WS, FirstLine ),
        warning_lines( OtherLines, WS ),
        end_warning.

warning( NotAList ) :-
        begin_warning,
        std_warning_stream( WS ),
        write( WS, NotAList ),
        write( WS, ' ' ),
        end_warning.

%
warning_lines( [], _ ).

warning_lines( [ Line | Lines ], WS ) :-
        write( WS, '---          ' ),
        warning_line( WS, Line ),
        warning_lines( Lines, WS ).

%
warning_line( WS, List ) :-
        ( List = [] ; List = [ _ | _ ] ),
        !,
        write_list( WS, List ),
        nl( WS ).

warning_line( WS, Term ) :-
        writeln( WS, Term ).


%%------------------------------------------------------------------------------
%% begin_warning:
%% Begin a warning printout.

begin_warning :-
        std_warning_stream( WS ),
        write( WS, '--- WARNING: ' ).


%%------------------------------------------------------------------------------
%% end_warning:
%% End a warning printout.

end_warning :-
        std_warning_stream( WS ),
        writeln( WS, '---' ).



%%------------------------------------------------------------------------------
%% error( + term ):
%% error( + list of terms ):
%% Print this term or list of terms as an error, then abort the computation.
%% There are no spaces between items on the list.
%% Strings are printed without quotes.
%% NOTE: If the term is "lines/1", then the argument should be a non-empty list.
%%       Each of the top level items on the list is printed in a separate line.

error( V ) :-
        var( V ),
        !,
        error( [ 'Incorrect invocation of error/1: \"', error( V ), '\"' ] ).

error( [] ) :-
        !,
        begin_error,
        end_error.

error( [ A | B ] ) :-
        !,
        begin_error,
        std_error_stream( ES ),
        write_list( ES, [ A | B ] ),
        write( ES, ' ' ),
        end_error.

error( lines( [ FirstLine | OtherLines ]  ) ) :-
        !,
        begin_error,
        std_error_stream( ES ),
        error_line( ES, FirstLine ),
        error_lines( OtherLines, ES ),
        end_error.

error( NotAList ) :-
        begin_error,
        std_error_stream( ES ),
        write( ES, NotAList ),
        write( ES, ' ' ),
        end_error.

%
error_lines( [], _ ).

error_lines( [ Line | Lines ], ES ) :-
        write( ES, '***        ' ),
        error_line( ES, Line ),
        error_lines( Lines, ES ).

%
error_line( ES, List ) :-
        ( List = [] ; List = [ _ | _ ] ),
        !,
        write_list( ES, List ),
        nl( ES ).

error_line( ES, Term ) :-
        writeln( ES, Term ).



%%------------------------------------------------------------------------------
%% begin_error:
%% Begin an error printout.

begin_error :-
        std_error_stream( ES ),
        write( ES, '*** ERROR: ' ).


%%------------------------------------------------------------------------------
%% end_error:
%% End an error printout.

end_error :-
        std_error_stream( ES ),
        writeln( ES, '***' ),
        abort.

%%------------------------------------------------------------------------------
