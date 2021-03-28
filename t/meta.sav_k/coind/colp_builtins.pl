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

%%%%%  Built-in predicates for the "colp" interpreter.  %%%%

%%% If the interpreted program invokes a built-in predicate, that predicate must
%%% be declared in the table "builtin/1" below.
%%% Every addition should be considered carefully: some built-ins might require
%%% special treatment by the interpreter.

%%  NOTE: Just adding "!" won't do the trick, the main interpreter would
%%        have to be modified substantially.

builtin( true               ).
builtin( false              ).
builtin( fail               ).
builtin( _ = _              ).
builtin( _ \= _             ).
builtin( \+( _ )            ).
builtin( once( _ )          ).   % special treatment in solve/2
builtin( (_ ->_ ; _)        ).   % special treatment in solve/2
builtin( (_ ; _)            ).   % special treatment in solve/2
builtin( (_ , _)            ).   % special treatment in solve/2
builtin( writeln( _ )       ).
builtin( write( _ )         ).
builtin( write_term( _, _ ) ).
builtin( nl                 ).
builtin( set_print_depth( _, _ ) ).     % not a real built-in, see "top_level"

