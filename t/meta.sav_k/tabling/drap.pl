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

%% This is the shell for SWI Prolog.  See dra_common.pl for documentation.

:- module( drap,
           [ prog/1, top/0,
             op( 1010, fy, coinductive  ),    % allow  ":- coinductive p/k ."
             op( 1010, fy, coinductive1 ),    % allow  ":- coinductive1 p/k ."
             op( 1010, fy, tabled       ),    % allow  ":- tabled p/k ."
             op( 1010, fy, old_first    ),    % allow  ":- old_first p/k ."
             op( 1010, fy, trace        ),    % allow  ":- trace  p/k ."
             op( 1010, fy, multifile    ),    % allow  ":- multifile  p/k ."
             op( 1010, fy, top          ),    % allow  ":- top p/k ."
             op( 1010, fy, support      ),    % allow  ":- support p/k ."
             op( 1010, fy, load_support )     % allow  ":- load_support filename
           ]
         ).

:- ensure_loaded( '../general/compatibility_utilities_swi' ).
:- ensure_loaded( dra_table_record ).    % OK for cyclic terms
:- ensure_loaded( dra_common ).
