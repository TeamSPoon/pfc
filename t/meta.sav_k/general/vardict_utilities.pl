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

%%%  Utilities that have to do with variable dictionaries.                   %%%
%%%                                                                          %%%
%%%  Written by Feliks Kluzniak at UTD (January 2009).                       %%%
%%%                                                                          %%%
%%%  Last update: 2 April 2009.                                              %%%
%%%                                                                          %%%


:- ensure_loaded( higher_order ).



%%------------------------------------------------------------------------------
%% expand_variable_dictionary( + term,
%%                             + variable dictionary,
%%                             - variable dictionary expanded as needed
%%                           ):
%% The variable dictionary is for the term in the form it was read in, but the
%% term may have been expanded (in particular: it may have been a DCG rule).
%% Make sure that all the variables are present in the dictionary.

expand_variable_dictionary( ExpandedTerm, VarDict, ExpandedVarDict ) :-
        ordered_term_variables( ExpandedTerm, Vars ),
        retain_new_variables( Vars, VarDict, RetainedVars ),
        mk_variable_dictionary( RetainedVars, NewVarDict ),
        append( NewVarDict, VarDict, ExpandedVarDict ).

%
retain_new_variables( [], _, [] ).

retain_new_variables( [ V | Vs ], VarDict, Retained ) :-
        in_vardict( V, VarDict ),
        !,
        retain_new_variables( Vs, VarDict, Retained ).

retain_new_variables( [ V | Vs ], VarDict, [ V | OtherRetained ] ) :-
        \+ in_vardict( V, VarDict ),
        !,
        retain_new_variables( Vs, VarDict, OtherRetained ).

%
in_vardict( V, [ [ _ | V2 ] | _ ] ) :-
        V == V2,
        !.

in_vardict( V, [ _ | RestOfVarDict ] ) :-
        in_vardict( V, RestOfVarDict ).


%%------------------------------------------------------------------------------
%% extract_vars_from_dict( + variable dictionary, - list of variables ) :
%% Produce a list of the (current instantiations of) the variables that
%% occur in this dictionary.

extract_vars_from_dict( VarDict, Vars ) :-
        map( drop_name, VarDict, Vars ).

%
drop_name( [ _Name | Var ], Var ).


%%------------------------------------------------------------------------------
%% bind_all_variables_to_names( +- term, +- variable dictionary  ):
%% Make sure that all the variables in this term are instantiated to their
%% names. This is not quite the same as bind_variables_to_names/1 (see below),
%% because variables that were originally represented by underscores do not find
%% their way into the variable dictionary.

bind_all_variables_to_names( Term, VarDict ) :-
        bind_variables_to_names( VarDict ),
        ordered_term_variables( Term, AnonymousVars ),
        bind_anonymous( AnonymousVars ).

%
bind_anonymous( [] ).

bind_anonymous( [ '_' | Vs ] ) :-
        bind_anonymous( Vs ).



%%------------------------------------------------------------------------------
%% bind_variables_to_names( +- variable dictionary  ):
%% The variable dictionary is of the format returned by readvar/3, i.e., a list
%% of pairs of the form "[ name | variable ]".  Go through the dictionary,
%% binding each variable to the associated name.
%% NOTE: 1. The assumption is that none of the variables has been instantiated!
%%       2. See also bind_all_variables_to_names/2 above!

bind_variables_to_names( VarDict ) :-
        map( bind_var_to_name, VarDict, _ ).

%
bind_var_to_name( [ Name | Name ], _ ).



%%------------------------------------------------------------------------------
%% bind_free_variables_to_names( +- variable dictionary  ):
%% Like bind_variables_to_names/1, but done only for those items in the
%% dictionary that are still variables.

bind_free_variables_to_names( [] ).

bind_free_variables_to_names( [ [ Name | Var ] | RestOfVarDict ] ) :-
        ( Var = Name
        ; true
        ),
        !,
        bind_free_variables_to_names( RestOfVarDict ).



%%------------------------------------------------------------------------------
%% mk_variable_dictionary( + term, - a variable dictionary ):
%% Produce a variable dictionary for this term, as if it had been read by
%% readvar/3.
%% Since the original variable names are not available, we will use the names
%% _A, _B, _C, ... _Z, _V0, _V1 etc. (The underscore is added to avoid spurious
%% messages about singleton variables in case these names are used for output
%% that will subsequently be read by Prolog again.)
%%
%% (All this is done "by hand", since numbervars/3 are not very useful in
%% Eclipse: the writing predicates are not "aware" of '$VAR'(n).)

mk_variable_dictionary( T, VarDict ) :-
        ordered_term_variables( T, Vars ),
        mk_variable_dictionary_( Vars, '_A', VarDict ).

mk_variable_dictionary_( [], _, [] ).

mk_variable_dictionary_( [ V | Vs ], Name, [ [ Name | V ] | VarDict ] ) :-
        mk_next_name( Name, NextName ),
        mk_variable_dictionary_( Vs, NextName, VarDict ).

%
% Once we run out of letters, we will use V0, V1 etc.
%
mk_next_name( '_Z', '_V0' ) :-
        !.

mk_next_name( Name, Next ) :-
        name_chars( Name, [ U, C ] ),      % still in single letters?
        !,
        NC is C + 1,         % good for ASCII, might not work for some encodings
        name_chars( Next, [ U, NC ] ).

mk_next_name( Name, Next ) :-
        name_chars( Name, [ CodeOfUndercore, CodeOfV | DigitChars ] ),
        name_chars( Number, DigitChars ),
        NextNumber is Number + 1,                               % good for ASCII
        name_chars( NextNumber, NewDigitChars ),
        name_chars( Next, [ CodeOfUndercore, CodeOfV | NewDigitChars ] ).

%%------------------------------------------------------------------------------
