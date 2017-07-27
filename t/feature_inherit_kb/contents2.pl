%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% FLUX State Exporter
:- module('microtheoryAboutFn(meredithMcGhan)',[fluents_for_mt/1]).
:- include('/var/lib/myfrdcsa/codebases/minor/free-life-planner/data-git/systems/planning/state-exporter').
%% :- flp_include('/var/lib/myfrdcsa/codebases/minor/free-life-planner/data-git/systems/planning/state-exporter').
fluents_for_mt(AllAssertedKnowledge) :-
	pred_for_m('microtheoryAboutFn(meredithMcGhan)',AllAssertedKnowledge).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

loves(andrewDougherty,meredithMcGhan).
