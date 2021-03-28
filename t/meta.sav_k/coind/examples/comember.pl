%% COINDUCTIVE PREDICATES:
%%   stream/1
%%   append1/3
%%   member1/2
%%   comember/2
%% "SUPPORT" PREDICATES:
%%   num/1
%%   drop/3

comember(_G4173, _G4174):-comember_(_G4173, _G4174, []).

num(0).
num(s(_G381)):-num(_G381).
stream_(_G2081, _G2134):-member(stream(_G2081), _G2134).
stream_([_G446|_G447], _G2204):-_G2271=[stream([_G446|_G447])|_G2204], num(_G446), stream_(_G447, _G2271).
append1_(_G2311, _G2312, _G2313, _G2378):-member(append1(_G2311, _G2312, _G2313), _G2378).
append1_([], _G545, _G545, _G2468).
append1_([_G586|_G587], _G593, [_G586|_G590], _G2555):-_G2639=[append1([_G586|_G587], _G593, [_G586|_G590])|_G2555], append1_(_G587, _G593, _G590, _G2639).
member1_(_G2686, _G2687, _G2749):-member(member1(_G2686, _G2687), _G2749).
member1_(_G740, [_G740|_G741], _G2832).
member1_(_G787, [_G784|_G785], _G2912):-_G2989=[member1(_G787, [_G784|_G785])|_G2912], member1_(_G787, _G785, _G2989).
member2_(_G861, [_G861|_G862], _G3086).
member2_(_G908, [_G905|_G906], _G3169):-member2_(_G908, _G906, _G3169).
drop(_G982, [_G982|_G983], _G983).
drop(_G1057, [_G1054|_G1055], _G1059):-drop(_G1057, _G1055, _G1059).
comember_(_G3292, _G3293, _G3361):-member(comember(_G3292, _G3293), _G3361).
comember_(_G1178, _G1179, _G3450):-_G3536=[comember(_G1178, _G1179)|_G3450], drop(_G1178, _G1179, _G1183), comember_(_G1178, _G1183, _G3536).
?- write('Query1'), nl, _G1303=[0, s(0), s(s(0))], member2_(s(0), _G1303, []), write('Yes1 !'), nl.
?- write('Query2'), nl, _G1385=[0, s(0), s(s(0))], member1_(s(0), _G1385, []), write('Yes2 !'), nl.
?- write('Query3'), nl, _G1467=[0, s(0), s(s(0))], comember_(s(0), _G1467, []), write('WHAT? SHOULD HAVE FAILED !'), nl.
?- write('Query4'), nl, _G1547=[0, s(0), s(s(0))|_G1547], once(comember_(s(0), _G1547, [])), write('Yes4 !'), nl, write_term(_G1547, [max_depth(10)]), nl.
