%% COINDUCTIVE PREDICATES:
%%   coverify/3
%% "SUPPORT" PREDICATES:
%%   holds/2
%%   normalize/2
%%   proposition/1
%%   state/1
%%   trans/2
%%   looping_prefix/2
%%   automaton_error/0
%%   check_consistency/0
%%   append/3

check(_G6555, _G6556):-check_(_G6555, _G6556, []).

:- dynamic essence_hook/2.
essence_hook(tverify_(_G6555, _G6556, _G6557, _G6558), tverify_(_G6555, _G6556, _G6557)).
:- op(10, fy, ~).
:- op(20, xfy, ^).
:- op(30, xfy, v).
:- op(10, fy, x).
:- op(10, fy, f).
:- op(10, fy, g).
:- op(20, xfx, u).
:- op(20, xfx, r).
:- ['normalize.pl'].
:- ['looping_prefix.pl'].
:- ['consistency_checker.pl'].
check_(_G594, _G595, _G3428):-check_consistency, (state(_G594)->true;write('"'), write(_G594), write('" is not a state'), nl, fail), write('Query for state '), write(_G594), write(': '), write(_G595), nl, once(normalize(~_G595, _G634)), write('(Negated and normalized: '), write(_G634), write(')'), nl, (once(verify_(_G594, _G634, _G646, _G3428))->write('COUNTEREXAMPLE: '), looping_prefix(_G646, _G653), write(_G653), nl, fail;true).
verify_(_G862, g _G860, _G864, _G3848):-once(coverify_(_G862, g _G860, _G864, _G3848)).
verify_(_G972, _G969 r _G970, _G974, _G4024):-once(coverify_(_G972, _G969 r _G970, _G974, _G4024)).
verify_(_G1109, f _G1107, _G1111, _G4200):-tverify_(_G1109, f _G1107, _G1111, _G4200).
verify_(_G1217, _G1214 u _G1215, _G1219, _G4368):-tverify_(_G1217, _G1214 u _G1215, _G1219, _G4368).
verify_(_G1350, _G1354, [_G1350], _G4536):-proposition(_G1354), holds(_G1350, _G1354).
verify_(_G1435, ~_G1433, [_G1435], _G4623):-proposition(_G1433), \+holds(_G1435, _G1433).
verify_(_G1523, _G1520^_G1521, _G1525, _G4712):-verify_(_G1523, _G1520, _G1529, _G4712), verify_(_G1523, _G1521, _G1533, _G4712), (append(_G1529, _G1536, _G1533)->_G1525=_G1533;append(_G1533, _G1546, _G1529)->_G1525=_G1529).
verify_(_G1743, _G1740 v _G1741, _G1745, _G4985):-verify_(_G1743, _G1740, _G1745, _G4985);verify_(_G1743, _G1741, _G1745, _G4985).
verify_(_G1882, x _G1880, [_G1882|_G1883], _G5228):-trans(_G1882, _G1890), verify_(_G1890, _G1880, _G1883, _G5228).
%:- tabled tverify_/4.
tverify_(_G2041, f _G2039, _G2043, _G5463):-verify_(_G2041, _G2039, _G2043, _G5463);verify_(_G2041, x f _G2039, _G2043, _G5463).
tverify_(_G2158, _G2155 u _G2156, _G2160, _G5712):-verify_(_G2158, _G2156, _G2160, _G5712);verify_(_G2158, _G2155^x (_G2155 u _G2156), _G2160, _G5712).
coverify_(_G5907, _G5908, _G5909, _G5980):-member(coverify(_G5907, _G5908, _G5909), _G5980).
coverify_(_G2323, g _G2321, _G2325, _G6076):-_G6154=[coverify(_G2323, g _G2321, _G2325)|_G6076], verify_(_G2323, _G2321^x g _G2321, _G2325, _G6154).
coverify_(_G2436, _G2433 r _G2434, _G2438, _G6259):-_G6337=[coverify(_G2436, _G2433 r _G2434, _G2438)|_G6259], verify_(_G2436, _G2433^_G2434, _G2438, _G6337).
coverify_(_G2572, _G2569 r _G2570, _G2574, _G6442):-_G6520=[coverify(_G2572, _G2569 r _G2570, _G2574)|_G6442], verify_(_G2572, _G2570^x (_G2569 r _G2570), _G2574, _G6520).
