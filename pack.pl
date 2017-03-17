name(pfc).
title('Pfc -- a package for forward chaining in Prolog').
version('1.1.115').
download('https://github.com/TeamSPoon/pfc/releases/*.zip').
author( 'Douglas R. Miles', 'logicmoo@gmail.com' ).
packager( 'TeamSPoon/LogicMoo', 'https://github.com/TeamSPoon/' ).
home('https://github.com/TeamSPoon/pfc').
requires(hook_hybrid).
requires(must_trace).
requires(loop_check).
requires(file_scope).
requires(xlisting).
requires(no_repeats).
requires(each_call_cleanup).
requires(with_thread_local).
requires(logicmoo_utils).
autoload(false).

