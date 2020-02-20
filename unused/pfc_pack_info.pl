
:- if((
   prolog_source_context(source,File),
   ( \+ current_predicate(pfc_file_info/1); \+ pfc_file_info(File)),
   asserta(pfc_file_info(File)))).

:- pfc_file_info(File),!,stream_property(In,file(File)),
         repeat,
            fill_buffer(In),
            read_pending_codes(In, Chars, Tail),
            \+ \+ ( Tail = [],
                    nop(format(Out, '~s', [Chars])),
                    nop(flush_output(Out))
                  ),
            (   Tail == []
            ->  !
            ;   fail
            ).


:- endif.

