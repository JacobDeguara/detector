-module(prop_add_rec).
-author("detectEr").
-generated("2024/ 3/28 20:05:18").
-export([mfa_spec/1]).
-import(proof_eval, [write_history/2,fix_trace/1,write_history/2]).
mfa_spec(_Mfa = {calc_server, loop, [_]}) ->
    {ok,
     begin
         Trace1 = [],
         FileName = "calc_server_History.txt",
         Proof_tree =
             {head,
              [{form,
                {'and',
                 [{nec,
                   "{trace,'_',init,'_',calc_server,loop,{'_',[],[]}}",
                   {max,
                    {var, 'X'},
                    {'and',
                     [{nec,
                       "{trace,'_','receive',{['_',add,'A'|'B'],[],[]}}",
                       {'and',
                        [{nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=/=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {ff}},
                         {nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=:=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {var, 'X'}}]}}]}}}]}},
               {form,
                {'and',
                 [{nec,
                   "{trace,'_',init,'_',calc_server_bug,loop,{'_',[],[]"
                   "}}",
                   {max,
                    {var, 'X'},
                    {'and',
                     [{nec,
                       "{trace,'_','receive',{['_',add,'A'|'B'],[],[]}}",
                       {'and',
                        [{nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=/=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {ff}},
                         {nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=:=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {var, 'X'}}]}}]}}}]}}]},
         io:format("\e[1m\e[33m*** [~w] Instrumenting monitor for MFA p"
                   "attern '~p'.~n\e[0m",
                   [self(), _Mfa]),
         fun(_E = {trace, _, spawned, _, {calc_server, loop, [_]}}) ->
                Trace2 =
                    lists:append(Trace1,
                                 ["{trace,'_',init,'_',calc_server,loop"
                                  ",{'_',[],[]}}"]),
                io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                          [self(), _E]),
                begin
                    Rec =
                        fun X(Trace3) ->
                                fun(_E =
                                        {trace, _, 'receive',
                                         {_, {add, A, B}}}) ->
                                       Trace4 =
                                           lists:append(Trace3,
                                                        ["{trace,'_','r"
                                                         "eceive',{['_'"
                                                         ",add,'A'|'B']"
                                                         ",[],[]}}"]),
                                       io:format("\e[37m*** [~w] Analyz"
                                                 "ing event ~p.~n\e[0m",
                                                 [self(), _E]),
                                       fun(_E =
                                               {trace, _, send,
                                                {ok, Res},
                                                _})
                                              when Res =/= A + B ->
                                              Trace5 =
                                                  lists:append(Trace4,
                                                               ["{trace"
                                                                ",'_',s"
                                                                "end,'_"
                                                                "',{[ok"
                                                                "|'Res'"
                                                                "],{'=/"
                                                                "=','Re"
                                                                "s',{'+"
                                                                "','A',"
                                                                "'B'}},"
                                                                "[]}}"]),
                                              io:format("\e[37m*** [~w]"
                                                        " Analyzing eve"
                                                        "nt ~p.~n\e[0m",
                                                        [self(), _E]),
                                              begin
                                                  io:format("\e[1m\e[31"
                                                            "m*** [~w] "
                                                            "<< Resulti"
                                                            "ng History"
                                                            " ~p >>~n\e"
                                                            "[0m",
                                                            [self(),
                                                             proof_eval:fix_trace(Trace5)]),
                                                  History =
                                                      proof_eval:write_history(proof_eval:fix_trace(Trace5),
                                                                               FileName),
                                                  io:format("\e[1m\e[31"
                                                            "m*** [~w] "
                                                            "Reached ve"
                                                            "rdict '~p'"
                                                            ".~n\e[0m",
                                                            [self(),
                                                             proof_eval:prove_property(Proof_tree,
                                                                                       History)])
                                              end;
                                          (_E =
                                               {trace, _, send,
                                                {ok, Res},
                                                _})
                                              when Res =:= A + B ->
                                              Trace5 =
                                                  lists:append(Trace4,
                                                               ["{trace"
                                                                ",'_',s"
                                                                "end,'_"
                                                                "',{[ok"
                                                                "|'Res'"
                                                                "],{'=:"
                                                                "=','Re"
                                                                "s',{'+"
                                                                "','A',"
                                                                "'B'}},"
                                                                "[]}}"]),
                                              io:format("\e[37m*** [~w]"
                                                        " Analyzing eve"
                                                        "nt ~p.~n\e[0m",
                                                        [self(), _E]),
                                              begin
                                                  io:format("\e[36m*** "
                                                            "[~w] Unfol"
                                                            "ding rec. "
                                                            "var. ~p.~n"
                                                            "\e[0m",
                                                            [self(),
                                                             'X']),
                                                  X(Trace5)
                                              end;
                                          (_E) ->
                                              begin
                                                  io:format("\e[1m\e[33"
                                                            "m*** [~w] "
                                                            "Reached ve"
                                                            "rdict 'end"
                                                            "' on event"
                                                            " ~p.~n\e[0"
                                                            "m",
                                                            [self(), _E]),
                                                  'end'
                                              end
                                       end;
                                   (_E) ->
                                       begin
                                           io:format("\e[1m\e[33m*** [~"
                                                     "w] Reached verdic"
                                                     "t 'end' on event "
                                                     "~p.~n\e[0m",
                                                     [self(), _E]),
                                           'end'
                                       end
                                end
                        end,
                    Rec(Trace2)
                end;
            (_E) ->
                begin
                    io:format("\e[1m\e[33m*** [~w] Reached verdict 'end"
                              "' on event ~p.~n\e[0m",
                              [self(), _E]),
                    'end'
                end
         end
     end};
mfa_spec(_Mfa = {calc_server_bug, loop, [_]}) ->
    {ok,
     begin
         Trace1 = [],
         FileName = "calc_server_bug_History.txt",
         Proof_tree =
             {head,
              [{form,
                {'and',
                 [{nec,
                   "{trace,'_',init,'_',calc_server,loop,{'_',[],[]}}",
                   {max,
                    {var, 'X'},
                    {'and',
                     [{nec,
                       "{trace,'_','receive',{['_',add,'A'|'B'],[],[]}}",
                       {'and',
                        [{nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=/=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {ff}},
                         {nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=:=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {var, 'X'}}]}}]}}}]}},
               {form,
                {'and',
                 [{nec,
                   "{trace,'_',init,'_',calc_server_bug,loop,{'_',[],[]"
                   "}}",
                   {max,
                    {var, 'X'},
                    {'and',
                     [{nec,
                       "{trace,'_','receive',{['_',add,'A'|'B'],[],[]}}",
                       {'and',
                        [{nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=/=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {ff}},
                         {nec,
                          "{trace,'_',send,'_',{[ok|'Res'],{'=:=','Res'"
                          ",{'+','A','B'}},[]}}",
                          {var, 'X'}}]}}]}}}]}}]},
         io:format("\e[1m\e[33m*** [~w] Instrumenting monitor for MFA p"
                   "attern '~p'.~n\e[0m",
                   [self(), _Mfa]),
         fun(_E = {trace, _, spawned, _, {calc_server_bug, loop, [_]}}) ->
                Trace2 =
                    lists:append(Trace1,
                                 ["{trace,'_',init,'_',calc_server_bug,"
                                  "loop,{'_',[],[]}}"]),
                io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                          [self(), _E]),
                begin
                    Rec =
                        fun X(Trace3) ->
                                fun(_E =
                                        {trace, _, 'receive',
                                         {_, {add, A, B}}}) ->
                                       Trace4 =
                                           lists:append(Trace3,
                                                        ["{trace,'_','r"
                                                         "eceive',{['_'"
                                                         ",add,'A'|'B']"
                                                         ",[],[]}}"]),
                                       io:format("\e[37m*** [~w] Analyz"
                                                 "ing event ~p.~n\e[0m",
                                                 [self(), _E]),
                                       fun(_E =
                                               {trace, _, send,
                                                {ok, Res},
                                                _})
                                              when Res =/= A + B ->
                                              Trace5 =
                                                  lists:append(Trace4,
                                                               ["{trace"
                                                                ",'_',s"
                                                                "end,'_"
                                                                "',{[ok"
                                                                "|'Res'"
                                                                "],{'=/"
                                                                "=','Re"
                                                                "s',{'+"
                                                                "','A',"
                                                                "'B'}},"
                                                                "[]}}"]),
                                              io:format("\e[37m*** [~w]"
                                                        " Analyzing eve"
                                                        "nt ~p.~n\e[0m",
                                                        [self(), _E]),
                                              begin
                                                  io:format("\e[1m\e[31"
                                                            "m*** [~w] "
                                                            "<< Resulti"
                                                            "ng History"
                                                            " ~p >>~n\e"
                                                            "[0m",
                                                            [self(),
                                                             proof_eval:fix_trace(Trace5)]),
                                                  History =
                                                      proof_eval:write_history(proof_eval:fix_trace(Trace5),
                                                                               FileName),
                                                  io:format("\e[1m\e[31"
                                                            "m*** [~w] "
                                                            "Reached ve"
                                                            "rdict '~p'"
                                                            ".~n\e[0m",
                                                            [self(),
                                                             proof_eval:prove_property(Proof_tree,
                                                                                       History)])
                                              end;
                                          (_E =
                                               {trace, _, send,
                                                {ok, Res},
                                                _})
                                              when Res =:= A + B ->
                                              Trace5 =
                                                  lists:append(Trace4,
                                                               ["{trace"
                                                                ",'_',s"
                                                                "end,'_"
                                                                "',{[ok"
                                                                "|'Res'"
                                                                "],{'=:"
                                                                "=','Re"
                                                                "s',{'+"
                                                                "','A',"
                                                                "'B'}},"
                                                                "[]}}"]),
                                              io:format("\e[37m*** [~w]"
                                                        " Analyzing eve"
                                                        "nt ~p.~n\e[0m",
                                                        [self(), _E]),
                                              begin
                                                  io:format("\e[36m*** "
                                                            "[~w] Unfol"
                                                            "ding rec. "
                                                            "var. ~p.~n"
                                                            "\e[0m",
                                                            [self(),
                                                             'X']),
                                                  X(Trace5)
                                              end;
                                          (_E) ->
                                              begin
                                                  io:format("\e[1m\e[33"
                                                            "m*** [~w] "
                                                            "Reached ve"
                                                            "rdict 'end"
                                                            "' on event"
                                                            " ~p.~n\e[0"
                                                            "m",
                                                            [self(), _E]),
                                                  'end'
                                              end
                                       end;
                                   (_E) ->
                                       begin
                                           io:format("\e[1m\e[33m*** [~"
                                                     "w] Reached verdic"
                                                     "t 'end' on event "
                                                     "~p.~n\e[0m",
                                                     [self(), _E]),
                                           'end'
                                       end
                                end
                        end,
                    Rec(Trace2)
                end;
            (_E) ->
                begin
                    io:format("\e[1m\e[33m*** [~w] Reached verdict 'end"
                              "' on event ~p.~n\e[0m",
                              [self(), _E]),
                    'end'
                end
         end
     end};
mfa_spec(_Mfa) ->
    io:format("\e[1m\e[31m*** [~w] Skipping instrumentation for MFA pat"
              "tern '~p'.~n\e[0m",
              [self(), _Mfa]),
    undefined.
