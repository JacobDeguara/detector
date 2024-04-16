-module(prop_server_system).

-author("detectEr").

-generated("2024/ 4/12 14:13:09").

-export([mfa_spec/1]).

-import(proof_eval, [write_history/2]).

mfa_spec(_Mfa = {server_system, loop, [_]}) ->
    {ok,
     begin
         Trace1 = [],
         FileName = "server_system_history.txt",
         Proof_tree =
             [{form,
               ignore,
               ignore,
               {nec,
                ignore,
                "{trace,'_',init,'_',server_system,loop,{'_',[],[]}}",
                {max,
                 ignore,
                 {var, ignore, 'X'},
                 {nec,
                  ignore,
                  "{trace,'_','receive',{['_',rec|'_'],[],[]}}",
                  {'and',
                   ignore,
                   {nec, ignore, "{trace,'_',send,'_',{[ok|msg],[],[]}}", {var, ignore, 'X'}},
                   {nec,
                    ignore,
                    "{trace,'_',send,'_',{[ok|special],[],[]}}",
                    {'or',
                     ignore,
                     {nec, ignore, "{trace,'_',send,'_',{[ok|alloc],[],[]}}", {ff, ignore}},
                     {nec,
                      ignore,
                      "{trace,'_',send,'_',{[ok|closing],[],[]}}",
                      {ff, ignore}}}}}}}}}],
         io:format("\e[1m\e[33m*** [~w] Instrumenting monitor for MFA pattern '~p'.~n\e[0m",
                   [self(), _Mfa]),
         fun (_E = {trace, _, spawned, _, {server_system, loop, [_]}}) ->
                 Trace2 =
                     lists:append(Trace1, ["{trace,'_',init,'_',server_system,loop,{'_',[],[]}}"]),
                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m", [self(), _E]),
                 fun X(Trace3) ->
                         fun (_E = {trace, _, 'receive', {_, {rec, _}}}) ->
                                 Trace4 =
                                     lists:append(Trace3,
                                                  ["{trace,'_','receive',{['_',rec|'_'],[],[]}}"]),
                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                           [self(), _E]),
                                 fun (_E = {trace, _, send, {ok, msg}, _}) ->
                                         Trace5 =
                                             lists:append(Trace4,
                                                          ["{trace,'_',send,'_',{[ok|msg],[],[]}}"]),
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         begin
                                             io:format("\e[36m*** [~w] Unfolding rec. var. ~p.~n\e[0m",
                                                       [self(), 'X']),
                                             X(Trace5)
                                         end;
                                     (_E = {trace, _, send, {ok, special}, _}) ->
                                         Trace5 =
                                             lists:append(Trace4,
                                                          ["{trace,'_',send,'_',{[ok|special],[],[]}}"]),
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         fun (_E = {trace, _, send, {ok, alloc}, _}) ->
                                                 Trace6 =
                                                     lists:append(Trace5,
                                                                  ["{trace,'_',send,'_',{[ok|alloc],[],[]}}"]),
                                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                           [self(), _E]),
                                                 begin
                                                     History =
                                                         proof_eval:write_history(Trace6, FileName),
                                                     io:format("\e[1m\e[33m*** [~w] << Resulting History ~p >>~n\e[0m",
                                                               [self(), History]),
                                                     io:format("\e[1m\e[31m*** [~w] Reached verdict '~p'.~n\e[0m",
                                                               [self(),
                                                                proof_eval:prove_property(Proof_tree,
                                                                                          History)])
                                                 end;
                                             (_E = {trace, _, send, {ok, closing}, _}) ->
                                                 Trace6 =
                                                     lists:append(Trace5,
                                                                  ["{trace,'_',send,'_',{[ok|closing],[],[]}}"]),
                                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                           [self(), _E]),
                                                 begin
                                                     History =
                                                         proof_eval:write_history(Trace6, FileName),
                                                     io:format("\e[1m\e[33m*** [~w] << Resulting History ~p >>~n\e[0m",
                                                               [self(), History]),
                                                     io:format("\e[1m\e[31m*** [~w] Reached verdict '~p'.~n\e[0m",
                                                               [self(),
                                                                proof_eval:prove_property(Proof_tree,
                                                                                          History)])
                                                 end;
                                             (_E) ->
                                                 begin
                                                     io:format("\e[1m\e[33m*** [~w] Reached verdict 'end' on event ~p.~n\e[0m",
                                                               [self(), _E]),
                                                     'end'
                                                 end
                                         end;
                                     (_E) ->
                                         begin
                                             io:format("\e[1m\e[33m*** [~w] Reached verdict 'end' on event ~p.~n\e[0m",
                                                       [self(), _E]),
                                             'end'
                                         end
                                 end;
                             (_E) ->
                                 begin
                                     io:format("\e[1m\e[33m*** [~w] Reached verdict 'end' on event ~p.~n\e[0m",
                                               [self(), _E]),
                                     'end'
                                 end
                         end
                 end(Trace2);
             (_E) ->
                 begin
                     io:format("\e[1m\e[33m*** [~w] Reached verdict 'end' on event ~p.~n\e[0m",
                               [self(), _E]),
                     'end'
                 end
         end
     end};
mfa_spec(_Mfa) ->
    io:format("\e[1m\e[31m*** [~w] Skipping instrumentation for MFA pattern "
              "'~p'.~n\e[0m",
              [self(), _Mfa]),
    undefined.
