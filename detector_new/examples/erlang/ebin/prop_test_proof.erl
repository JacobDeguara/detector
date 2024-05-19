-module(prop_test_proof).

-author("detectEr").

-generated("2024/ 5/18 18:20:07").

-export([mfa_spec/1]).

-import(proof_eval, [write_history/2]).

mfa_spec(_Mfa = {system, start, [_]}) ->
    {ok,
     begin
         Trace1 = [],
         FileName = "system_history.txt",
         Proof_tree =
             [{form,
               ignore,
               ignore,
               {nec,
                ignore,
                "{trace,'_',init,'_',system,start,{'_',[]}}",
                {rec,
                 ignore,
                 {var, ignore, 'X'},
                 {'and',
                  ignore,
                  {nec,
                   ignore,
                   "{trace,'_','receive',{r,[]}}",
                   {nec, ignore, "{trace,'_',send,'_',{s,[]}}", {var, ignore, 'X'}}},
                  {'or',
                   ignore,
                   {nec,
                    ignore,
                    "{trace,'_',send,'_',{a,[]}}",
                    {'and',
                     ignore,
                     {var, ignore, 'X'},
                     {nec, ignore, "{trace,'_','receive',{d,[]}}", {no, ignore}}}},
                   {nec, ignore, "{trace,'_',send,'_',{c,[]}}", {no, ignore}}}}}}}],
         io:format("\e[1m\e[33m*** [~w] Instrumenting monitor for MFA pattern '~p'.~n\e[0m",
                   [self(), _Mfa]),
         fun (_E = {trace, _, spawned, _, {system, start, [_]}}) ->
                 Trace2 = lists:append(Trace1, ["{trace,'_',init,'_',system,start,{'_',[]}}"]),
                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m", [self(), _E]),
                 fun X(Trace3) ->
                         fun (_E = {trace, _, send, {c}, _}) ->
                                 Trace4 = lists:append(Trace3, ["{trace,'_',send,'_',{c,[]}}"]),
                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                           [self(), _E]),
                                 begin
                                     History = proof_eval:write_history(Trace4, FileName),
                                     io:format("\e[1m\e[33m*** [~w] << Resulting History ~p >>~n\e[0m",
                                               [self(), History]),
                                     io:format("\e[1m\e[31m*** [~w] Reached verdict '~p'.~n\e[0m",
                                               [self(),
                                                proof_eval:prove_property(Proof_tree, History)])
                                 end;
                             (_E = {trace, _, send, {a}, _}) ->
                                 Trace4 = lists:append(Trace3, ["{trace,'_',send,'_',{a,[]}}"]),
                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                           [self(), _E]),
                                 begin
                                     io:format("\e[36m*** [~w] Unfolding rec. var. ~p.~n\e[0m",
                                               [self(), 'X']),
                                     X(Trace4)
                                 end;
                             (_E = {trace, _, 'receive', {r}}) ->
                                 Trace4 = lists:append(Trace3, ["{trace,'_','receive',{r,[]}}"]),
                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                           [self(), _E]),
                                 fun (_E = {trace, _, send, {s}, _}) ->
                                         Trace5 =
                                             lists:append(Trace4, ["{trace,'_',send,'_',{s,[]}}"]),
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         begin
                                             io:format("\e[36m*** [~w] Unfolding rec. var. ~p.~n\e[0m",
                                                       [self(), 'X']),
                                             X(Trace5)
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
