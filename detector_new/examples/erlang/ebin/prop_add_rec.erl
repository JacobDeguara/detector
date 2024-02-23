-module(prop_add_rec).

-author("detectEr").

-generated("2024/ 2/16 15:03:00").

-export([mfa_spec/1]).

mfa_spec(_Mfa = {calc_server, loop, [_]}) ->
    {ok,
     begin
         io:format("\e[1m\e[33m*** [~w] Instrumenting monitor for MFA pattern '~p'.~n\e[0m",
                   [self(), _Mfa]),
         fun (_E = {trace, _, spawned, _, {calc_server, loop, [_]}}) ->
                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m", [self(), _E]),
                 fun X() ->
                         fun (_E = {trace, _, 'receive', {_, {add, A, B}}}) ->
                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                           [self(), _E]),
                                 fun (_E = {trace, _, send, {ok, Res}, _}) when Res =/= A + B ->
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         begin
                                             io:format("\e[1m\e[31m*** [~w] Reached verdict 'no'.~n\e[0m",
                                                       [self()]),
                                             no
                                         end;
                                     (_E = {trace, _, send, {ok, Res}, _}) when Res =:= A + B ->
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         begin
                                             io:format("\e[36m*** [~w] Unfolding rec. var. ~p.~n\e[0m",
                                                       [self(), 'X']),
                                             X()
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
                 end();
             (_E) ->
                 begin
                     io:format("\e[1m\e[33m*** [~w] Reached verdict 'end' on event ~p.~n\e[0m",
                               [self(), _E]),
                     'end'
                 end
         end
     end};
mfa_spec(_Mfa = {calc_server_bug, loop, [_]}) ->
    {ok,
     begin
         io:format("\e[1m\e[33m*** [~w] Instrumenting monitor for MFA pattern '~p'.~n\e[0m",
                   [self(), _Mfa]),
         fun (_E = {trace, _, spawned, _, {calc_server_bug, loop, [_]}}) ->
                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m", [self(), _E]),
                 fun X() ->
                         fun (_E = {trace, _, 'receive', {_, {add, A, B}}}) ->
                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                           [self(), _E]),
                                 fun (_E = {trace, _, send, {ok, Res}, _}) when Res =/= A + B ->
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         begin
                                             io:format("\e[1m\e[31m*** [~w] Reached verdict 'no'.~n\e[0m",
                                                       [self()]),
                                             no
                                         end;
                                     (_E = {trace, _, send, {ok, Res}, _}) when Res =:= A + B ->
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         begin
                                             io:format("\e[36m*** [~w] Unfolding rec. var. ~p.~n\e[0m",
                                                       [self(), 'X']),
                                             X()
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
                 end();
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
