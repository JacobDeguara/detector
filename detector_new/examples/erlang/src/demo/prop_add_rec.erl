-module(prop_add_rec).

-author("detectEr").

-generated("2024/ 2/23 15:57:49").

-export([mfa_spec/1, setup/1]).
-export([record/1]).

-spec setup(List :: list()) -> pid().
setup(List) ->
    spawn(?MODULE, record, List).

writeToFile(Data) ->
    {ok, FileBinary} = file:read_file("Newfile.txt"),
    {ok, Fd} = file:open("Newfile.txt", [append]),
    FileContent = erlang:binary_to_list(FileBinary),
    if FileContent =:= [] ->
           file:write(Fd, [Data]);
       true ->
           file:write(Fd, [lists:append(["\n", Data])])
    end,
    file:close(Fd).

-spec record(List :: list()) -> no_return().
record(List) ->
    receive
        {Record} ->
            record(lists:append([List, ";", Record]));
        {_, stp} ->
            io:format("\n< ~p >\n", [List]),
            writeToFile(List)
    end.

mfa_spec(_Mfa = {calc_server_bug, loop, [_]}) ->
    {ok,
     begin
         TraceRecorder = setup(["[_ <- _, calc_server:loop(_)]"]),
         io:format("\e[1m\e[33m*** [~w] Instrumenting monitor for MFA pattern '~p'.~n\e[0m",
                   [self(), _Mfa]),
         fun (_E = {trace, _, spawned, _, {calc_server_bug, loop, [_]}}) ->
                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m", [self(), _E]),
                 fun X() ->
                         fun (_E = {trace, _, 'receive', {_, {add, A, B}}}) ->
                                 TraceRecorder ! {"[_ ? {_, {add, A, B}}]"},
                                 io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                           [self(), _E]),
                                 fun (_E = {trace, _, send, {ok, Res}, _}) when Res =/= A + B ->
                                         TraceRecorder ! {"[_:_ ! {ok, Res} when Res =/= A + B]"},
                                         io:format("\e[37m*** [~w] Analyzing event ~p.~n\e[0m",
                                                   [self(), _E]),
                                         begin
                                             TraceRecorder ! {self(), stp},
                                             io:format("\e[1m\e[31m*** [~w] Reached verdict 'no'.~n\e[0m",
                                                       [self()]),
                                             no
                                         end;
                                     (_E = {trace, _, send, {ok, Res}, _}) when Res =:= A + B ->
                                         TraceRecorder ! {"[_:_ ! {ok, Res} when Res =:= A + B]"},
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
