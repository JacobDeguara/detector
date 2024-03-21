-module(server_system).

-author("Jacob Deguara").

%%% Includes.
-include_lib("stdlib/include/assert.hrl").

%%% Public API.
-export([start/1]).
%%% Internal callbacks.
-export([loop/1]).

%%% ----------------------------------------------------------------------------
%%% Public API.
%%% ----------------------------------------------------------------------------

-spec start(N :: integer()) -> pid().
start(N) ->
    spawn(?MODULE, loop, [N]).

%%% ----------------------------------------------------------------------------
%%% Internal callbacks.
%%% ----------------------------------------------------------------------------

-spec loop(N :: integer()) -> no_return().
loop(N) ->
    receive
        {Clt, {rec, _ActType = {req}}} ->
            Clt ! {ok, req},
            loop(N);
        {Clt, {rec, _ActType = {msg}}} ->
            Clt ! {ok, msg},
            loop(N);
        {Clt, {rec, _ActType = {alloc}}} ->
            Clt ! {ok, alloc},
            loop(N);
        {Clt, {rec, _ActType = {close}}} ->
            Clt ! {ok, closing}
    end.
