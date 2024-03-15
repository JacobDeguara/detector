
-module(client_system).
-author("Jacob Deguara").

%%% Public API.

-export([rpc/2]).


%%% ----------------------------------------------------------------------------
%%% Public API.
%%% ----------------------------------------------------------------------------

-spec rpc(To :: pid() | atom(), Req :: any()) -> any().
rpc(To, Req) ->
  To ! {self(), Req},
  receive
    Resp ->
      Resp
  end.