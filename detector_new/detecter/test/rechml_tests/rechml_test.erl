-module(rechml_test).
-author("Jacob Deguara").

%%% Includes.
-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-export([gen_action_test/2]).
-export([does_nothing/1]).


-spec gen_action_test(Monitor_File :: file:filename(), Fun :: function()) -> ok.
gen_action_test(Monitor_File, Fun) ->
    try gen_eval:parse_file(rechml_lexer, rechml_parser, Monitor_File) of
        {ok, AstP} ->
            gen_action_form(AstP, Fun);
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    catch
        _:Reason:Stk ->
            erlang:raise(error, Reason, Stk)
    end.

gen_action_form([], _) ->
    ok;
gen_action_form([{form, _, _, Shml} | Forms], Fun) ->
    gen_action(Shml, Fun),
    gen_action_form(Forms, Fun).

gen_action({no, _}, _) ->
    ok;
gen_action({undefined, _}, _) ->
    ok;
gen_action({var, _, _}, _) ->
    ok;
gen_action({rec, _, _, Shml}, Fun) ->
    gen_action(Shml, Fun);
gen_action({'and', _, Shml1, Shml2}, Fun) ->
    gen_action(Shml1, Fun),
    gen_action(Shml2, Fun);
gen_action({'or', _, Shml1, Shml2}, Fun) ->
    gen_action(Shml1, Fun),
    gen_action(Shml2, Fun);
gen_action({nec, _, Act, Shml}, Fun) ->
    io:format("~s~n",
              [lists:flatten(io_lib:format("~p", [Fun(Act)]))]),
    gen_action(Shml, Fun).

does_nothing(Something) ->
    Something.


-spec start() -> pid().
start() ->
    spawn(?MODULE, loop, []).

-spec loop() -> no_return().
loop() ->
    receive
        {'end'} ->
            ok;
        {_} ->
            loop()
    end.
