-module(rechml_unit_test).

-include_lib("eunit/include/eunit.hrl").

% Import the module to be tested
-export([run_tests/0]).
-export([removes_whitespace/1]).
-export([gen_action_test_cal/0]).
-export([start/0]).
-export([loop/0]).

-import(rechml_eval, [parse_file/1]).
-import(proof_eval, [prove_property/2, get_action/1, read_history/1]).

-define(small_wait, timer:sleep(800)).

% setting up elements
get_monitor_1() ->
    case parse_file("src/monitoring/testing/prop_test_proofsystem.hml") of
        {ok, Ast} ->
            Ast;
        {error, Reason} ->
            throw({error, Reason})
    end.

get_monitor_2() ->
    case parse_file("src/monitoring/testing/prop_test_traceaggragator.hml") of
        {ok, Ast} ->
            Ast;
        {error, Reason} ->
            throw({error, Reason})
    end.

get_monitor_3() ->
    case parse_file("src/monitoring/testing/prop_test_action.hml") of
        {ok, Ast} ->
            Ast;
        {error, Reason} ->
            throw({error, Reason})
    end.

slab([]) ->
    [];
slab([F | R]) ->
    case io_lib:char_list(F) of
        true ->
            [F | slab(R)];
        false ->
            slab(F) ++ slab(R)
    end.

-spec gen_action_test_(File :: file:filename(), Fun :: function()) -> ok.
gen_action_test_(File, Fun) ->
    try parse_file(File) of
        {ok, Ast} ->
            slab(gen_action_form(Ast, Fun));
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    catch
        _:Reason:Stk ->
            erlang:raise(error, Reason, Stk)
    end.

gen_action_form([], _) ->
    [];
gen_action_form([{form, _, _, Shml} | Forms], Fun) ->
    [gen_action(Shml, Fun) | gen_action_form(Forms, Fun)].

gen_action({no, _}, _) ->
    [];
gen_action({undefined, _}, _) ->
    [];
gen_action({var, _, _}, _) ->
    [];
gen_action({rec, _, _, Shml}, Fun) ->
    gen_action(Shml, Fun);
gen_action({'and', _, Shml1, Shml2}, Fun) ->
    [gen_action(Shml1, Fun) | gen_action(Shml2, Fun)];
gen_action({'or', _, Shml1, Shml2}, Fun) ->
    [gen_action(Shml1, Fun) | gen_action(Shml2, Fun)];
gen_action({nec, _, Act, Shml}, Fun) ->
    [Fun(Act) | gen_action(Shml, Fun)].

removes_whitespace(String) ->
    re:replace(
        lists:flatten(
            io_lib:format("~p", [String])),
        "\\s+",
        "",
        [global, {return, list}]).

-spec start() -> pid().
start() ->
    spawn(?MODULE, loop, []).

-spec loop() -> no_return().
loop() ->
    receive
        {'end'} ->
            'end';
        {_} ->
            loop()
    end.

        %"{trace,'_',init,'_',system,start,{'_',[]}}",
        % "{trace,'_','receive',{r,[]}}",
        % "{trace,'_','receive',{s,[]}}",
        % "{trace,'_','receive',{a,[]}}",
        % "{trace,'_','receive',{c,[]}}",

-spec gen_action_test_cal() -> ok.
gen_action_test_cal() ->
    Ast = get_monitor_3(),
    List1 = lists:flatten(gen_action_form(Ast, fun proof_eval:get_action/1)),
    List2 = lists:flatten(gen_action_form(Ast, fun removes_whitespace/1)),
    io:format("Calculated difference <~p%> ~n",
              [string:len(List1) / string:len(List2) * 100]).

file_exists(FilePath) ->
    case file:read_file_info(FilePath) of
        {ok, _Info} ->
            true;
        _ ->
            false
    end.

file_doesnt_exists(FilePath) ->
    case file:read_file_info(FilePath) of
        {ok, _Info} ->
            false;
        _ ->
            true
    end.

should_contain_trace([], _) ->
    false;
should_contain_trace([HeadHistory | RestHistory], Trace) ->
    case HeadHistory == Trace of
        true ->
            true;
        false ->
            should_contain_trace(RestHistory, Trace)
    end.

% Test cases

proof_system_History_1_test() ->
    ?assertEqual(undefined, prove_property(get_monitor_1(), [[]])).

proof_system_History_2_test() ->
    ?assertEqual(undefined,
                 prove_property(get_monitor_1(), [["{trace,'_',init,'_',system,start,{'_',[]}}"]])).

proof_system_History_3_test() ->
    ?assertEqual(undefined,
                 prove_property(get_monitor_1(),
                                [["{trace,'_',init,'_',system,start,{'_',[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{a,[]}}"]])).

proof_system_History_4_test() ->
    ?assertEqual(undefined,
                 prove_property(get_monitor_1(),
                                [["{trace,'_',init,'_',system,start,{'_',[]}}",
                                  "{trace,'_','receive',{c,[]}}"]])).

proof_system_History_5_test() ->
    ?assertEqual(undefined,
                 prove_property(get_monitor_1(),
                                [["{trace,'_',init,'_',system,start,{'_',[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{a,[]}}"],
                                 ["{trace,'_',init,'_',system,start,{'_',[]}}",
                                  "{trace,'_','receive',{c,[]}}"]])).

proof_system_History_6_test() ->
    ?assertEqual(no,
                 prove_property(get_monitor_1(),
                                [["{trace,'_',init,'_',system,start,{'_',[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{a,[]}}"],
                                 ["{trace,'_',init,'_',system,start,{'_',[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{c,[]}}"]])).

trace_aggragator_instrument_1_test() ->
    Pid = rechml_unit_test:start(),
    Pid ! {q},
    ?small_wait,
    ?assert(file_doesnt_exists("rechml_unit_test_history.txt")).

trace_aggragator_instrument_2_test() ->
    Pid = rechml_unit_test:start(),
    Pid ! {r},
    Pid ! {s},
    Pid ! {a},
    ?small_wait,
    ?assert(file_exists("rechml_unit_test_history.txt")),
    {ok, History} = read_history("rechml_unit_test_history.txt"),
    ?assert(should_contain_trace(History,
                                 ["{trace,'_',init,'_',rechml_unit_test,loop,{[],[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{a,[]}}"])).

trace_aggragator_instrument_3_test() ->
    Pid = start(),
    Pid ! {r},
    Pid ! {s},
    Pid ! {c},
    ?small_wait,
    ?assert(file_exists("rechml_unit_test_history.txt")),
    {ok, History} = read_history("rechml_unit_test_history.txt"),
    ?assert(should_contain_trace(History,
                                 ["{trace,'_',init,'_',rechml_unit_test,loop,{[],[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{c,[]}}"])).

trace_aggragator_instrument_4_test() ->
    Pid = rechml_unit_test:start(),
    Pid ! {r},
    Pid ! {s},
    Pid ! {a},
    Pid ! {r},
    Pid ! {s},
    Pid ! {a},
    ?small_wait,
    ?assert(file_exists("rechml_unit_test_history.txt")),
    {ok, History} = read_history("rechml_unit_test_history.txt"),
    ?assert(should_contain_trace(History,
                                 ["{trace,'_',init,'_',rechml_unit_test,loop,{[],[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{a,[]}}",
                                  "{trace,'_','receive',{r,[]}}",
                                  "{trace,'_','receive',{s,[]}}",
                                  "{trace,'_','receive',{a,[]}}"])).

trace_aggragator_instrument_breakdown_test() ->
    file:delete("rechml_unit_test_history.txt"),
    file:delete("ebin/prop_test_traceaggragator.beam"),
    ?assert(file_doesnt_exists("rechml_unit_test_history.txt")),
    ?assert(file_doesnt_exists("ebin/prop_test_traceaggragator.beam")).

gen_action_test() ->
    ?assert(string:len(
                lists:flatten(gen_action_form(get_monitor_3(), fun proof_eval:get_action/1)))
            < string:len(
                  lists:flatten(gen_action_form(get_monitor_3(), fun removes_whitespace/1)))).

% Function to run the tests
run_tests() ->
    eunit:test(rechml_unit_test),
    io:format("~nIMPORTANT NOTE: Because the weave function is not behaving as expected when run in a function test enviorment~n"
              "You are expected to run these 2 functions  before run_tests() to ensure that the tests run with the weaver in the correct enviorment.~n"
              "Also ensure that you re run the erlang enviorment, thus the list of commands is:~n~n"),
    io:format("detector_new/detecter$ erl -pa ../../detecter/ebin ebin~n"),
    io:format("rechml_eval:compile(\"src/monitoring/testing/prop_test_traceaggragat"
              "or.hml\",[{outdir, \"ebin\"}, v]).~n"),
    io:format("weaver:weave(\"src/monitoring/testing\",fun prop_test_traceaggragato"
              "r:mfa_spec/1,[{outdir, \"ebin\"}]).~n"),
    io:format("rechml_unit_test:run_tests().~n~n"),

    io:format("If you have already done these setps ignore this note.~n").


