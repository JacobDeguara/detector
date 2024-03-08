-module(proof_eval).

-author("Jacob Deguara").

%%% Includes.
-include_lib("stdlib/include/assert.hrl").
-include_lib("syntax_tools/include/merl.hrl").

-include("log.hrl").

-export([visit_act_string/1, read_env/1, create_proof_tree/1]).
-export([sub_EnvTrace/2]).
-export([already_exists/2]).
-export([append_EnvTrace/2]).
-export([find_ff_shml/1]).
-export([sub_EnvTraces/2]).

%%% ----------------------------------------------------------------------------
%%% Macro and record definitions.
%%% ----------------------------------------------------------------------------

%% File extensions.
-define(EXT_HML, ".hml").
-define(EXT_ERL, ".erl").
-define(EXT_BEAM, ".beam").
-define(MFA_SPEC, mfa_spec).
%% Option definitions and their values.
%%-define(OPT_INCLUDE, i). % Kept same option name as Erlang compiler.
-define(OPT_OUT_DIR, outdir). % Kept same option name as Erlang compiler.
-define(OPT_ERL, erl).
-define(OPT_VERBOSE, v).
%% Default Erlang compiler options.
-define(COMPILER_OPTS, [nowarn_shadow_vars, return]).

%%% ----------------------------------------------------------------------------
%%% Type definitions.
%%% ----------------------------------------------------------------------------

%%-type option() :: {outdir, directory()} | erl | v.
-type option() :: opts:option().

%% Compiler options.

-type options() :: [option()].

%% Compiler option list.

-type directory() :: string().

%% Directory.

-type line() :: erl_anno:line().

%% Line number in source.

-type error_description() :: term().

%% Internal error description.

-type error_info() :: {line(), module(), error_description()}.

%% Error information.

-type warnings() :: [{file:filename(), [error_info()]}] | [].

%% Warning list.

-type errors() :: [{file:filename(), [error_info()]}] | [].

%% Error list.

-type af_ff() :: {ff, line()}.
-type af_var() :: {var, line(), atom()}.
-type af_max() :: {max, line(), af_var(), af_shml()}.
-type af_n_and() :: {'and', line(), arity(), af_shml_seq()}.
-type af_n_or() :: {'or', line(), arity(), af_shml_seq()}.
-type af_nec() :: {nec, line(), af_act(), af_shml()}.
-type af_shml() :: af_ff() | af_var() | af_max() | af_n_and() | af_n_or().
-type af_shml_seq() :: [af_nec()].
-type formula() :: {form, line(), af_mfa(), af_shml()}.
-type af_mfa() :: {mfa, line(), module(), atom(), arity(), erl_parse:abstract_clause()}.
-type af_fork_act() :: {fork, line(), af_var(), af_var(), af_mfa()}.
-type af_init_act() :: {init, line(), af_var(), af_var(), af_mfa()}.
-type af_exit_act() :: {exit, line(), af_var(), erl_parse:abstract_clause()}.
-type af_send_act() :: {send, line(), af_var(), erl_parse:abstract_clause()}.
-type af_recv_act() :: {recv, line(), af_var(), erl_parse:abstract_clause()}.
-type af_user_act() :: {user, line(), erl_parse:abstract_clause()}.
-type af_act() ::
    af_fork_act() |
    af_init_act() |
    af_exit_act() |
    af_send_act() |
    af_recv_act() |
    af_user_act().
-type pf_ff() :: {ff}.
-type pf_var() :: {var, atom()}.
-type pf_max() :: {max, pf_var(), pf_shml()}.
-type pf_n_and() :: {'and', pf_shml_seq()}.
-type pf_n_or() :: {'or', pf_shml_seq()}.
-type pf_nec() :: {nec, pf_act(), pf_shml()}.
-type pf_shml() :: pf_ff() | pf_var() | pf_max() | pf_n_and() | pf_n_or().
-type pf_shml_seq() :: [pf_nec()].
-type pf_act() :: string().
-type pf_formula() :: {form, pf_shml()}.
-type pf_head() :: {head, [pf_formula()]}.
-type envTrace() :: [string()].
-type envTraces() :: [envTrace()].
-type proof_return_types() :: ff | undefined | {atom(), envTraces()}.

%%% ----------------------------------------------------------------------------
%%% Trace Format Functions.
%%% ----------------------------------------------------------------------------

%% Takes an Act type and returns an object representing the Trace
-spec visit_act_string(Act) -> any() when Act :: af_act().
visit_act_string({fork, _, Var0, Var1, {mfa, _, Mod, Fun, _, Clause}}) ->
    {trace,
     extract_act_string(Var0),
     spawn,
     extract_act_string(Var1),
     Mod,
     Fun,
     extract_act_string(Clause)};
visit_act_string({init, _, Var0, Var1, {mfa, _, Mod, Fun, _, Clause}}) ->
    {trace,
     extract_act_string(Var0),
     init,
     extract_act_string(Var1),
     Mod,
     Fun,
     extract_act_string(Clause)};
visit_act_string({exit, _, Var, Clause}) ->
    {exit, extract_act_string(Var), extract_act_string(Clause)};
visit_act_string({send, _, Var1, Var2, Clause}) ->
    {trace,
     extract_act_string(Var1),
     send,
     extract_act_string(Var2),
     extract_act_string(Clause)};
visit_act_string({recv, _, Var, Clause}) ->
    {trace, extract_act_string(Var), 'receive', extract_act_string(Clause)};
visit_act_string({user, _, Clause}) ->
    {user, extract_act_string(Clause)}.

%% Takes simple sets of Clause types and returns an object representing the Trace
-spec extract_act_string(Any) -> any() when Any :: list() | map().
extract_act_string({var, _, String}) ->
    String;
extract_act_string({atom, _, String}) ->
    String;
extract_act_string([]) ->
    [];
extract_act_string([Head]) ->
    extract_act_string(Head);
extract_act_string([Head | Rest]) ->
    [extract_act_string(Head) | extract_act_string(Rest)];
extract_act_string({tuple, _, List}) ->
    extract_act_string(List);
extract_act_string({op, _, Op, Var1, Var2}) ->
    {Op, extract_act_string(Var1), extract_act_string(Var2)};
extract_act_string({clause, _, List1, List2, List3}) ->
    {extract_act_string(List1), extract_act_string(List2), extract_act_string(List3)}.

% Reads a file and returns a lists of lists of traces
-spec read_env(File :: file:filename()) ->
                  {ok, Env :: [list()]} | {error, Error :: error_info()}.
read_env(File) when is_list(File) ->
    case file:read_file(File) of
        {ok, Bytes} ->
            {ok, split_Bytes(binary_to_list(Bytes))};
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    end.

% Takes a list of bytes and splits it based on \n and ;
-spec split_Bytes(Line) -> list() when Line :: [byte()].
split_Bytes(Line) ->
    foreach(fun(H) -> string:tokens(H, ";") end, string:tokens(Line, "\n")).

% Applies a function to a list
foreach(F, [H | T]) ->
    [F(H) | foreach(F, T)];
foreach(F, []) ->
    [].

% creates a tree based on the hml for proofing
-spec create_proof_tree(Ast) -> Forms :: [pf_head()] when Ast :: [formula()].
create_proof_tree(Ast) ->
    {head, visit_proof_forms(Ast)}.

% goes through each of the forms
-spec visit_proof_forms(Forms) -> Forms :: [pf_formula()] when Forms :: [formula()].
visit_proof_forms([]) ->
    [];
visit_proof_forms([{form, _, _, Shml} | Forms]) ->
    [{form, visit_proof_shml(Shml)} | visit_proof_forms(Forms)].

% Takes the Shml types and returns a simpler version
-spec visit_proof_shml(Shml) -> pf_shml() when Shml :: af_shml().
visit_proof_shml(_Node = {ff, _}) ->
    {ff};
visit_proof_shml(Var = {var, _, Name}) ->
    {Var, Name};
visit_proof_shml(_Node = {max, _, _Var = {var, _, Name}, Shml}) ->
    {max, {var, Name}, visit_proof_shml(Shml)};
visit_proof_shml(_Node = {'or', _, _, ShmlSeq}) when is_list(ShmlSeq) ->
    {'or', visit_proof_shml_seq(ShmlSeq)};
visit_proof_shml(_Node = {'and', _, _, ShmlSeq}) when is_list(ShmlSeq) ->
    {'and', visit_proof_shml_seq(ShmlSeq)}.

% goes through the list of shml sequenses
-spec visit_proof_shml_seq(ShmlSeq) -> [pf_shml()] when ShmlSeq :: af_shml_seq().
visit_proof_shml_seq([Nec]) ->
    [visit_proof_nec(Nec)];
visit_proof_shml_seq([Nec | ShmlSeq]) ->
    [visit_proof_nec(Nec) | visit_proof_shml_seq(ShmlSeq)].

% nec has the Trace important
-spec visit_proof_nec(Nec) -> pf_shml() when Nec :: af_nec().
visit_proof_nec(_Node = {nec, _, Act, Shml}) ->
    Body = visit_proof_shml(Shml),
    Trace = io_lib:format("~p", [visit_act_string(Act)]),
    io:format("~p~n", [flatten([Trace])]),
    {nec, flatten(Trace), Body}.

% takes a lists of lists and returns a list
flatten(X) ->
    flatten(X, []).
    
flatten([], Acc) ->
    Acc;
flatten([[] | T], Acc) ->
    flatten(T, Acc);
flatten([[_ | _] = H | T], Acc) ->
    flatten(T, flatten(H, Acc));
flatten([H | T], Acc) ->
    flatten(T, Acc ++ [H]).

-spec prove_property(Proof_tree, EnvTrace) -> no | undefined
    when Proof_tree :: [pf_head()],
         EnvTrace :: envTraces().
prove_property(_Proof_tree = {head, Form_seq}, EnvTrace) ->
    prove_property_form_seq(Form_seq, EnvTrace).

-spec prove_property_form_seq(List, EnvTrace) -> no | undefined
    when List :: [pf_formula()],
         EnvTrace :: envTraces().
prove_property_form_seq(_List = [_Head = {form, Shml}], EnvTrace) ->
    Result = prove_shml(Shml, EnvTrace),
    if Result == ff ->
           no;
       true ->
           undefined
    end;
prove_property_form_seq(_List = [_Head = {form, Shml} | Rest], EnvTrace) ->
    Result = prove_shml(Shml, EnvTrace),
    if Result == ff ->
           no;
       true ->
           prove_property_form_seq(Rest, EnvTrace)
    end.

-spec prove_shml(Shml, EnvTrace) -> proof_return_types()
    when Shml :: pf_shml(),
         EnvTrace :: envTraces().
prove_shml({ff}, _) ->
    ff;
prove_shml({var, Var}, EnvTrace) ->
    if EnvTrace == [] ->
           undefined;
       true ->
           {Var, EnvTrace}
    end;
prove_shml(Max = {max, _Var_ob = {var, Var}, Shml}, EnvTrace) ->
    Result = prove_shml(Shml, EnvTrace),
    {Result_check, NewEnvTrace} = check_Var(Result, Var, EnvTrace),
    if Result_check ->
           prove_shml(Max, NewEnvTrace);
       true ->
           Result
    end;
prove_shml({'and', ShmlSeq}, EnvTrace) ->
    prove_shml_seq_and(ShmlSeq, EnvTrace);
prove_shml({'or', ShmlSeq}, EnvTrace) ->
    prove_shml_seq_or(ShmlSeq, EnvTrace).

-spec prove_shml_seq_and(Shml_seq, EnvTrace) -> proof_return_types()
    when Shml_seq :: pf_shml_seq(),
         EnvTrace :: envTraces().
prove_shml_seq_and([Nec], EnvTrace) ->
    prove_nec(Nec, EnvTrace);
prove_shml_seq_and([Nec | Shml_seq], EnvTrace) ->
    Result = prove_nec(Nec, EnvTrace),
    if Result == undefined ->
           prove_shml_seq_and(Shml_seq, EnvTrace);
       Result == ff ->
           ff;
       true ->
           Result_SubSet = check_EnvTrace_SubSet(Result, EnvTrace),
           if Result_SubSet ->
                  prove_shml_seq_and(Shml_seq, EnvTrace);
              true ->
                  Result
           end
    end.

-spec prove_shml_seq_or(Shml_seq, EnvTrace) -> proof_return_types()
    when Shml_seq :: pf_shml_seq(),
         EnvTrace :: envTraces().
prove_shml_seq_or([Nec], EnvTrace) ->
    prove_nec(Nec, EnvTrace);
prove_shml_seq_or([Nec | Shml_seq], EnvTrace) ->
    Result = prove_nec(Nec, EnvTrace),
    Result_ff = find_ff_shml(Nec),
    if Result == ff ->
           prove_shml_seq_or(Shml_seq, EnvTrace);
       Result == undefined ->
           if Result_ff == found ->
                  Result;
              true ->
                  prove_shml_seq_or(Shml_seq, EnvTrace)
           end;
       true -> % {Var, Rest of the Trace} do this in a function so that you can
           % change the EnvTrace if needed.
           if Result_ff == none ->
                  Result_Next = prove_shml_seq_or(Shml_seq, EnvTrace),
                  if Result_Next == ff ->
                         ff;
                     Result_Next == undefined ->
                         Result;
                     true ->
                         Result_SubSet = check_EnvTrace_SubSet(Result_Next, EnvTrace),
                         if Result_SubSet ->
                                Result;
                            true ->
                                Result_Next
                         end
                  end;
              true ->
                  Result
           end
    end.

-spec check_EnvTrace_SubSet(EnvTrace1, EnvTrace2) -> boolean()
    when EnvTrace1 :: envTraces(),
         EnvTrace2 :: envTrace().
check_EnvTrace_SubSet({_, NewEnvTrace}, EnvTrace) ->
    check_EnvTrace_SubSet(EnvTrace, NewEnvTrace);
check_EnvTrace_SubSet([LastTrace], Trace) ->
    Result = ordsets:is_subset(LastTrace, Trace),
    if Result ->
           true;
       true ->
           false
    end;
check_EnvTrace_SubSet([HeadTrace | RestTrace], Trace) ->
    Result = ordsets:is_subset(HeadTrace, Trace),
    if Result ->
           true;
       true ->
           check_EnvTrace_SubSet(RestTrace, Trace)
    end.

-spec prove_nec(Nec, EnvTrace) -> proof_return_types()
    when Nec :: pf_nec(),
         EnvTrace :: envTraces().
prove_nec(_Nec = {nec, Trace, Shml}, EnvTrace) ->
    Result = sub_EnvTrace(EnvTrace, Trace),
    if Result == [] ->
           undefined;
       true ->
           prove_shml(Shml, Result)
    end.

-spec check_Var(Proof_return, Var, EnvTrace) -> {boolean(), envTraces()}
    when Proof_return :: proof_return_types(),
         Var :: atom(),
         EnvTrace :: envTraces().
check_Var(ff, _, EnvTrace) ->
    {false, EnvTrace};
check_Var(undefined, _, EnvTrace) ->
    {false, EnvTrace};
check_Var({Var, NewEnvTrace}, VarMax, EnvTrace) ->
    if %% If VarMax (which is the Var the max object represents)
       %% is the same as the Var given
       VarMax == Var ->
           %% then append the newTrace to our oldTrace
           {NewEnvTraceList, Result} = append_EnvTrace(EnvTrace, NewEnvTrace),
           if %% if the Result doesnt change then there are no new Traces we can use
              Result == old ->
                  {false, EnvTrace};
              %% else the NewTraceList
              true ->
                  {true, NewEnvTraceList}
           end;
       true ->
           {false, EnvTrace}
    end.

-spec find_ff_shml(PF_stucture) -> found | none when PF_stucture :: pf_shml() | pf_nec().
find_ff_shml({ff}) ->
    found;
find_ff_shml({var, _}) ->
    none;
find_ff_shml({max, _, Shml}) ->
    find_ff_shml(Shml);
find_ff_shml({'and', ShmlSeq}) ->
    find_ff_shml_seq(ShmlSeq);
find_ff_shml({'or', ShmlSeq}) ->
    find_ff_shml_seq(ShmlSeq);
find_ff_shml({nec, _, Shml}) ->
    find_ff_shml(Shml).

-spec find_ff_shml_seq(PF_stucture_list) -> found | none
    when PF_stucture_list :: pf_shml_seq().
find_ff_shml_seq([Nec]) ->
    find_ff_shml(Nec);
find_ff_shml_seq([Nec | Shml_seq]) ->
    Result = find_ff_shml(Nec),
    if Result == none ->
           find_ff_shml_seq(Shml_seq);
       true ->
           Result
    end.

-spec already_exists(EnvTrace, Trace) -> boolean()
    when EnvTrace :: envTraces(),
         Trace :: envTrace().
already_exists([HeadTrace], Trace) ->
    Result = ordsets:is_subset(HeadTrace, Trace) andalso ordsets:is_subset(Trace, HeadTrace),
    if Result ->
           true;
       true ->
           false
    end;
already_exists([HeadTrace | RestTrace], Trace) ->
    Result = ordsets:is_subset(HeadTrace, Trace) andalso ordsets:is_subset(Trace, HeadTrace),
    if Result ->
           true;
       true ->
           already_exists(RestTrace, Trace)
    end.

-spec append_EnvTrace(TraceList1, TraceList2) -> {TraceList3, old | new}
    when TraceList1 :: envTraces(),
         TraceList2 :: envTraces(),
         TraceList3 :: envTraces().
append_EnvTrace(TraceListOld, TraceListNew) ->
    append_EnvTrace(TraceListOld, TraceListNew, old).

append_EnvTrace(TraceListOld, [TraceHead2], Result_is) when is_list(TraceHead2) ->
    Result = already_exists(TraceListOld, TraceHead2),
    if Result ->
           {TraceListOld, Result_is};
       true ->
           {lists:append(TraceListOld, [TraceHead2]), new}
    end;
append_EnvTrace(TraceListOld, [TraceHead2 | TraceRest2], Result_is) ->
    Result = already_exists(TraceListOld, TraceHead2),
    if Result ->
           append_EnvTrace(TraceListOld, TraceRest2, Result_is);
       true ->
           append_EnvTrace(lists:append(TraceListOld, [TraceHead2]), TraceRest2, new)
    end.

-spec sub_EnvTraces(TraceList, Trace) -> {Result, boolean()}
    when TraceList :: envTraces(),
         Trace :: envTrace(),
         Result :: envTraces().
sub_EnvTraces(TraceList, Trace) ->
    Result = sub_EnvTrace(TraceList, Trace),
    {Result, Result == []}.

-spec sub_EnvTrace(TraceList, Trace) -> Result
    when TraceList :: envTraces(),
         Trace :: envTrace(),
         Result :: envTraces().
sub_EnvTrace([[Head_EnvTrace | Rest_EnvTrace]], Trace) ->
    if Head_EnvTrace == Trace ->
           [Rest_EnvTrace];
       true ->
           []
    end;
sub_EnvTrace([[Head_EnvTrace | Rest_EnvTrace] | Rest_EnvTraces], Trace) ->
    if Head_EnvTrace == Trace ->
           [Rest_EnvTrace | sub_EnvTrace(Rest_EnvTraces, Trace)];
       true ->
           sub_EnvTrace(Rest_EnvTraces, Trace)
    end.
