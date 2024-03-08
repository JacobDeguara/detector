-module(proof_eval).

-author("Jacob Deguara").

%%% Includes.
-include_lib("stdlib/include/assert.hrl").
-include_lib("syntax_tools/include/merl.hrl").

-include("log.hrl").

-export([visit_act_string/1, read_env/1, create_proof_tree/1]).

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
-type pf_head() :: [pf_formula()].

%%% ----------------------------------------------------------------------------
%%% Trace Format Functions.
%%% ----------------------------------------------------------------------------

%% @private
-spec visit_act_string(Act) -> map() when Act :: af_act().
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

-spec read_env(File :: file:filename()) ->
                  {ok, Env :: [list()]} | {error, Error :: error_info()}.
read_env(File) when is_list(File) ->
    case file:read_file(File) of
        {ok, Bytes} ->
            {ok, split_Bytes(binary_to_list(Bytes))};
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    end.

-spec split_Bytes(Line) -> list() when Line :: [byte()].
split_Bytes(Line) ->
    foreach(fun(H) -> string:tokens(H, ";") end, string:tokens(Line, "\n")).

foreach(F, [H | T]) ->
    [F(H) | foreach(F, T)];
foreach(F, []) ->
    [].

-spec create_proof_tree(Ast) -> Forms :: [pf_head()] when Ast :: [formula()].
create_proof_tree(Ast) ->
    {head, visit_proof_forms(Ast)}.

-spec visit_proof_forms(Forms) -> Forms :: [pf_formula()] when Forms :: [formula()].
visit_proof_forms([]) ->
    ok;
visit_proof_forms([{form, _, _, Shml} | Forms]) ->
    [{form, visit_proof_shml(Shml)} | visit_proof_forms(Forms)].

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

-spec visit_proof_shml_seq(ShmlSeq) -> [pf_shml()] when ShmlSeq :: af_shml_seq().
visit_proof_shml_seq([Nec]) ->
    [visit_proof_nec(Nec)];
visit_proof_shml_seq([Nec | ShmlSeq]) ->
    [visit_proof_nec(Nec) | visit_proof_shml_seq(ShmlSeq)].

-spec visit_proof_nec(Nec) -> pf_shml() when Nec :: af_nec().
visit_proof_nec(_Node = {nec, _, Act, Shml}) ->
    Body = visit_proof_shml(Shml),
    Trace = io_lib:format("~p", [visit_act_string(Act)]),
    io:format("~p~n", [flatten([Trace])]),
    {nec, flatten(Trace), Body}.

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
