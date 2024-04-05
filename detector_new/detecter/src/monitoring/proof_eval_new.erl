-module(proof_eval_new).

-author("Jacob Deguara").

%%% Includes.
-include_lib("stdlib/include/assert.hrl").
-include_lib("syntax_tools/include/merl.hrl").

-include("log.hrl").

-export([convert_act_to_format/1, read_history/1]).
-export([prove_property/2]).
-export([create_erl_syntax_proof_tree/1]).
-export([write_history/2]).
-export([get_trace/1]).

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
-type action() :: string().
-type trace() :: [action()].
-type history() :: [trace()].
-type proof_return_types() :: ff | undefined | {atom(), ff}.

          % Note {atom(), ff} is not used but i dont want to break anything so i left it.

%%% ----------------------------------------------------------------------------
%%% Trace Format Functions.
%%% ----------------------------------------------------------------------------

%%% visit_act_string() takes an action and return a new structure ment to be smaller
%%% and ment to allow one to more easily see the difference between each trace.

-spec convert_act_to_format(Act) -> any() when Act :: af_act().
convert_act_to_format({fork, _, Var0, Var1, {mfa, _, Mod, Fun, _, Clause}}) ->
    {trace,
     clause_to_format(Var0),
     spawn,
     clause_to_format(Var1),
     Mod,
     Fun,
     clause_to_format(Clause)};
convert_act_to_format({init, _, Var0, Var1, {mfa, _, Mod, Fun, _, Clause}}) ->
    {trace,
     clause_to_format(Var0),
     init,
     clause_to_format(Var1),
     Mod,
     Fun,
     clause_to_format(Clause)};
convert_act_to_format({exit, _, Var, Clause}) ->
    {exit, clause_to_format(Var), clause_to_format(Clause)};
convert_act_to_format({send, _, Var1, Var2, Clause}) ->
    {trace, clause_to_format(Var1), send, clause_to_format(Var2), clause_to_format(Clause)};
convert_act_to_format({recv, _, Var, Clause}) ->
    {trace, clause_to_format(Var), 'receive', clause_to_format(Clause)};
convert_act_to_format({user, _, Clause}) ->
    {user, clause_to_format(Clause)}.

%% Takes simple sets of Clause types and returns an object representing the Trace
-spec clause_to_format(Any) -> any() when Any :: list() | map().
clause_to_format({var, _, String}) ->
    String;
clause_to_format({atom, _, String}) ->
    String;
clause_to_format([]) ->
    [];
clause_to_format([Head]) ->
    clause_to_format(Head);
clause_to_format([Head | Rest]) ->
    [clause_to_format(Head) | clause_to_format(Rest)];
clause_to_format({tuple, _, List}) ->
    clause_to_format(List);
clause_to_format({op, _, Op, Var1, Var2}) ->
    {Op, clause_to_format(Var1), clause_to_format(Var2)};
clause_to_format({clause, _, List1, List2, List3}) ->
    {clause_to_format(List1), clause_to_format(List2), clause_to_format(List3)}.

% read_env takes a file name and reads the Data and extracts the Traces compiled
% returning the history or an error
-spec read_history(File :: file:filename()) ->
                      {ok, Env :: [list()]} | {error, Error :: error_info()}.
read_history(File) when is_list(File) ->
    case file:read_file(File) of
        {ok, Bytes} ->
            {ok, format_binary_to_history(binary_to_list(Bytes))};
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    end.

% Takes a Binary list and tokens the list based on '\n'.
-spec format_binary_to_history(Line) -> list() when Line :: [byte()].
format_binary_to_history(Line) ->
    format_binary_to_history2(string:tokens(Line, "\n")).

% Takes a Binary list and tokens the list based on ';'.
format_binary_to_history2([]) ->
    [];
format_binary_to_history2([Head | Rest]) ->
    [string:tokens(Head, ";"), format_binary_to_history2(Rest)].

%%% ----------------------------------------------------------------------------
%%% Proof System Functions.
%%% ----------------------------------------------------------------------------

% prove_property() takes the genereated prooftree and a Lists of Lists Histroy
% and goes through the tree eventually returning a no or undefined result.
-spec prove_property(Ast, History) -> no | undefined
    when Ast :: [formula()],
         History :: history().
prove_property(Ast, History) ->
    prove_property_form_seq(Ast, History, dict:new()).

% RecRefDic is the Recersive element Refrence Dictionary that refrences the shml from a given Max node

% prove_property_form_seq goes through the first set of different properties one tree might have.
-spec prove_property_form_seq(List, History, RecRefDic) -> no | undefined
    when List :: [formula()],
         History :: history(),
         RecRefDic :: dict:dict().
prove_property_form_seq(_List = [_Head = {form, _, _, Shml}], History, RecRefDic) ->
    Result = prove_shml(Shml, History, RecRefDic),
    if Result == ff ->
           no;
       true ->
           undefined
    end;
prove_property_form_seq(_List = [_Head = {form, _, _, Shml} | Forms],
                        History,
                        RecRefDic) ->
    Result = prove_shml(Shml, History, RecRefDic),
    if Result == ff ->
           no;
       true ->
           prove_property_form_seq(Forms, History, RecRefDic)
    end.

% prove_shml() goes through the Shml nodes and does the appropriate logic
% Max node will add its SHMl to the Dictionary RecRefDic with its atom as the refrence
% Var node will continue opening the tree using that refrence.
% 'and' and 'or' will do the appropriate functions from determining the result.
% and ff will result in an ff being returned.
-spec prove_shml(Shml, History, RecRefDic) -> proof_return_types()
    when Shml :: af_shml(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml(_Node = {ff, _}, _ENV, _) ->
    ?TRACE("Proving 'ff' Leaf node ~p.~n", [_Node]),
    ff;
prove_shml(_Var = {var, _, Name}, History, RecRefDic) ->
    Rec = dict:fetch(Name, RecRefDic),
    ?TRACE("Proving 'var' Leaf node ~p.~n Refrenced Tree:~p.~n", [_Var, Rec]),
    prove_shml(Rec, History, RecRefDic);
prove_shml(_Max = {max, _, _Var = {var, _, Name}, Shml}, History, RecRefDic) ->
    ?TRACE("Proving 'max' node~p.~n Dictionary Refrence ~p.~n", [_Max, _Var]),
    NewRecRefDic = dict:store(Name, Shml, RecRefDic),
    prove_shml(Shml, History, NewRecRefDic);
prove_shml(_And = {'and', _, _, ShmlSeq}, History, RecRefDic) ->
    ?TRACE("Proving 'and' node ~p.~n", [_And]),
    prove_shml_seq_and(ShmlSeq, History, RecRefDic);
prove_shml(_Or = {'or', _, _, ShmlSeq}, History, RecRefDic) ->
    ?TRACE("Proving 'or' node~p.~n", [_Or]),
    prove_shml_seq_or(ShmlSeq, History, RecRefDic).

% prove_shml_seq_and() will continue to prove based on the Shml and then run an analysis check on the given result.
-spec prove_shml_seq_and(Shml_seq, History, RecRefDic) -> proof_return_types()
    when Shml_seq :: af_shml_seq(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml_seq_and([Nec], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    ?TRACE("Proving 'and' -FINAL Result:~p.~n", [Result]),
    Result;
prove_shml_seq_and([Nec | Shml_seq], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    ?TRACE("Proving 'and' -ANALYZE- Result:~p.~n", [Result]),
    prove_shml_seq_and_analysis(Result, Shml_seq, History, RecRefDic).

% prove_shml_seq_and_analysis() will
% given ff -> ff
% given undefined & Next_Shml exists -> try running prove shml on the Next_Shml
% given undefeined & Next_Shml is empty -> undefined

-spec prove_shml_seq_and_analysis(Result, Next_Shml, History, RecRefDic) ->
                                     proof_return_types()
    when Result :: proof_return_types(),
         Next_Shml :: af_shml_seq(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml_seq_and_analysis(ff, _, _, _) ->
    ff;
prove_shml_seq_and_analysis(undefined, [], _, _) ->
    undefined;
prove_shml_seq_and_analysis(undefined, Next_Shml, History, RecRefDic) ->
    prove_shml_seq_and(Next_Shml, History, RecRefDic).

% prove_shml_seq_or will run the prove Nec on the given shml and check using the analysis function
-spec prove_shml_seq_or(Shml_seq, History, RecRefDic) -> proof_return_types()
    when Shml_seq :: af_shml_seq(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml_seq_or([Nec], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    ?TRACE("Proving 'or' -FINAL Result:~p.~n", [Result]),
    Result;
prove_shml_seq_or([Nec | Shml_seq], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    ?TRACE("Proving 'or' -ANALYZE- Result:~p.~n", [Result]),
    prove_shml_seq_or_analysis(Result, Shml_seq, History, RecRefDic).

% prove_shml_seq_or_analysis() will
% given the result and an empty shml -> Result
% given undefined -> undefined
% given ff and Next_Shml exists -> try Next_Shml
-spec prove_shml_seq_or_analysis(Result, Next_ShmlSeq, History, RecRefDic) ->
                                    proof_return_types()
    when Result :: proof_return_types(),
         Next_ShmlSeq :: af_shml_seq(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml_seq_or_analysis(Result, [], _, _) ->
    Result;
prove_shml_seq_or_analysis(undefined, _, _, _) ->
    undefined;
prove_shml_seq_or_analysis(ff, Next_ShmlSeq, History, RecRefDic) ->
    prove_shml_seq_or(Next_ShmlSeq, History, RecRefDic).

% prove_nec() will check that the resulting Action matches an Action in the History
% if the result is the emtpy list it will end here.
% else it continues on.
-spec prove_nec(Nec, History, RecRefDic) -> proof_return_types()
    when Nec :: af_nec(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_nec(_Nec = {nec, _, Act, Shml}, History, RecRefDic) ->
    Result = sub(History, get_trace(Act)),
    ?TRACE("Proving 'nec' node ~n Action:~p,~n History:~p,~n New_History "
           "~p,~n",
           [Act, History, Result]),
    if Result == [] ->
           undefined;
       true ->
           prove_shml(Shml, Result, RecRefDic)
    end.

-spec sub(History :: history(), Trace :: trace()) -> history().
sub([], _Trace) ->
    [];
sub([_HeadTrace = [HeadAction | RestAction] | RestHistory], Trace)
    when HeadAction == Trace ->
    [RestAction | sub(RestHistory, Trace)];
sub([_HeadTrace = [HeadAction | _RestAction] | RestHistory], Trace)
    when HeadAction =/= Trace ->
    sub(RestHistory, Trace).

%%% ----------------------------------------------------------------------------
%%% Synthesising specific functions.
%%% ----------------------------------------------------------------------------

% Takes a given proof tree and converts it to a erl_syntax version for synthesizing.
-spec create_erl_syntax_proof_tree(Ast) -> erl_syntax:syntaxTree()
    when Ast :: [formula()].
create_erl_syntax_proof_tree(Ast) ->
    erl_syntax:list(create_erl_syntax_proof_tree_forms(Ast)).

create_erl_syntax_proof_tree_forms([]) ->
    [];
create_erl_syntax_proof_tree_forms([{form, _, {mfa, _, _, _, _, _}, Shml} | Forms]) ->
    [erl_syntax:tuple([erl_syntax:atom(form),
                       erl_syntax:atom(ignore),
                       erl_syntax:atom(ignore),
                       create_erl_syntax_proof_tree_shml(Shml)])
     | create_erl_syntax_proof_tree_forms(Shml)].

create_erl_syntax_proof_tree_shml({ff, _}) ->
    erl_syntax:tuple([erl_syntax:atom(ff), erl_syntax:atom(ignore)]);
create_erl_syntax_proof_tree_shml({var, _, Name}) ->
    erl_syntax:tuple([erl_syntax:atom(var), erl_syntax:atom(ignore), erl_syntax:atom(Name)]);
create_erl_syntax_proof_tree_shml({max, _, Var, Shml}) ->
    erl_syntax:tuple([erl_syntax:atom(max),
                      erl_syntax:atom(ignore),
                      create_erl_syntax_proof_tree_shml(Var),
                      create_erl_syntax_proof_tree_shml(Shml)]);
create_erl_syntax_proof_tree_shml({'and', _, _, Shml_seq}) ->
    erl_syntax:tuple([erl_syntax:atom('and'),
                      erl_syntax:atom(ignore),
                      erl_syntax:atom(ignore),
                      erl_syntax:list([create_erl_syntax_proof_tree_shml_seq(Shml_seq)])]);
create_erl_syntax_proof_tree_shml({'or', _, _, Shml_seq}) ->
    erl_syntax:tuple([erl_syntax:atom('or'),
                      erl_syntax:atom(ignore),
                      erl_syntax:atom(ignore),
                      erl_syntax:list([create_erl_syntax_proof_tree_shml_seq(Shml_seq)])]);
create_erl_syntax_proof_tree_shml({nec, _, Act, Shml}) ->
    erl_syntax:tuple([erl_syntax:atom(nec),
                      erl_syntax:atom(ignore),
                      erl_syntax:string(get_trace(Act)),
                      create_erl_syntax_proof_tree_shml(Shml)]).

create_erl_syntax_proof_tree_shml_seq([Nec]) ->
    [create_erl_syntax_proof_tree_shml(Nec)];
create_erl_syntax_proof_tree_shml_seq([Nec | Shml_seq]) ->
    [create_erl_syntax_proof_tree_shml(Nec)
     | create_erl_syntax_proof_tree_shml_seq(Shml_seq)].

% add_to_history takes a history and a trace and and adds the Trace to the history
-spec add_to_history(TraceList, Trace) -> Result
    when TraceList :: history(),
         Trace :: trace(),
         Result :: history().
add_to_history([], []) ->
    [];
add_to_history([], Trace) ->
    [Trace];
add_to_history([HeadTrace | RestHistory], Trace) ->
    Test = ordsets:is_subset(HeadTrace, Trace) andalso ordsets:is_subset(Trace, HeadTrace),
    if Test ->
           [HeadTrace | add_to_history(RestHistory, [])];
       true ->
           [HeadTrace | add_to_history(RestHistory, Trace)]
    end.

% write_history takes a Trace and file name,
% Read the file to get the history,
% adds the Trace to the history,
% add the Trace to the file with the history if the new history was changed,
% and returns the new history.
-spec write_history(New_Trace, FileName) -> New_History
    when New_Trace :: trace(),
         FileName :: string(),
         New_History :: history().
write_history(New_Trace, FileName) ->
    {ok, Fd} = file:open(FileName, [append]),
    {ok, Old_History} = read_history(FileName),
    New_History = add_to_history(Old_History, New_Trace),
    Test =
        ordsets:is_subset(Old_History, New_History)
        andalso ordsets:is_subset(New_History, Old_History),
    if Test ->
           New_History;
       true ->
           file:write(Fd, [format_trace_for_writing(New_Trace), "\n"]),
           New_History
    end.

% format_trace_for_writing() adds ; to the Trace bewteen each action
-spec format_trace_for_writing([string()]) -> [string()].
format_trace_for_writing([]) ->
    [];
format_trace_for_writing([Head | Rest]) ->
    [Head, ";" | format_trace_for_writing(Rest)].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-spec get_trace(Act :: af_act() | list() | string()) -> string().
get_trace(Act) when is_list(Act) ->
    Result = io_lib:char_list(Act),
    if Result ->
           Act;
       true ->
           lists:flatten(
               io_lib:format("~p", [lists:flatten(Act)]))
    end;
get_trace(Act) ->
    Result = io_lib:char_list(Act),
    if Result ->
           Act;
       true ->
           lists:flatten(
               io_lib:format("~p", [convert_act_to_format(Act)]))
    end.
