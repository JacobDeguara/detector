-module(proof_eval).

-author("Jacob Deguara").

%%% Includes.
-include_lib("stdlib/include/assert.hrl").
-include_lib("syntax_tools/include/merl.hrl").

-include("log.hrl").

-export([visit_act_string/1, read_env/1, create_proof_tree/1]).
-export([prove_property/2]).
-export([create_erl_syntax_proof_tree/1]).
-export([write_history/2]).
-export([fix_trace/1]).

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
-type action() :: string().
-type trace() :: [action()].
-type history() :: [trace()].
-type proof_return_types() :: ff | undefined | {atom(), ff}. % Note {atom(), ff} is not used but i dont want to break anything so i left it.

%%% ----------------------------------------------------------------------------
%%% Trace Format Functions.
%%% ----------------------------------------------------------------------------

%%% visit_act_string() takes an action and return a new structure ment to be smaller
%%% and ment to allow one to more easily see the difference between each trace.

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

% read_env takes a file name and reads the Data and extracts the Traces compiled
% Example data is 
% Trace1 : ?Action1?;?Action2?;... \n
% Trace2 : ... \n
% ...
% \n
-spec read_env(File :: file:filename()) ->
                  {ok, Env :: [list()]} | {error, Error :: error_info()}.
read_env(File) when is_list(File) ->
    case file:read_file(File) of
        {ok, Bytes} ->
            {ok, split_Bytes(binary_to_list(Bytes))};
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    end.

% Given the List of aata read from the file it will split the list based on \n and ;
-spec split_Bytes(Line) -> list() when Line :: [byte()].
split_Bytes(Line) ->
    foreach(fun(H) -> string:tokens(H, ";") end, string:tokens(Line, "\n")).

% Applies a function to a list
foreach(F, [H | T]) ->
    [F(H) | foreach(F, T)];
foreach(_, []) ->
    [].

% Generates a proof tree based on the given parsed tree
-spec create_proof_tree(Ast) -> Forms :: [pf_head()] when Ast :: [formula()].
create_proof_tree(Ast) ->
    {head, visit_proof_forms(Ast)}.

% Goes through the Forms section of the parsed tree
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
    {var, Name};
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

% goes through the nec stucture of the trace that has the Action string. 
-spec visit_proof_nec(Nec) -> pf_shml() when Nec :: af_nec().
visit_proof_nec(_Node = {nec, _, Act, Shml}) ->
    Body = visit_proof_shml(Shml),
    Trace = io_lib:format("~p", [visit_act_string(Act)]),
    %io:format("Before: ~p~nAfter: ~p~n", [Shml,Body]),
    {nec, lists:flatten(Trace), Body}.

%%% ----------------------------------------------------------------------------
%%% Proof System Functions.
%%% ----------------------------------------------------------------------------

% prove_property() takes the genereated prooftree and a Lists of Lists Histroy
% and goes through the tree eventually returning a no or undefined result.

-spec prove_property(Proof_tree, History) -> no | undefined
    when Proof_tree :: [pf_head()],
         History :: history().
prove_property(_Proof_tree = {head, Form_seq}, History) ->
    %?TRACE("Proving Property at -HEAD- ~p.",[Form_seq]),
    prove_property_form_seq(Form_seq, History, dict:new()).


% RecRefDic is the Recersive element Refrence Dictionary that refrences the shml from a given Max node

% prove_property_form_seq goes through the first set of different properties one tree might have.
-spec prove_property_form_seq(List, History, RecRefDic) -> no | undefined
    when List :: [pf_formula()],
         History :: history(),
         RecRefDic :: dict:dict().
prove_property_form_seq(_List = [_Head = {form, Shml}], History, RecRefDic) ->
    Result = prove_shml(Shml, History, RecRefDic),
    if Result == ff ->
           no;
       true ->
           undefined
    end;
prove_property_form_seq(_List = [_Head = {form, Shml} | Rest], History, RecRefDic) ->
    Result = prove_shml(Shml, History, RecRefDic),
    if Result == ff ->
           no;
       true ->
           prove_property_form_seq(Rest, History, RecRefDic)
    end.


% prove_shml() goes through the Shml nodes and does the appropriate logic 
% Max node will add its SHMl to the Dictionary RecRefDic with its atom as the refrence
% Var node will continue opening the tree using that refrence.
% 'and' and 'or' will do the appropriate functions from determining the result.
% and ff will result in an ff being returned.
-spec prove_shml(Shml, History, RecRefDic) -> proof_return_types()
    when Shml :: pf_shml(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml({ff}, _ENV, _) ->
    %?TRACE("Proving 'ff' Leaf node~n.",[]),
    ff;
prove_shml({var, Var}, History, RecRefDic) ->
    Rec = dict:fetch(Var, RecRefDic),
    %?TRACE("Proving 'var' Leaf node~n Opening Tree: ~p~n.",[Rec]),
    prove_shml(Rec, History, RecRefDic);
prove_shml(_Max = {max, _Var_ob = {var, Var}, Shml}, History, RecRefDic) ->
    %?TRACE("Proving 'max' node~n Tree: ~p~n.",[Shml]),
    NewRecRefDic = dict:store(Var, Shml, RecRefDic),
    prove_shml(Shml, History, NewRecRefDic);
prove_shml({'and', ShmlSeq}, History, RecRefDic) ->
    %?TRACE("Proving 'and' node~n Tree: ~p~n.",[ShmlSeq]),
    prove_shml_seq_and(ShmlSeq, History, RecRefDic);
prove_shml({'or', ShmlSeq}, History, RecRefDic) ->
    %?TRACE("Proving 'or' node~n Tree: ~p~n.",[ShmlSeq]),
    prove_shml_seq_or(ShmlSeq, History, RecRefDic).


% prove_shml_seq_and() will continue to prove based on the Shml and then run an analysis check on the given result. 
-spec prove_shml_seq_and(Shml_seq, History, RecRefDic) -> proof_return_types()
    when Shml_seq :: pf_shml_seq(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml_seq_and([Nec], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    %?TRACE("Proving 'and' -continued- ~nResult ~p.",[Result]),
    Result;
prove_shml_seq_and([Nec | Shml_seq], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    %?TRACE("Proving 'and' -continued- ~nResult ~p.",[Result]),
    prove_shml_seq_and_analysis(Result, Shml_seq, History, RecRefDic).

% prove_shml_seq_and_analysis() will
% given ff -> ff
% given undefined & Next_Shml exists -> try running prove shml on the Next_Shml
% given undefeined & Next_Shml is empty -> undefined

-spec prove_shml_seq_and_analysis(Result, Next_Shml, History, RecRefDic) ->
                                     proof_return_types()
    when Result :: proof_return_types(),
         Next_Shml :: pf_shml_seq(),
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
    when Shml_seq :: pf_shml_seq(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml_seq_or([Nec], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    %?TRACE("Proving 'or' -continued- ~nResult ~p.",[Result]),
    Result;
prove_shml_seq_or([Nec | Shml_seq], History, RecRefDic) ->
    Result = prove_nec(Nec, History, RecRefDic),
    %?TRACE("Proving 'or' -continued- ~nResult ~p.",[Result]),
    prove_shml_seq_or_analysis(Result, Shml_seq, History, RecRefDic).

% prove_shml_seq_or_analysis() will
% given the result and an empty shml -> Result
% given undefined -> undefined
% given ff and Next_Shml exists -> try Next_Shml
-spec prove_shml_seq_or_analysis(Result, Next_ShmlSeq, History, RecRefDic) ->
                                    proof_return_types()
    when Result :: proof_return_types(),
         Next_ShmlSeq :: pf_shml_seq(),
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
    when Nec :: pf_nec(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_nec(_Nec = {nec, Trace, Shml}, History, RecRefDic) ->
    %?TRACE("Proving 'nec' node with Trace ~p,~n ENV: ~p.",[Trace,History]),
    Result = sub_Histories(History, Trace),
    if Result == [] ->
           undefined;
       true ->
           prove_shml(Shml, Result, RecRefDic)
    end.

% sub_History() takes a History and a Trace, and returns the History with the Trace given removed
% or the empty list of no Trace was found
-spec sub_History(History, Trace) -> {Result, boolean()}
    when History :: history(),
         Trace :: trace(),
         Result :: history().
sub_History(TraceList, Trace) ->
    Result = sub_Histories(TraceList, Trace),
    {Result, Result == []}.

-spec sub_Histories(TraceList, Trace) -> Result
    when TraceList :: history(),
         Trace :: trace(),
         Result :: history().
sub_Histories([[Head_EnvTrace | Rest_EnvTrace]], Trace) ->
    if Head_EnvTrace == Trace ->
           [Rest_EnvTrace];
       true ->
           []
    end;
sub_Histories([[Head_EnvTrace | Rest_EnvTrace] | Rest_EnvTraces], Trace) ->
    if Head_EnvTrace == Trace ->
           [Rest_EnvTrace | sub_Histories(Rest_EnvTraces, Trace)];
       true ->
           sub_Histories(Rest_EnvTraces, Trace)
    end.

%%% ----------------------------------------------------------------------------
%%% Synthesising specific functions.
%%% ----------------------------------------------------------------------------

% Takes a given proof tree and converts it to a erl_syntax version for synthesizing.
-spec create_erl_syntax_proof_tree(Shml) -> erl_syntax:syntaxTree()
    when Shml :: pf_shml() | pf_nec() | pf_head() | pf_formula().
create_erl_syntax_proof_tree({ff}) ->
    erl_syntax:tuple([erl_syntax:atom(ff)]);
create_erl_syntax_proof_tree({var, Atom}) ->
    erl_syntax:tuple([erl_syntax:atom(var), erl_syntax:atom(Atom)]);
create_erl_syntax_proof_tree({max, Var, Shml}) ->
    erl_syntax:tuple([erl_syntax:atom(max),
                      create_erl_syntax_proof_tree(Var),
                      create_erl_syntax_proof_tree(Shml)]);
create_erl_syntax_proof_tree({'and', Shml_seq}) ->
    erl_syntax:tuple([erl_syntax:atom('and'),
                      erl_syntax:list(create_erl_syntax_proof_tree_seq(Shml_seq))]);
create_erl_syntax_proof_tree({'or', Shml_seq}) ->
    erl_syntax:tuple([erl_syntax:atom('or'),
                      erl_syntax:list(create_erl_syntax_proof_tree_seq(Shml_seq))]);
create_erl_syntax_proof_tree({form, Shml}) ->
    erl_syntax:tuple([erl_syntax:atom(form), create_erl_syntax_proof_tree(Shml)]);
create_erl_syntax_proof_tree({head, Shml_seq}) ->
    erl_syntax:tuple([erl_syntax:atom(head),
                      erl_syntax:list(create_erl_syntax_proof_tree_seq(Shml_seq))]);
create_erl_syntax_proof_tree({nec, Act, Shml}) ->
    erl_syntax:tuple([erl_syntax:atom(nec),
                      erl_syntax:string(Act),
                      create_erl_syntax_proof_tree(Shml)]).

% manages the SHML_SEQ section of the proof_tree
-spec create_erl_syntax_proof_tree_seq(Shml_seq) -> erl_syntax:syntaxTree()
    when Shml_seq :: pf_shml_seq().
create_erl_syntax_proof_tree_seq([Shml]) ->
    [create_erl_syntax_proof_tree(Shml)];
create_erl_syntax_proof_tree_seq([Shml | Shml_seq]) ->
    [create_erl_syntax_proof_tree(Shml) | create_erl_syntax_proof_tree_seq(Shml_seq)].

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
    {ok, Old_History} = read_env(FileName),
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

% flattens each action to be a string
-spec fix_trace(List :: [list()]) -> List :: [list()].
fix_trace([]) ->
    [];
fix_trace([Head | Rest]) ->
    [lists:flatten(Head) | fix_trace(Rest)].
