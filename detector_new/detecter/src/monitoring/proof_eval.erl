-module(proof_eval).

-author("Jacob Deguara").

%%% Includes.
-include_lib("stdlib/include/assert.hrl").
-include_lib("syntax_tools/include/merl.hrl").

-include("log.hrl").

-export([convert_act_to_format/1, read_history/1, format_binary_to_history/1]).
-export([prove_property/2]).
-export([create_erl_syntax_proof_tree/1]).
-export([write_history/2]).
-export([get_action/1, fix_trace/1]).
-export([prove_monitor_test/2]).
-export([gen_action_test/2]).
-export([does_nothing/1]).

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

-type action() :: string().
-type trace() :: [action()].
-type history() :: [trace()].
-type proof_return_types() :: ff | undefined.

%%% ----------------------------------------------------------------------------
%%% Trace Format Functions.
%%% ----------------------------------------------------------------------------

%%% convert_act_to_format/1 takes an action from maxShml and Shmlnf
%%% the result should be {trace, '~~~', ACTION, {['~~~',...], ['~~~',...], ['~~~',...]}}
%%% A format of maxShml would have; {act,_,ACT} | {act,_,ACT,Clause} result in using the convert_act_to_format/2

-spec convert_act_to_format(Act) -> any() when Act :: any().
convert_act_to_format({fork, _, Var0, Var1, {_, _, Mod, Fun, _, Clause}}) ->
    {trace,
     clause_to_format(Var0),
     spawn,
     clause_to_format(Var1),
     Mod,
     Fun,
     clause_to_format(Clause)};
convert_act_to_format({init, _, Var0, Var1, {_, _, Mod, Fun, _, Clause}}) ->
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

%%% clause_to_format/1 takes a few different formats and just takes
%%% the important Names, lists or important information for the convertion

-spec clause_to_format(Any) -> any() when Any :: list() | map().
clause_to_format({_, _, '\'rec\''}) ->
    clause_to_format(rec);
clause_to_format({_, _, '\'no\''}) ->
    clause_to_format(no);
clause_to_format({_, _, '\'undefined\''}) ->
    clause_to_format(undefined);
clause_to_format({_, _, '\'check\''}) ->
    clause_to_format(check);
clause_to_format({_, _, '\'with\''}) ->
    clause_to_format(with);
clause_to_format({_, _, Something}) ->
    clause_to_format(Something);
clause_to_format([]) ->
    [];
clause_to_format([Head]) ->
    clause_to_format(Head);
clause_to_format([Head | Rest]) ->
    [clause_to_format(Head) | clause_to_format(Rest)];
clause_to_format({op, _, Op, Var1, Var2}) ->
    {Op, clause_to_format(Var1), clause_to_format(Var2)};
clause_to_format({op, _, Op, Var1}) ->
    {Op, clause_to_format(Var1)};
clause_to_format({clause, _, List1, List2, _}) ->
    {clause_to_format(List1), clause_to_format(List2)};
clause_to_format(Anything) ->
    Anything.

%%% ----------------------------------------------------------------------------
%%% Proof System Functions.
%%% ----------------------------------------------------------------------------

%%% prove_property/2 takes the Ast of a maxShml parser and the a history to
%%% prove a property given the history given.
%%% it will result in a no meaning the property is violated by the history of the system
%%% or undefined meaning the property has not been violated by the given history

-spec prove_property(Ast, History) -> no | undefined
    when Ast :: any(),
         History :: history().
prove_property(Ast, History) ->
    prove_property_form_seq(Ast,
                            History,
                            dict:new()).    %%% Adding the dictionary is important as it saves the max trees needed for recursion

%%% prove_property_form_seq/3 is used to Test each property in a given Ast tree
%%% given that one violates the property it will return a violation.
%%% each forms are of this format :: {form, _, _, Shml}

-spec prove_property_form_seq(List, History, RecRefDic) -> no | undefined
    when List :: [any()],
         History :: history(),
         RecRefDic :: dict:dict().
prove_property_form_seq(_List = [_Head = {form, _, _, Shml}], History, RecRefDic) ->
    prove_shml(Shml, History, RecRefDic);
prove_property_form_seq(_List = [_Head = {form, _, _, Shml} | Forms],
                        History,
                        RecRefDic) ->
    case prove_shml(Shml, History, RecRefDic) of
        no ->
            no;
        undefined ->
            prove_property_form_seq(Forms, History, RecRefDic)
    end.

%%% prove_shml/3 takes the Nodes and applies the correct logic to the given node
%%% Shml formats are ; {ff, _} | {tt, _} | {var, _, Name} | {max, _, _Var = {var, _, Name}, Shml}
%%% {nec, _, Act, Shml} | {'and', _, Shml1, Shml2} | {'or', _, Shml1, Shml2}
%%% 'ff' & 'tt' node will return themselves,
%%% 'max' node will save the tree in the dict with the Name as the key
%%% and 'var' will call that tree and recurse.
%%% 'nec' node holds a given action and will be followed through substituting from the history
%%% 'and' and 'or' nodes will do their respective logic

-spec prove_shml(Shml, History, RecRefDic) -> no | undefined
    when Shml :: any(),
         History :: history(),
         RecRefDic :: dict:dict().
prove_shml(_Node = {no, _}, _ENV, _) ->
    %?TRACE("Proving 'no' Leaf node ~p.~n", [_Node]),
    no;
prove_shml(_Node = {undefined, _}, _ENV, _) ->
    %?TRACE("Proving 'undefined' Leaf node ~p.~n", [_Node]),
    undefined;
prove_shml(_Var = {var, _, Name}, History, RecRefDic) ->
    Rec = dict:fetch(Name, RecRefDic),
    %?TRACE("Proving 'var' Leaf node ~p.~n Refrenced Tree:~p.~n", [_Var, Rec]),
    prove_shml(Rec, History, RecRefDic);
prove_shml(_Max = {rec, _, _Var = {var, _, Name}, Shml}, History, RecRefDic) ->
    %?TRACE("Proving 'rec' node~p.~n Dictionary Refrence ~p.~n", [_Max, _Var]),
    NewRecRefDic = dict:store(Name, Shml, RecRefDic),
    prove_shml(Shml, History, NewRecRefDic);
prove_shml(_And = {'and', _, Shml1, Shml2}, History, RecRefDic) ->
    %?TRACE("Proving 'and' node ~p.~n", [_And]),
    case prove_shml(Shml1, History, RecRefDic) of
        no ->
            no;
        undefined ->
            prove_shml(Shml2, History, RecRefDic)
    end;
prove_shml(_Or = {'or', _, Shml1, Shml2}, History, RecRefDic) ->
    %?TRACE("Proving 'or' node~p.~n", [_Or]),
    case prove_shml(Shml1, History, RecRefDic) of
        no ->
            prove_shml(Shml2, History, RecRefDic);
        undefined ->
            undefined
    end;
prove_shml(_Nec = {nec, _, Act, Shml}, History, RecRefDic) ->
    Result = sub(History, get_action(Act)),
    %?TRACE("Proving 'nec' node ~n Action:~p,~n History:~p,~n New_History ""~p,~n",[Act, History, Result]),
    prove_nec_analysis(Result, Shml, RecRefDic).

%%% prove_nec_analysis/3 given the resulting history if the history is;
%%% empty the execution is halted and returns tt meaning the result failes
%%% not empty the execution is continued with the new history

-spec prove_nec_analysis(History, NextShml, RecRefDic) -> proof_return_types()
    when History :: history(),
         NextShml :: any(),
         RecRefDic :: dict:dict().
prove_nec_analysis([], _, _) ->
    undefined;
prove_nec_analysis(New_History, NextShml, RecRefDic) ->
    prove_shml(NextShml, New_History, RecRefDic).

%%% sub/2 given a History and a Action if the given Trace in the History;
%%% has the same headAction as the Action -> it will return the RestTrace and continue
%%% does not have the same headAction as the Action -> it will continue with the next
%%% is an empty list -> it is ignored

-spec sub(History :: history(), Action :: trace()) -> history().
sub([], _) ->
    [];
sub([[] | RestHistory], Action) ->
    sub(RestHistory, Action);
sub([_HeadTrace = [HeadAction | RestAction] | RestHistory], Action)
    when HeadAction == Action ->
    [RestAction | sub(RestHistory, Action)];
sub([_HeadTrace = [HeadAction | _RestAction] | RestHistory], Action)
    when HeadAction =/= Action ->
    sub(RestHistory, Action).

%%% ----------------------------------------------------------------------------
%%% Synthesising functions.
%%% ----------------------------------------------------------------------------

%%% create_erl_syntax_proof_tree/1 given a Ast of maxShml it will be converted into a erl_syntax:syntaxTree()
%%% The given syntaxTree has ignored aspects of the format
%%% the ignored elements are conclusive toward the implementation of the proof system
%%% additionally the Act section of the tree is converted into a string to more efficient use

-spec create_erl_syntax_proof_tree(Ast) -> erl_syntax:syntaxTree() when Ast :: [any()].
create_erl_syntax_proof_tree(Ast) ->
    erl_syntax:list(create_erl_syntax_proof_tree_forms(Ast)).

%%% create_erl_syntax_proof_tree_forms/1 given a Ast of maxShml it will be converted into a erl_syntax:syntaxTree()
%%% this function will work based for the lists of forms only

-spec create_erl_syntax_proof_tree_forms(Ast) -> erl_syntax:syntaxTree()
    when Ast :: [any()].
create_erl_syntax_proof_tree_forms([]) ->
    [];
create_erl_syntax_proof_tree_forms([{form, _, _, Shml} | Forms]) ->
    [erl_syntax:tuple([erl_syntax:atom(form),
                       erl_syntax:atom(ignore),
                       erl_syntax:atom(ignore),
                       create_erl_syntax_proof_tree_shml(Shml)])
     | create_erl_syntax_proof_tree_forms(Forms)].

%%% create_erl_syntax_proof_tree_shml/1 given a Ast of maxShml it will be converted into a erl_syntax:syntaxTree()
%%% this function will work based for the Nodes of the tree from the forms.

-spec create_erl_syntax_proof_tree_shml(Ast) -> erl_syntax:syntaxTree() when Ast :: any().
create_erl_syntax_proof_tree_shml({no, _}) ->
    erl_syntax:tuple([erl_syntax:atom(no), erl_syntax:atom(ignore)]);
create_erl_syntax_proof_tree_shml({undefined, _}) ->
    erl_syntax:tuple([erl_syntax:atom(undefined), erl_syntax:atom(ignore)]);
create_erl_syntax_proof_tree_shml({var, _, Name}) ->
    erl_syntax:tuple([erl_syntax:atom(var), erl_syntax:atom(ignore), erl_syntax:atom(Name)]);
create_erl_syntax_proof_tree_shml({rec, _, Var, Shml}) ->
    erl_syntax:tuple([erl_syntax:atom(rec),
                      erl_syntax:atom(ignore),
                      create_erl_syntax_proof_tree_shml(Var),
                      create_erl_syntax_proof_tree_shml(Shml)]);
create_erl_syntax_proof_tree_shml({'and', _, Shml1, Shml2}) ->
    erl_syntax:tuple([erl_syntax:atom('and'),
                      erl_syntax:atom(ignore),
                      create_erl_syntax_proof_tree_shml(Shml1),
                      create_erl_syntax_proof_tree_shml(Shml2)]);
create_erl_syntax_proof_tree_shml({'or', _, Shml1, Shml2}) ->
    erl_syntax:tuple([erl_syntax:atom('or'),
                      erl_syntax:atom(ignore),
                      create_erl_syntax_proof_tree_shml(Shml1),
                      create_erl_syntax_proof_tree_shml(Shml2)]);
create_erl_syntax_proof_tree_shml({nec, _, Act, Shml}) ->
    erl_syntax:tuple([erl_syntax:atom(nec),
                      erl_syntax:atom(ignore),
                      erl_syntax:string(get_action(Act)),
                      create_erl_syntax_proof_tree_shml(Shml)]).

%%% ----------------------------------------------------------------------------
%%% History manipulation functions.
%%% ----------------------------------------------------------------------------

%%% read_history/1 takes a file name and returns either an error or the history from that file
%%% given the file's history is of this format '~~~;~~~;~~~;\n~~~;~~~;~~~;'
%%% the resultant history will seporate traces based on the \n
%%% and seporate actions from traces based on ;

-spec read_history(File :: file:filename()) ->
                      {ok, Env :: [list()]} | {error, Error :: error_info()}.
read_history(File) when is_list(File) ->
    case file:read_file(File) of
        {ok, Bytes} ->
            {ok, format_binary_to_history(binary_to_list(Bytes))};
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    end.

%%% format_binary_to_history/1 takes a byte list and returns the history from the list
%%% it tokenizes the list based on \n

-spec format_binary_to_history(Line) -> list() when Line :: [byte()].
format_binary_to_history(Line) ->
    format_binary_to_history2(string:tokens(Line, "\n")).

%%% format_binary_to_history/2 takes a Trace list and returns the history from the list
%%% it tokenizes the list based on ;

format_binary_to_history2([]) ->
    [];
format_binary_to_history2([Head | Rest]) ->
    [string:tokens(Head, ";") | format_binary_to_history2(Rest)].

%%% add_to_history/2 Takes a history and a new Trace and adds it to the history
%%% if the history already has the trace the trace is not added at the end of the history

-spec add_to_history(History, Trace) -> Result
    when History :: history(),
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

%%% write_history/2 takes a new Trace needed to be saved, and the file it will be saved in
%%% if the Trace is a replica in the history it will not be added and the history is returned
%%% if the Trace is new it is saved and added to the history, then the new history is returned

-spec write_history(New_Trace, FileName) -> New_History | {error, Error :: error_info()}
    when New_Trace :: trace(),
         FileName :: string(),
         New_History :: history().
write_history(New_Trace, FileName) ->
    case file:open(FileName, [append]) of
        {ok, Fd} ->
            case read_history(FileName) of
                {ok, Old_History} ->
                    New_History = add_to_history(Old_History, fix_trace(New_Trace)),
                    case ordsets:is_subset(Old_History, New_History)
                         andalso ordsets:is_subset(New_History, Old_History)
                    of
                        true ->
                            New_History;
                        false ->
                            file:write(Fd, [format_trace_for_writing(New_Trace), "\n"]),
                            New_History
                    end;
                {error, Reason} ->
                    throw({error, {?MODULE, Reason}})
            end;
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    end.

%%% format_trace_for_writing/1 takes a given trace and adds the ; between each action

-spec format_trace_for_writing([string()]) -> [string()].
format_trace_for_writing([]) ->
    [];
format_trace_for_writing([Head | Rest]) ->
    [Head, ";" | format_trace_for_writing(Rest)].

%%% get_trace/1 takes a string, a list or a Ast Act stucture from the maxShml and returns a string of the correct format.
%%% if the given element is an Act it will be converted into the correct stucture and returned as a string
%%% if the given element is a list it will be flattened into a string and returned
%%% if the given element is a string it will just be returned

-spec get_action(Act :: any() | list() | string()) -> string().
get_action(Act) when is_list(Act) ->
    Result = io_lib:char_list(Act),
    if Result ->
           Act;
       true ->
           lists:flatten(
               io_lib:format("~p", [lists:flatten(Act)]))
    end;
get_action(Act) ->
    Result = io_lib:char_list(Act),
    if Result ->
           Act;
       true ->
           lists:flatten(
               io_lib:format("~p", [convert_act_to_format(Act)]))
    end.

-spec fix_trace(Trace :: trace()) -> FixedTrace :: trace().
fix_trace([]) ->
    [];
fix_trace([HeadAction | Rest]) ->
    [lists:flatten(HeadAction) | fix_trace(Rest)].

%%% ----------------------------------------------------------------------------
%%% Test System
%%% ----------------------------------------------------------------------------

-spec prove_monitor_test(Monitor_File :: file:filename(),
                         History_File :: file:filename()) ->
                            no | undefined.
prove_monitor_test(Monitor_File, History_File) ->
    try gen_eval:parse_file(rechml_lexer, rechml_parser, Monitor_File) of
        {ok, AstP} ->
            try read_history(History_File) of
                {ok, History} ->
                    proof_eval:prove_property(AstP, History);
                {error, Reason} ->
                    throw({error, {?MODULE, Reason}})
            catch
                _:Reason:Stk ->
                    erlang:raise(error, Reason, Stk)
            end;
        {error, Reason} ->
            throw({error, {?MODULE, Reason}})
    catch
        _:Reason:Stk ->
            erlang:raise(error, Reason, Stk)
    end.

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

gen_action_form([], Fun) ->
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
