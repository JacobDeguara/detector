-module(rechml_eval).

-author("Jacob Deguara").

-prior_author("Duncan Paul Attard").

%%% Includes.
-include_lib("stdlib/include/assert.hrl").
-include_lib("syntax_tools/include/merl.hrl").

-include("log.hrl").

%%% Public API.
-export([compile/2, parse_string/1, parse_file/1]).
-export([convert_to_shml/1]).
-export([fix_list_to_shml/1, check_no_node_exists/1, merge_into_closed_list/2]).

%%-export([parse_transform/2, get_ast/3]). %% Check if these are being used.

%%% Types.
-export_type([formula_nf/0, formula_rec/0]).
-export_type([option/0, options/0]).
-export_type([directory/0]).
-export_type([line/0, error_description/0, error_info/0, errors/0, warnings/0]).

%%% Imports.

-import(proof_eval, [create_erl_syntax_proof_tree/1, convert_act_to_format/1]).
-import(gen_eval, [parse_file/3]).

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

-type af_rechml_no() :: {no, line()}.
-type af_rechml_undefined() :: {undefined, line()}.
-type af_rechml_var() :: {var, line(), atom()}.
-type af_rechml_rec() :: {rec, line(), af_rechml_var(), af_rechml()}.
-type af_rechml_or() :: {'or', line(), af_rechml(), af_rechml()}.
-type af_rechml_and() :: {'and', line(), af_rechml(), af_rechml()}.
-type af_rechml_nec() :: {nec, line(), af_act(), af_rechml()}.
-type af_rechml() ::
  af_rechml_no() |
  af_rechml_undefined() |
  af_rechml_var() |
  af_rechml_rec() |
  af_rechml_or() |
  af_rechml_and() |
  af_rechml_nec().
-type formula_rec() :: {form, line(), af_mfa(), af_rechml()}.
-type af_ff() :: {ff, line()}.
-type af_var() :: {var, line(), atom()}.
-type af_max() :: {max, line(), af_var(), af_shml()}.
-type af_n_and() :: {'and', line(), arity(), af_shml_seq()}.
-type af_nec() :: {nec, line(), af_act(), af_shml()}.
-type af_shml() :: af_ff() | af_var() | af_max() | af_n_and().
-type af_shml_seq() :: [af_nec()].
-type formula_nf() :: {form, line(), af_mfa(), af_rechml()}.
-type af_mfa() :: {mfa, line(), module(), atom(), arity(), erl_parse:abstract_clause()}.
-type af_fork_act() :: {fork, line(), af_rechml_var(), af_rechml_var(), af_mfa()}.
-type af_init_act() :: {init, line(), af_rechml_var(), af_rechml_var(), af_mfa()}.
-type af_exit_act() :: {exit, line(), af_rechml_var(), erl_parse:abstract_clause()}.
-type af_send_act() :: {send, line(), af_rechml_var(), erl_parse:abstract_clause()}.
-type af_recv_act() :: {recv, line(), af_rechml_var(), erl_parse:abstract_clause()}.
-type af_user_act() :: {user, line(), erl_parse:abstract_clause()}.
-type af_act() ::
  af_fork_act() |
  af_init_act() |
  af_exit_act() |
  af_send_act() |
  af_recv_act() |
  af_user_act().
-type tracename() :: [string() | integer()].

%%% ----------------------------------------------------------------------------
%%% Public API.
%%% ----------------------------------------------------------------------------

%% @doc Compiles the specified file containing one or more properties specified
%% in SHMLnf, and writes the executable monitor descriptions to file.
%%
%% {@params
%%  {@name File}
%%  {@desc The path where the file to compile resides.}
%%  {@name Opts}
%%  {@desc Compiler options.}
%% }
%%
%% {@par The following options are available:
%%       {@dl
%%         {@term `@{outdir, Dir@}'}
%%         {@desc The directory where the generated output monitor file should
%%                be written. Defaults to the current directory `.'.
%%         }
%%         {@term `v'}
%%         {@desc Inserts logging statements into the generated output monitor
%%                file. Only use for debugging purposes.
%%         }
%%         {@term `erl'}
%%         {@desc Instructs the compiler to output the generated monitor as
%%                Erlang source code rather than beam. Defaults to beam.
%%         }
%%       }
%% }
%% {@returns `ok' if compilation succeeds, `@{error, Reason@}' otherwise.}
-spec compile(File, Opts) -> ok | {error, Reason}
  when File :: file:filename(),
       Opts :: options(),
       Reason :: file:posix() | badarg | terminated.
compile(File, Opts) when is_list(Opts) ->
  try parse_file(File) of
    {ok, ASTrechml} ->
      % Convert recHML AST to a shml AST
      Module = list_to_atom(filename:basename(File, ?EXT_HML)),

      ASTshml = convert_to_shml(ASTrechml),
      % Synthesize monitor from parsed syntax tree in the form of an Erlang
      % syntax tree and write result to file as Erlang source or beam code.
      write_monitor(create_module(ASTshml, ASTrechml, Module, Opts), File, Opts);
    {error, Reason} ->
      throw({error, {?MODULE, Reason}})
  catch
    _:Reason:Stk ->
      erlang:raise(error, Reason, Stk)
  end.

%% @doc Parses the specified string containing one or more properties specified
%% in SHMLnf.
%%
%% {@params
%%   {@name String}
%%   {@desc The string to parse.}
%% }
%% {@par See {@link parse_string/1} for details on SHMLnf specification format.}
%%
%% {@returns The syntax tree for the properties specified in SHMLnf.}
-spec parse_string(String) ->
                    {ok, Ast :: [formula_rec()]} | {error, Error :: error_info()}
  when String :: string().
parse_string(String) when is_list(String) ->
  case rechml_lexer:string(String) of
    {ok, [], _} ->
      {ok, skip};
    {ok, Tokens, _} ->
      case rechml_parser:parse(Tokens) of
        {ok, Ast} ->
          {ok, Ast};
        {error, Error = {_, _, _}} ->
          % Error in parsing.
          {error, Error}
      end;
    {error, Error = {_, _, _}, _} ->
      % Error in lexical analysis.
      {error, Error}
  end.

-spec parse_file(File :: file:filename()) ->
                  {ok, Ast :: [formula_rec()]} | {error, Error :: error_info()}.
parse_file(File) when is_list(File) ->
  case file:read_file(File) of
    {ok, Bytes} ->
      parse_string(binary_to_list(Bytes));
    {error, Reason} ->
      throw({error, {?MODULE, Reason}})
  end.

%%% ----------------------------------------------------------------------------
%%% Compiler option functions.
%%% ----------------------------------------------------------------------------

%% @private Configures the Erlang compiler options used to generate the beam
%% code file.
-spec compile_opts(Opts :: options()) -> CompileOpts :: [compile:option()].
compile_opts(Opts) ->
  %%  [{i, include_opt(Opts)}, {i, out_dir_opt(Opts)} | ?COMPILER_OPTS].
  [{i, opts:out_dir_opt(Opts)} | ?COMPILER_OPTS].

%%% ----------------------------------------------------------------------------
%%% ASTshml convertion tool functions.
%%% ----------------------------------------------------------------------------

-spec convert_to_shml(ASTrechml :: [formula_rec()]) -> ASTshml :: [formula_nf()].
convert_to_shml([]) ->
  [];
convert_to_shml([{form, _line, MFA, SHMLrec} | Forms]) ->
  [{form, _line, MFA, {'and', 0, 1, [convert_to_shml_start(SHMLrec)]}}
   | convert_to_shml(Forms)].

convert_to_shml_start({no, _line}) ->
  {ff, 1};
convert_to_shml_start({undefined, _line}) ->
  {tt, 2};
convert_to_shml_start({var, _line, Name}) ->
  {var, 3, Name};
convert_to_shml_start({rec, _line, Var, Shml}) ->
  {max, 4, Var, convert_to_shml_start(Shml)};
convert_to_shml_start(HML = {'and', _line, _, _}) ->
  {'and', 5, 0, fix_list_to_shml(lists:flatten(convert_to_shml_and(HML)))};
convert_to_shml_start(HML = {'or', _line, _, _}) ->
  {'and', 6, 0, fix_list_to_shml(lists:flatten(convert_to_shml_and(HML)))};
convert_to_shml_start({nec, _line, Act, Shml}) ->
  case convert_to_shml_start(Shml) of
    FF_node = {ff, _} ->
      {nec, 7, Act, FF_node};
    Var_node = {var, _, _} ->
      {nec, 7, Act, Var_node};
    Max_node = {max, _, _, _} ->
      {nec, 7, Act, Max_node};
    Any ->
      {nec, 7, Act, {'and', 8, 1, [Any]}}
  end.

% makes list
convert_to_shml_and({no, _line}) ->
  [{ff, 9}];
convert_to_shml_and({ff, _line}) ->
  [{ff, 9.5}];
convert_to_shml_and({undefined, _line}) ->
  [{tt, 10}];
convert_to_shml_and({tt, _line}) ->
  [{tt, 10.5}];
convert_to_shml_and({var, _line, Name}) ->
  [{var, 11, Name}];
convert_to_shml_and({rec, _line, Var, Shml}) ->
  [{max, 12, Var, Shml}];
convert_to_shml_and({max, _line, Var, Shml}) ->
  [{max, 12.5, Var, Shml}];
convert_to_shml_and({'and', _line, Shml1, Shml2}) ->
  [convert_to_shml_and(Shml1) | convert_to_shml_and(Shml2)];
convert_to_shml_and({'or', _line, Shml1, Shml2}) ->
  [convert_to_shml_and(Shml1) | convert_to_shml_and(Shml2)];
convert_to_shml_and({nec, _line, Act, Shml}) ->
  [{nec, 13, Act, Shml}].

fix_list_to_shml(List) ->
  % checks if a single no node exists
  case check_no_node_exists(List) of
    true ->
      {ff, 14};
    false ->
      % checks if a single var node exists
      case check_var_node_exists(List) of
        {var, _line, Name} ->
          {var, 15, Name};
        false ->
          % removes all other nodes other then the nec nodes
          case fix_list_to_nec_nodes_only(List) of
            [] ->
              {ff, 16};
            NewList ->
              merge_into_closed_list(NewList, [])
          end
      end
  end.

% not working ?
check_no_node_exists([]) ->
  false;
check_no_node_exists([{ff, _line} | _]) ->
  true;
check_no_node_exists([{no, _line} | _]) ->
  true;
check_no_node_exists([_ | Next]) ->
  check_no_node_exists(Next).

check_var_node_exists([]) ->
  false;
check_var_node_exists([VAR = {var, _line, _} | _]) ->
  VAR;
check_var_node_exists([_ | Next]) ->
  check_var_node_exists(Next).

fix_list_to_nec_nodes_only([]) ->
  [];
fix_list_to_nec_nodes_only([NEC = {nec, _line, _, _} | Next]) ->
  [NEC | fix_list_to_nec_nodes_only(Next)];
fix_list_to_nec_nodes_only([_ | Next]) ->
  fix_list_to_nec_nodes_only(Next).

compare_nec_nodes({nec, _, Act1, _}, {nec, _, Act2, _}) ->
  proof_eval:get_action(Act1) == proof_eval:get_action(Act2).

already_in_saved_list([], _) ->
  false;
already_in_saved_list([NecR | Next], NecA) ->
  case compare_nec_nodes(NecR, NecA) of
    true ->
      true;
    false ->
      already_in_saved_list(Next, NecA)
  end.

find_repeating_elements([], _) ->
  [];
find_repeating_elements([NEC = {nec, _line, _, Shml} | Next], NecR) ->
  case compare_nec_nodes(NEC, NecR) of
    true ->
      [Shml | find_repeating_elements(Next, NecR)];
    false ->
      find_repeating_elements(Next, NecR)
  end.

merge_into_closed_list([], List) ->
  List;
merge_into_closed_list(Current_List = [NEC = {nec, _line, Act, _} | Next], List) ->
  case already_in_saved_list(List, NEC) of
    true ->
      merge_into_closed_list(Next, List);
    false ->
      case fix_list_to_shml(expand_list(find_repeating_elements(Current_List, NEC))) of
        FF_node = {ff, _} ->
          NewNec = {nec, 17, Act, FF_node},
          merge_into_closed_list(Next, [NewNec | List]);
        Var_node = {var, _, _} ->
          NewNec = {nec, 17, Act, Var_node},
          merge_into_closed_list(Next, [NewNec | List]);
        Max_node = {max, _, _, _} ->
          NewNec = {nec, 17, Act, Max_node},
          merge_into_closed_list(Next, [NewNec | List]);
        Any ->
          NewNec = {nec, 17, Act, {'and', 8, 1, Any}},
          merge_into_closed_list(Next, [NewNec | List])
      end
  end.


expand_list([]) -> [];
expand_list([{'and', _line, Shml1, Shml2}|Next]) -> [expand_list(Shml1),expand_list(Shml2)|expand_list(Next)];
expand_list([{'or', _line, Shml1, Shml2}|Next]) -> [expand_list(Shml1),expand_list(Shml2)|expand_list(Next)];
expand_list([Any|Next]) -> [Any|expand_list(Next)];
expand_list(Any) -> Any.



%%% ----------------------------------------------------------------------------
%%% AST manipulation functions functions.
%%% ----------------------------------------------------------------------------

%% @private Generates the syntax tree describing the monitor module including
%% the module header, function exports and function describing monitor bodies.
%% The function is employed by the tracing mechanism implementations (see
%% {@link tracer} and {@link weaver}) to determine whether a monitor needs to
%% be instrumented or otherwise. This, it does via standard Erlang pattern
%% matching on MFA patterns specified by the user.
-spec create_module(ASTshml, ASTrechml, Module, Opts) ->
                     Forms :: [erl_parse:abstract_form()]
  when ASTshml :: [formula_nf()],
       ASTrechml :: [formula_rec()],
       Module :: module(),
       Opts :: options().
create_module(ASTshml, ASTrechml, Module, Opts) ->
  % Create monitor file meta information.
  MfaSpec = ?MFA_SPEC,
  {{YY, MM, DD}, {HH, Mm, SS}} = calendar:local_time(),
  Date = io_lib:format("~4B/~2B/~2..0B ~2..0B:~2..0B:~2..0B", [YY, MM, DD, HH, Mm, SS]),

  % Generate module base and attribute meta information with additonal imports.
  Forms =
    ?Q(["-module('@Module@').",
        "-author(\"detectEr\").",
        "-generated('@Date@').",
        "-export(['@MfaSpec@'/1]).",
        "-import(proof_eval,[write_history/2])."]),

  %% Create monitor module.
  Fun =
    erl_syntax:function(
      erl_syntax:atom(?MFA_SPEC), visit_forms(ASTshml, Opts, ASTshml, ASTrechml)),
  erl_syntax:revert_forms(Forms ++ [Fun]).

%% @private Visits SHMLnf formula nodes and generates the corresponding syntax
%% tree describing one monitor (i.e. one formula is mapped to one monitor).
-spec visit_forms(Forms, Opts, ASTshml, ASTrechml) -> Forms :: [erl_syntax:syntaxTree()]
  when Forms :: [formula_nf()],
       Opts :: options(),
       ASTshml :: [formula_nf()],
       ASTrechml :: [formula_rec()].
visit_forms([], Opts, _, _) ->
  % Generate catchall function clause pattern that matches Mod:Fun(Args) pattern
  % to return undefined. This is the case when no monitor should be attached to
  % said MFA.
  case opts:verbose_opt(Opts) of
    true ->
      % Create verbose function clause body to include logging information.
      MfaVar = erl_syntax:variable('_Mfa'),
      Log = create_log("Skipping instrumentation for MFA pattern '~p'.~n", [MfaVar], no),
      [erl_syntax:clause([MfaVar], none, [Log, erl_syntax:atom(undefined)])];
    _ ->
      [erl_syntax:clause([erl_syntax:underscore()], none, [erl_syntax:atom(undefined)])]
  end;
visit_forms([{form, _, {mfa, _, Mod, Fun, _, Clause}, Shml} | Forms],
            Opts,
            ASTshml,
            ASTrechml) ->
  % Generate TraceName Number to refrence new names for Trace identification.
  TraceNameNum = 1,

  % Create The First Empty List Trace
  TraceRecorder =
    erl_syntax:match_expr(
      erl_syntax:variable(traceNameFlatten(TraceNameNum)), erl_syntax:list([], none)),

  % Create the FileName the Trace & History will be saved in
  FileName =
    erl_syntax:match_expr(
      erl_syntax:variable("FileName"),
      erl_syntax:string(
        io_lib:format("~p_history.txt", [Mod]))),

  % Generate the ProofTree for proofing later and save it as code int the monitor
  Proof_tree =
    erl_syntax:match_expr(
      erl_syntax:variable("Proof_tree"), proof_eval:create_erl_syntax_proof_tree(ASTrechml)),

  % Unpack patterns and guard from MFA clause. The clause patterns are the
  % argument patterns used in the Mod:Fun(Args) invocation: these must be
  % encoded as {Mod, Fun, Args} tuples to be used as a singular pattern in
  % the different clauses of the mon_spec function. Meanwhile, the guard from
  % MFA clause is used as is as a guard for the clause of mon_spec.
  Patterns = erl_syntax:clause_patterns(Clause),
  Guard = erl_syntax:clause_guard(Clause),

  % Create {Mod, Fun, Args} tuple. Mod and Fun are the atoms taken as is from
  % the MFA definition; Args are provided as a pattern list inside the tuple.
  MfaTuple =
    erl_syntax:tuple([erl_syntax:atom(Mod), erl_syntax:atom(Fun), erl_syntax:list(Patterns)]),

  % Create the body for current function clause, consisting of a singular tagged
  % pair enclosing the monitor encoding as one anonymous function.
  Body =
    erl_syntax:tuple([erl_syntax:atom(ok),
                      erl_syntax:block_expr([TraceRecorder,
                                             FileName,
                                             Proof_tree,
                                             visit_shml(Shml, Opts, TraceNameNum)])]),

  % Return function clause for {Mod, Fun, Args} with monitor implementation.
  case opts:verbose_opt(Opts) of
    true ->
      MfaVar = erl_syntax:variable('_Mfa'),
      Log = create_log("Instrumenting monitor for MFA pattern '~p'.~n", [MfaVar], 'end'),
      Body0 =
        erl_syntax:tuple([erl_syntax:atom(ok),
                          erl_syntax:block_expr([TraceRecorder,
                                                 FileName,
                                                 Proof_tree,
                                                 Log,
                                                 visit_shml(Shml, Opts, TraceNameNum)])]),
      Match = erl_syntax:match_expr(MfaVar, MfaTuple),
      [erl_syntax:clause([Match], Guard, [Body0]) | visit_forms(Forms,
                                                                Opts,
                                                                ASTshml,
                                                                ASTrechml)];
    _ ->
      [erl_syntax:clause([MfaTuple], Guard, [Body]) | visit_forms(Forms,
                                                                  Opts,
                                                                  ASTshml,
                                                                  ASTrechml)]
  end.

%%  [erl_syntax:clause([MfaTuple], Guard, [Body]) | visit_forms(Forms, Opts)].

%% @private Visits a SHMLnf term and generates the corresponding syntax tree
%% that describes the monitor equivalent construct. The following are translated
%% thus:
%% {@ul
%%   {@item A SHMLnf falsity is translated to monitor verdict `no';}
%%   {@item A SHMLnf recursive variable is translated to a monitor recursive
%%          variable;
%%   }
%%   {@item A SHMLnf maximal fix-point is translated to a recursive monitor
%%          construct;
%%   }
%%   {@item A SHMLnf n-ary conjunction is translated to a monitor n-ary choice.}
%% }
-spec visit_shml(Shml, Opts, TraceNameNum) -> erl_syntax:syntaxTree()
  when Shml :: af_shml(),
       Opts :: options(),
       TraceNameNum :: integer().
visit_shml(_Node = {ff, _}, Opts, TraceNameNum) ->
  %?TRACE("Visiting 'ff' node ~p.", [_Node]),
  % Create atom 'no' denoting the rejection monitoring verdict. This corresponds
  % to the SHMLnf violation verdict 'ff'.
  % History = proof_eval:write_history(Trace5,FileName)
  % proof_eval:prove_property(Proof_tree,History)
  % an Error has occuered during testing this function fixes that issue.
  % the Issue was that the Trace list was defaulting a none string variant which
  % caused issues with the next part.
  % Run the function that handles the given new Trace, saves it to history and returns new History to be used.
  Writing =
    erl_syntax:match_expr(
      erl_syntax:variable("History"),
      erl_syntax:application(
        erl_syntax:atom(proof_eval),
        erl_syntax:atom(write_history),
        [erl_syntax:variable(traceNameFlatten(TraceNameNum)), erl_syntax:variable("FileName")])),

  % Run the Prove Property function that will determine weather the property has been violated
  Verdict =
    erl_syntax:application(
      erl_syntax:atom(proof_eval),
      erl_syntax:atom(prove_property),
      [erl_syntax:variable("Proof_tree"), erl_syntax:variable("History")]),

  case opts:verbose_opt(Opts) of
    true ->
      Log = create_log("Reached verdict '~p'.~n", [Verdict], no),
      Log2 =
        create_log("<< Resulting History ~p >>~n",
                   [erl_syntax:variable("History")],
                   'end'), % who the history
      erl_syntax:block_expr([Writing, Log2, Log]);
    _ ->
      erl_syntax:block_expr([Writing, Verdict])
  end;
visit_shml(Var = {var, _, Name}, Opts, TraceNameNum) ->
  %?TRACE("Visiting 'var' node ~p.", [Var]),
  % Create function application denoting the recursive call the monitor performs
  % when it reaches the recursive variable. This corresponds to the SHMLns
  % recursion variable.
  case opts:verbose_opt(Opts) of
    true ->
      Log = create_log("Unfolding rec. var. ~p.~n", [erl_syntax:atom(Name)], var),
      erl_syntax:block_expr([Log,
                             erl_syntax:application(Var,
                                                    [erl_syntax:variable(traceNameFlatten(TraceNameNum))])]);
    _ ->
      erl_syntax:application(Var, [erl_syntax:variable(traceNameFlatten(TraceNameNum))])
  end;
visit_shml(_Node = {max, _, Var = {var, _, _}, Shml}, Opts, TraceNameNum) ->
  %?TRACE("Visiting 'max' node ~p.", [_Node]),
  % Create function clause containing monitor body.
  Clause =
    erl_syntax:clause([erl_syntax:variable(traceNameFlatten(TraceNameNum + 1))],
                      none,
                      [visit_shml(Shml, Opts, TraceNameNum + 1)]),

  % Create named anonymous function whose name provides the monitor with a
  % handle that allows it to call itself recursively. This corresponds to the
  % SHMLnf maximal fix-point operator. The named anonymous function is applied
  % immediately as soon as it is created, thereby executing the very first
  % recursion unfolding immediately.
  Fun = erl_syntax:named_fun_expr(Var, [Clause]),
  FunApplication =
    erl_syntax:application(Fun, [erl_syntax:variable(traceNameFlatten(TraceNameNum))]);
visit_shml(_Node = {'or', _, _, ShmlSeq}, Opts, TraceNameNum) when is_list(ShmlSeq) ->
  %?TRACE("Visiting 'and_~w' node ~p.", [length(ShmlSeq), _Node]),
  % Create function clauses for all conjuncts in the n-ary conjunction. These
  % will be combined to form the function that permits a choice through its
  % guards.
  Clauses = visit_shml_seq(ShmlSeq, Opts, TraceNameNum),

  % Create catch-all function clause to which any unrecognized pattern will
  % default. The body of this function returns 'end', denoting the monitor
  % inconclusive verdict.
  CatchAllClause =
    case opts:verbose_opt(Opts) of
      true ->
        % Create verbose function clause body to include logging information.
        EventVar = erl_syntax:variable('_E'),
        Log = create_log("Reached verdict 'end' on event ~p.~n", [EventVar], 'end'),
        Body = erl_syntax:block_expr([Log, erl_syntax:atom('end')]),
        erl_syntax:clause([EventVar], none, [Body]);
      _ ->
        erl_syntax:clause([erl_syntax:underscore()], none, [erl_syntax:atom('end')])
    end,

  % Create anonymous function combining all clauses (including catch-all)
  % denoting all possible branches that the monitor may follow. Each branch
  % (encoded as a function clause) corresponds to the action of each top
  % necessity specified in the SHMLnf n-ary conjunction.
  erl_syntax:fun_expr(Clauses ++ [CatchAllClause]);
visit_shml(_Node = {'and', _, _, ShmlSeq}, Opts, TraceNameNum) when is_list(ShmlSeq) ->
  %?TRACE("Visiting 'and_~w' node ~p.", [length(ShmlSeq), _Node]),
  % Create function clauses for all conjuncts in the n-ary conjunction. These
  % will be combined to form the function that permits a choice through its
  % guards.
  Clauses = visit_shml_seq(ShmlSeq, Opts, TraceNameNum),

  % Create catch-all function clause to which any unrecognized pattern will
  % default. The body of this function returns 'end', denoting the monitor
  % inconclusive verdict.
  CatchAllClause =
    case opts:verbose_opt(Opts) of
      true ->
        % Create verbose function clause body to include logging information.
        EventVar = erl_syntax:variable('_E'),
        Log = create_log("Reached verdict 'end' on event ~p.~n", [EventVar], 'end'),
        Body = erl_syntax:block_expr([Log, erl_syntax:atom('end')]),
        erl_syntax:clause([EventVar], none, [Body]);
      _ ->
        erl_syntax:clause([erl_syntax:underscore()], none, [erl_syntax:atom('end')])
    end,

  % Create anonymous function combining all clauses (including catch-all)
  % denoting all possible branches that the monitor may follow. Each branch
  % (encoded as a function clause) corresponds to the action of each top
  % necessity specified in the SHMLnf n-ary conjunction.
  erl_syntax:fun_expr(Clauses ++ [CatchAllClause]).

%% @private Visits the list of conjuncts node (see {@link visit_shml/2}) and
%% generates a list of syntax trees for function clauses denoting one or more
%% monitor action prefixes that the monitor then chooses from. The choice
%% corresponds to the SHMLnf 'and', and is implemented via standard Erlang
%% function clause pattern matching.
%%
%% Note: The specification of the SHMLnf grammar guarantees that each element in
%% the list of conjuncts is a necessity (i.e., all sub-formulas are guarded).
-spec visit_shml_seq(ShmlSeq, Opts, TraceNameNum) -> [erl_syntax:syntaxTree()]
  when ShmlSeq :: af_shml_seq(),
       Opts :: options(),
       TraceNameNum :: integer().
visit_shml_seq([Nec], Opts, TraceNameNum) ->
  [visit_nec(Nec, Opts, TraceNameNum)];
visit_shml_seq([Nec | ShmlSeq], Opts, TraceNameNum) ->
  [visit_nec(Nec, Opts, TraceNameNum) | visit_shml_seq(ShmlSeq, Opts, TraceNameNum)].

%% @private Visits the SHMLnf necessity 'nec' node and generates the syntax tree
%% for a function clause describing the monitor action prefix. The clause is
%% combined together with other such clauses (resulting from other necessities)
%% under one function that describes a monitor choice between said necessities.
-spec visit_nec(Nec, Opts, TraceNameNum) -> erl_syntax:syntaxTree()
  when Nec :: af_nec(),
       Opts :: options(),
       TraceNameNum :: integer().
visit_nec(_Node = {nec, _, Act, Shml}, Opts, TraceNameNum) ->
  %?TRACE("Visiting 'nec' node ~p.", [_Node]),
  % Create monitor body.
  Body = visit_shml(Shml, Opts, TraceNameNum + 1),

  % Visit action to obtain clause patterns and guard. In this particular case,
  % the list of patterns will only contain the trace pattern; meanwhile the
  % guard on said pattern is used as is to construct the clause pattern for the
  % function.
  {Patterns, Guard} = visit_act(Act),

  % Takes the pevious trace name and appends it to the new trace name
  RecordTrace =
    erl_syntax:match_expr(
      erl_syntax:variable(traceNameFlatten(TraceNameNum + 1)),
      erl_syntax:application(
        erl_syntax:atom(lists),
        erl_syntax:atom(append),
        [erl_syntax:variable(traceNameFlatten(TraceNameNum)),
         erl_syntax:list([erl_syntax:string(
                            io_lib:format("~p", [proof_eval:convert_act_to_format(Act)]))])])),

  % Create function clause consisting of exactly one pattern and guard. The
  % pattern matches the singular trace event that is to be processed; the guard
  % allows refined matching to be performed dynamically whilst the function
  % clause is being evaluated at runtime. The pattern and guard constructs
  % correspond to the SHMLns modal necessity.
  case opts:verbose_opt(Opts) of
    true ->
      % Create verbose function clause body to include logging information.
      EventVar = erl_syntax:variable('_E'),
      Log = create_log("Analyzing event ~p.~n", [EventVar], prf),
      Match = erl_syntax:match_expr(EventVar, hd(Patterns)),
      erl_syntax:clause([Match], Guard, [RecordTrace, Log, Body]);
    _ ->
      erl_syntax:clause(Patterns, Guard, [RecordTrace, Body])
  end.

%% @private Visits the action 'act' node to extract the pattern and guard from
%% the abstract syntax clause. The specification of the SHMLnf grammar restricts
%% clauses to consist of exactly one Erlang pattern with an empty body.
-spec visit_act(Act) ->
                 {Patterns :: [erl_syntax:syntaxTree()], Guard :: erl_syntax:syntaxTree()}
  when Act :: af_act().
%%  Act :: term().
visit_act({fork, _, Var0, Var1, {mfa, _, Mod, Fun, _, Clause}}) ->
  Patterns = erl_syntax:clause_patterns(Clause),
  Guard = erl_syntax:clause_guard(Clause),

  Mfa =
    erl_syntax:tuple([erl_syntax:atom(Mod), erl_syntax:atom(Fun), erl_syntax:list(Patterns)]),
  Pattern =
    erl_syntax:tuple([erl_syntax:atom(trace), Var0, erl_syntax:atom(spawn), Var1, Mfa]),
  {[Pattern], Guard};
visit_act({init, _, Var0, Var1, {mfa, _, Mod, Fun, _, Clause}}) ->
  Patterns = erl_syntax:clause_patterns(Clause),
  Guard = erl_syntax:clause_guard(Clause),

  Mfa =
    erl_syntax:tuple([erl_syntax:atom(Mod), erl_syntax:atom(Fun), erl_syntax:list(Patterns)]),
  Pattern =
    erl_syntax:tuple([erl_syntax:atom(trace), Var0, erl_syntax:atom(spawned), Var1, Mfa]),
  {[Pattern], Guard};
visit_act({exit, _, Var, Clause}) ->
  [Pattern] = erl_syntax:clause_patterns(Clause),
  Pattern0 =
    erl_syntax:tuple([erl_syntax:atom(trace), Var, erl_syntax:atom(exit), Pattern]),
  {[Pattern0], erl_syntax:clause_guard(Clause)};
visit_act({send, _, Var1, Var2, Clause}) ->
  [Pattern] = erl_syntax:clause_patterns(Clause),
  Pattern0 =
    erl_syntax:tuple([erl_syntax:atom(trace), Var1, erl_syntax:atom(send), Pattern, Var2]),
  {[Pattern0], erl_syntax:clause_guard(Clause)};
visit_act({recv, _, Var, Clause}) ->
  [Pattern] = erl_syntax:clause_patterns(Clause),
  Pattern0 =
    erl_syntax:tuple([erl_syntax:atom(trace), Var, erl_syntax:atom('receive'), Pattern]),
  {[Pattern0], erl_syntax:clause_guard(Clause)};
visit_act({user, _, Clause}) ->
  {erl_syntax:clause_patterns(Clause), erl_syntax:clause_guard(Clause)}.

%% @private Returns the syntax tree for a function call that creates a log
%% statement. The type argument determines how the log statement is rendered
%% on the standard output.
-spec create_log(Format, Args, Type) -> Call :: erl_syntax:syntaxTree()
  when Format :: string(),
       Args :: [erl_syntax:syntaxTree()],
       Type :: no | prf | var | 'end'.
create_log(Format, Args, Type) ->
  Format0 = color_log(["*** [~w] ", Format], Type),
  SelfCall = erl_syntax:application(none, erl_syntax:atom(self), []),
  erl_syntax:application(
    erl_syntax:atom(io),
    erl_syntax:atom(format),
    [erl_syntax:string(Format0), erl_syntax:list([SelfCall | Args])]).

%% @private Applies ASCII colors to the specified log message depending on the
%% Type of monitor construct. Type argument determines how the log statement is
%% rendered on the standard output.
-spec color_log(Log, Type) -> Log0 :: string()
  when Log :: iolist(),
       Type :: no | prf | var | 'end'.
color_log(Log, no) ->
  lists:flatten(["\e[1m\e[31m", Log, "\e[0m"]); % Bold red.
color_log(Log, prf) ->
  lists:flatten(["\e[37m", Log, "\e[0m"]); % White.
color_log(Log, var) ->
  lists:flatten(["\e[36m", Log, "\e[0m"]); % Cyan.
color_log(Log, 'end') ->
  lists:flatten(["\e[1m\e[33m", Log, "\e[0m"]); % Bold yellow.
color_log(Log, _) ->
  lists:flatten(Log).

%%% ----------------------------------------------------------------------------
%%% Code generating functions.
%%% ----------------------------------------------------------------------------

%% @private Writes the monitor code (specified in the form of a syntax tree) to
%% file. The options dictate the type of output produced: by default, beam is
%% produced; if however the 'erl' switch is specified, Erlang source code is
%% produced instead. The option 'v' determines whether the monitor generated
%% includes in it logging statements used for debugging purposes.
-spec write_monitor(Ast, File, Opts) -> ok | {error, Reason}
  when Ast :: [erl_syntax:syntaxTree()],
       File :: file:filename(),
       Opts :: options(),
       Reason :: file:posix() | badarg | terminated.
write_monitor(Ast, File, Opts) ->
  % Create base filename, taking into account the output directory specified in
  % the compiler options.
  FileBase = filename:join([opts:out_dir_opt(Opts), filename:basename(File, ?EXT_HML)]),

  % Open file for writing and write Erlang source or beam code depending on
  % the specified compiler options.
  % Open file for writing. File extension depends on specified compiler options.
  {ok, IoDev} =
    file:open(FileBase
              ++ case opts:erl_opt(Opts) of
                   true ->
                     ?EXT_ERL;
                   _ ->
                     ?EXT_BEAM
                 end,
              [write]),

  % Write monitor Erlang or beam source code depending on specified compiler
  % options.
  case opts:erl_opt(Opts) of
    true ->
      write_erl(IoDev, Ast, File, compile_opts(Opts));
    _ ->
      write_beam(IoDev, Ast, File, compile_opts(Opts))
  end,

  % Close file.
  file:close(IoDev).

%% @private Translates the given Erlang syntax tree to source code and writes
%% it to the specified IO device. Errors and warnings are reported accordingly.
%% No source code is generated if errors are found.
-spec write_erl(IoDev, Ast, File, CompileOpts) ->
                 {ok, Warnings :: warnings()} | {error, Errors :: errors(), Warnings :: warnings()}
  when IoDev :: file:io_device(),
       Ast :: [erl_syntax:syntaxTree()],
       File :: file:filename(),
       CompileOpts :: [compile:option()].
write_erl(IoDev, Ast, File, CompileOpts) ->
  % Lint Erlang syntax tree and report any errors or warnings found to standard
  % output. If linting completes without errors, write sources code into a .erl
  % file.
  case erl_lint:module(Ast, File, CompileOpts) of
    Ok = {ok, Warnings} ->
      show_warnings(Warnings),
      list_erl(IoDev, Ast),
      Ok;
    Error = {error, Errors, Warnings} ->
      show_errors(Errors),
      show_warnings(Warnings),
      Error
  end.

%% @private Compiles the given Erlang syntax tree to beam and writes it to the
%% specified IO device. Errors and warnings are reported accordingly. No beam
%% code is generated if errors are found.
-spec write_beam(IoDev, Ast, File, CompileOpts) ->
                  {ok, Warnings :: warnings()} | {error, Errors :: errors(), Warnings :: warnings()}
  when IoDev :: file:io_device(),
       Ast :: [erl_syntax:syntaxTree()],
       File :: file:filename(),
       CompileOpts :: [compile:option()].
write_beam(IoDev, Ast, File, CompileOpts) ->
  % Compile Erlang syntax tree and report any errors or warnings found to
  % standard output. If compilation completes without errors, write object code
  % into a .beam file.
  case compile:forms(Ast, [{source, File} | CompileOpts]) of
    Ok = {ok, _, Binary, Warnings} ->
      show_warnings(Warnings),
      list_beam(IoDev, Binary),
      Ok;
    Error = {error, Errors, Warnings} ->
      show_errors(Errors),
      show_warnings(Warnings),
      Error
  end.

%% @private Converts the list of Erlang forms into formatted Erlang code and
%% writes them to the specified IO device.
-spec list_erl(IoDev, Forms) -> ok
  when IoDev :: file:io_device(),
       Forms :: [erl_parse:abstract_form()].
list_erl(_, []) ->
  ok;
list_erl(IoDev, [Form | Forms]) ->
  io:put_chars(IoDev, erl_pp:form(Form)),
  list_erl(IoDev, Forms).

%% @private Writes the binary as it to the specified IO device.
-spec list_beam(IoDev, Beam) -> ok | {error, Reason}
  when IoDev :: file:io_device(),
       Beam :: binary(),
       Reason :: file:posix() | badarg | terminated.
list_beam(IoDev, Beam) ->
  file:write(IoDev, Beam).

%%% ----------------------------------------------------------------------------
%%% Error handling and reporting functions.
%%% ----------------------------------------------------------------------------

%% @private Reports the specified error message on standard output. Currently
%% only used for lexical analysis- and parsing-related errors.
-spec show_error(File :: file:filename(), Error :: error_info()) -> ok.
show_error(File, Error) ->
  {Line, Desc} = format_error(Error),
  io:format("~s:~b: ~s~n", [File, Line, Desc]).

%% @private Reports the specified list of error messages on standard output.
%% Handles errors emitted by Erlang {@link compiler} and {@link erl_lint}
%% modules.
-spec show_errors(Errors :: errors()) -> ok.
show_errors([]) ->
  ok;
show_errors([{File, ErrorsInfos}]) ->
  lists:map(fun(ErrorInfo) ->
               {Line, Desc} = format_error(ErrorInfo),
               io:format("~s:~b: ~s~n", [File, Line, Desc])
            end,
            ErrorsInfos),
  ok;
show_errors(_) ->
  ok.

%% @private Reports the specified list of warning messages on standard output.
%% Handles warnings emitted by Erlang {@link compiler} and {@link erl_lint}
%% modules.
-spec show_warnings(Warnings :: warnings()) -> ok.
show_warnings([]) ->
  ok;
show_warnings([{File, ErrorInfos}]) ->
  lists:map(fun(ErrorInfo) ->
               {Line, Desc} = format_error(ErrorInfo),
               io:format("~s:~b: Warning: ~s~n", [File, Line, Desc])
            end,
            ErrorInfos),
  ok;
show_warnings(_) ->
  ok.

%% @private Formats error and warning messages as human-readable descriptions,
%% returning the results together with the corresponding line number where the
%% error occurred.
-spec format_error(ErrorInfo) -> {Line :: line(), Description :: string()}
  when ErrorInfo :: error_info().
format_error({Line, erl_lint, Error}) ->
  {Line, erl_lint:format_error(Error)};
format_error({Line, hml_parser, Error}) ->
  {Line, hml_parser:format_error(Error)};
format_error({Line, hml_lexer, Error}) ->
  {Line, hml_lexer:format_error(Error)}.%%format_error({Line, sys_core_fold, Error}) ->
                                        %%  {Line, sys_core_fold:format_error(Error)}.

%%% ----------------------------------------------------------------------------
%%% Trace Name Syntax
%%% ----------------------------------------------------------------------------

traceNameFlatten(Num) when is_integer(Num) ->
  lists:flatten(["Trace", integer_to_list(Num)]).
