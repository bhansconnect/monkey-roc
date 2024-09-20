module [eval, evalWithEnvs, newEnv, printValue]

import Lexer
import Parser exposing [Index, Node, ParsedData]

# I seem stuck.
# I am trying to make a version of eval that builds up closures from the expression tree.
# Then a call is just running the final closure with an environment.
# Sadly, to have higher order functions, either Value or Environment need to contain closures in them.
# This breaks the roc type system.
# I either get stack overflows, invalid recusion, or infinitely recursive types.

Value : [
    Int I64,
    True,
    False,
    Null,
    Fn { paramsIndex : Index, bodyIndex : Index, envIndex : Index },

    # Values that need to be propogated up and returned.
    RetInt I64,
    RetTrue,
    RetFalse,
    RetNull,
    RetFn { paramsIndex : Index, bodyIndex : Index, envIndex : Index },

    # Errors are just strings.
    # They are boxed to not bloat Value.
    # TODO: Boxing here breaks tests if run.
    # It works fine in repl, so I guess this is just not testable for now.
    Error (Box Str),
]

valueListEq : List Value, List Value -> Bool
valueListEq = \lhs, rhs ->
    List.map2 lhs rhs valueEq
    |> List.all \x -> x

valueEq : Value, Value -> Bool
valueEq = \lhs, rhs ->
    when (lhs, rhs) is
        (True, True) | (False, False) | (Null, Null) ->
            Bool.true

        (Int x, Int y) ->
            x == y

        _ ->
            Bool.false

makeError : Str -> Value
makeError = \str -> Error (Box.box str)

valueToType : Value -> Str
valueToType = \val ->
    when val is
        Int _ -> "INTEGER"
        True | False -> "BOOLEAN"
        Null -> "NULL"
        Fn _ -> "FUNCTION"
        _ -> crash "value has no type"

boolToValue : Bool -> Value
boolToValue = \bool ->
    if bool then
        True
    else
        False

printValue : Value -> Str
printValue = \value ->
    when value is
        Int int -> Num.toStr int
        True -> "true"
        False -> "false"
        Null -> "null"
        Fn _ -> "<function>"
        Error boxedStr -> Str.concat "ERROR: " (Box.unbox boxedStr)
        _ -> "Invalid ret value"

Env : {
    rc : U32,
    # Given most environments are small, a list and linear search was faster than a dict.
    # That said, only did a few tests.
    inner : List (Str, Value),
    outer : Result Index [IsRoot],
}

Evaluator : {
    envs : List Env,
    currentEnv : Index,
}

setIdent : Evaluator, Str, Value -> (Evaluator, Value)
setIdent = \{ envs: envs0, currentEnv }, ident, val ->
    { list: envs1, value: { rc, inner, outer } } = List.replace envs0 (Num.toU64 currentEnv) (newEnv {})
    when List.findFirstIndex inner (\(k, _) -> k == ident) is
        Ok i ->
            nextInner = List.set inner i (ident, val)
            ({ currentEnv, envs: List.set envs1 (Num.toU64 currentEnv) { rc, inner: nextInner, outer } }, val)

        Err _ ->
            # TODO: check if sorted insert is faster.
            nextInner = List.append inner (ident, val)
            ({ currentEnv, envs: List.set envs1 (Num.toU64 currentEnv) { rc, inner: nextInner, outer } }, val)

getIdent : List Env, Index, Str -> Value
getIdent = \envs, currentEnv, ident ->
    # TODO: maybe do binary search if the list is large enough.
    { inner, outer } =
        when List.get envs (Num.toU64 currentEnv) is
            Ok env -> env
            Err _ -> crash "bad env index"
    when List.findFirst inner (\(k, _) -> k == ident) is
        Ok (_, v) -> v
        Err _ ->
            when outer is
                Ok envIndex ->
                    getIdent envs envIndex ident

                Err _ ->
                    makeError "identifier not found: $(ident)"

newEnv : {} -> Env
newEnv = \{} -> { rc: 1, inner: [], outer: Err IsRoot }

incEnv : Evaluator, Index -> Evaluator
incEnv = \{ envs, currentEnv }, i ->
    when List.get envs (Num.toU64 i) is
        Ok { rc, inner, outer } ->
            nextRc = Num.addSaturated rc 1
            nextEnvs = List.set envs (Num.toU64 i) { rc: nextRc, inner, outer }
            { envs: nextEnvs, currentEnv }

        Err _ ->
            crash "env index out of bounds"

decEnv : Evaluator, Index -> Evaluator
decEnv = \{ envs, currentEnv }, i ->
    when List.get envs (Num.toU64 i) is
        Ok { rc, inner, outer } ->
            nextRc = Num.subSaturated rc 1
            nextEnvs = List.set envs (Num.toU64 i) { rc: nextRc, inner, outer }
            { envs: nextEnvs, currentEnv }
            |> maybeFreeEnv i

        Err _ ->
            crash "env index out of bounds"

maybeFreeEnv = \{ envs, currentEnv }, i ->
    when List.get envs (Num.toU64 i) is
        Ok { rc: 0, inner } ->
            List.walk inner { envs, currentEnv } \e0, (_, val) ->
                when val is
                    Fn { envIndex } ->
                        decEnv e0 envIndex

                    _ ->
                        e0

        _ ->
            { envs, currentEnv }

wrapAndSetEnv : Evaluator, Index -> Evaluator
wrapAndSetEnv = \{ envs }, i ->
    # First pick unused envs
    when List.findLastIndex envs (\{ rc } -> rc == 0) is
        Ok newIndex ->
            nextEnvs = List.set envs newIndex { rc: 1, inner: [], outer: Ok i }
            incEnv { envs: nextEnvs, currentEnv: Num.toU32 newIndex } i

        Err _ ->
            nextEnvs = List.append envs { rc: 1, inner: [], outer: Ok i }
            newIndex = List.len envs |> Num.toU32
            incEnv { envs: nextEnvs, currentEnv: newIndex } i

eval : ParsedData -> (List Env, Value)
eval = \pd ->
    evalWithEnvs pd [newEnv {}]

evalWithEnvs : ParsedData, List Env -> (List Env, Value)
evalWithEnvs = \{ program, nodes }, envs ->
    closure = buildProgram nodes program
    ({ envs: outEnvs }, outVal) = closure { envs, currentEnv: 0 }
    (outEnvs, outVal)

buildProgram : List Node, List Index -> (Evaluator -> (Evaluator, Value))
buildProgram = \nodes, statements ->
    statements
    |> List.map \index -> buildNode nodes index
    |> List.walk (\e -> (e, Null)) \programClosure, nodeClosure ->
        \e0 ->
            (e1, val) = programClosure e0
            when val is
                RetInt int -> (e1, Int int)
                RetTrue -> (e1, True)
                RetFalse -> (e1, False)
                RetNull -> (e1, Null)
                RetFn data -> (e1, Fn data)
                Error e -> (e1, Error e)
                _ ->
                    nodeClosure e1

buildNode : List Node, Index -> (Evaluator -> (Evaluator, Value))
buildNode = \nodes, index ->
    node = loadOrCrash nodes index
    when node is
        Int int -> \e -> (e, Int int)
        True -> \e -> (e, True)
        False -> \e -> (e, False)
        Not { expr } ->
            closure = buildNode nodes expr
            \e0 ->
                (e1, val) = closure e0
                when val is
                    True -> (e1, False)
                    False -> (e1, True)
                    Null -> (e1, True)
                    Int _ -> (e1, False)
                    Error e -> (e1, Error e)
                    _ -> (e1, Null)

        Negate { expr } ->
            closure = buildNode nodes expr
            \e0 ->
                (e1, val) = closure e0
                when val is
                    Int int -> (e1, Int -int)
                    Error e -> (e1, Error e)
                    _ ->
                        type = valueToType val
                        (e1, makeError "unknown operator: -$(type)")

        Plus { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                when (lhsVal, rhsVal) is
                    (Int lhsInt, Int rhsInt) ->
                        (e2, Int (lhsInt + rhsInt))

                    (_, Error e) | (Error e, _) ->
                        (e2, Error e)

                    _ ->
                        (e2, infixError "+" lhsVal rhsVal)

        Minus { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                when (lhsVal, rhsVal) is
                    (Int lhsInt, Int rhsInt) ->
                        (e2, Int (lhsInt - rhsInt))

                    (_, Error e) | (Error e, _) ->
                        (e2, Error e)

                    _ ->
                        (e2, infixError "-" lhsVal rhsVal)

        Product { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                when (lhsVal, rhsVal) is
                    (Int lhsInt, Int rhsInt) ->
                        (e2, Int (lhsInt * rhsInt))

                    (_, Error e) | (Error e, _) ->
                        (e2, Error e)

                    _ ->
                        (e2, infixError "*" lhsVal rhsVal)

        Div { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                when (lhsVal, rhsVal) is
                    (Int lhsInt, Int rhsInt) ->
                        (e2, Int (lhsInt // rhsInt))

                    (_, Error e) | (Error e, _) ->
                        (e2, Error e)

                    _ ->
                        (e2, infixError "/" lhsVal rhsVal)

        Lt { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                when (lhsVal, rhsVal) is
                    (Int lhsInt, Int rhsInt) ->
                        (e2, (lhsInt < rhsInt) |> boolToValue)

                    (_, Error e) | (Error e, _) ->
                        (e2, Error e)

                    _ ->
                        (e2, infixError "<" lhsVal rhsVal)

        Gt { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                when (lhsVal, rhsVal) is
                    (Int lhsInt, Int rhsInt) ->
                        (e2, (lhsInt > rhsInt) |> boolToValue)

                    (_, Error e) | (Error e, _) ->
                        (e2, Error e)

                    _ ->
                        (e2, infixError ">" lhsVal rhsVal)

        Eq { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                (e2, valueEq lhsVal rhsVal |> boolToValue)

        NotEq { lhs, rhs } ->
            lhsClosure = buildNode nodes lhs
            rhsClosure = buildNode nodes rhs
            \e0 ->
                (e1, lhsVal) = lhsClosure e0
                (e2, rhsVal) = rhsClosure e1
                (e2, !(valueEq lhsVal rhsVal) |> boolToValue)

        If { cond, consequence } ->
            condClosure = buildNode nodes cond
            consequenceClosure = buildNode nodes consequence
            \e0 ->
                (e1, condVal) = condClosure e0
                when condVal is
                    Error e -> (e1, Error e)
                    _ ->
                        if isTruthy condVal then
                            consequenceClosure e1
                        else
                            (e1, Null)

        IfElse { cond, consequence, alternative } ->
            condClosure = buildNode nodes cond
            consequenceClosure = buildNode nodes consequence
            alternativeClosure = buildNode nodes alternative
            \e0 ->
                (e1, condVal) = condClosure e0
                when condVal is
                    Error e -> (e1, Error e)
                    _ ->
                        if isTruthy condVal then
                            consequenceClosure e1
                        else
                            alternativeClosure e1

        Block statements ->
            # Lambasets and recursion bugs seem to stop me from making this a separate function.
            # They also stop me from building this the same way as buildProgram.
            # Instead, the list of closures is kept around.
            closures = List.map statements \i -> buildNode nodes i
            \e0 ->
                List.walk closures (e0, Null) \(e1, val), stmtClosure ->
                    when val is
                        RetInt int -> (e1, RetInt int)
                        RetTrue -> (e1, RetTrue)
                        RetFalse -> (e1, RetFalse)
                        RetNull -> (e1, RetNull)
                        RetFn data -> (e1, RetFn data)
                        Error e -> (e1, Error e)
                        _ ->
                            stmtClosure e1

        Return { expr } ->
            closure = buildNode nodes expr
            \e0 ->
                (e1, val) = closure e0
                when val is
                    Int int -> (e1, RetInt int)
                    True -> (e1, RetTrue)
                    False -> (e1, RetFalse)
                    Null -> (e1, RetNull)
                    Fn data -> (e1, RetFn data)
                    Error e -> (e1, Error e)
                    _ -> (e1, Null)

        Let { ident, expr } ->
            identNode = loadOrCrash nodes ident
            when identNode is
                Ident identStr ->
                    closure = buildNode nodes expr
                    \e0 ->
                        (e1, val) = closure e0
                        when val is
                            Error e -> (e1, Error e)
                            _ -> setIdent e1 identStr val

                _ -> crash "We already verified that we have an ident when parsing"

        Ident identStr ->
            \e -> (e, getIdent e.envs e.currentEnv identStr)

        Fn { params, body } ->
            # bodyClosure = buildNode nodes body
            \e0 ->
                e1 = incEnv e0 e0.currentEnv
                (e1, Fn { paramsIndex: params, bodyIndex: body, envIndex: e1.currentEnv })

        # Call { fn, args } ->
        #     fnClosure = buildNode nodes fn
        #     argsNode = loadOrCrash e1 args
        #     when argsNode is
        #         CallArgs callArgs ->
        #             # (e2, argVals) = evalArgs e1 callArgs
        #             \e0 ->
        #                 (e1, fnVal) = fnClosure e0
        #                 when (argVals, fnVal) is
        #                     ([Error e], _) -> (e2, Error e)
        #                     (_, Error e) -> (e2, Error e)
        #                     (_, Fn { paramsIndex, bodyIndex, envIndex }) ->
        #                         (params, body) =
        #                             when (loadOrCrash e2 paramsIndex, loadOrCrash e2 bodyIndex) is
        #                                 (IdentList paramList, Block statementList) ->
        #                                     (paramList, statementList)
        #                                 _ -> crash "We already verified that we have an ident list and body when parsing"
        #                         if List.len params == List.len argVals then
        #                             oldIndex = e2.currentEnv
        #                             e3 = wrapAndSetEnv e2 envIndex
        #                             newIndex = e3.currentEnv
        #                             (e6, _) =
        #                                 List.walk params (e3, 0) \(e4, i), param ->
        #                                     (e5, _) = setIdent e4 param (okOrUnreachable (List.get argVals i) "size checked")
        #                                     (e5, i + 1)
        #                             (e7, val) = evalProgram e6 body
        #                             # reset environment back to before the function was run.
        #                             e8 = decEnv e7 newIndex
        #                             ({ e8 & currentEnv: oldIndex }, val)
        #                         else
        #                             (e2, makeError "FUNCTION applied with wrong number of args")
        #                     _ ->
        #                         type = valueToType fnVal
        #                         (e2, makeError "expected FUNCTION instead got $(type)")
        #         _ -> crash "We already verified that we have call args when parsing"
        # IdentList _ -> crash "unreachable"
        # CallArgs _ -> crash "unreachable"
        _ -> crash "todo"

# evalArgs = \e0, args ->
#     List.walkUntil args (e0, List.withCapacity (List.len args)) \(e1, exprs), arg ->
#         (e2, argVal) = evalNode e1 arg
#         when argVal is
#             Error e -> Break (e2, [Error e])
#             _ -> Continue (e2, List.append exprs argVal)

infixError : Str, Value, Value -> Value
infixError = \op, lhs, rhs ->
    lhsType = valueToType lhs
    rhsType = valueToType rhs
    if lhsType != rhsType then
        makeError "type mismatch: $(lhsType) $(op) $(rhsType)"
    else
        makeError "unknown operator: $(lhsType) $(op) $(rhsType)"

isTruthy : Value -> Bool
isTruthy = \val ->
    when val is
        True -> Bool.true
        False -> Bool.false
        Null -> Bool.false
        Int _ -> Bool.true
        _ -> crash "ret values are not truthy"

loadOrCrash : List Node, Index -> Node
loadOrCrash = \nodes, i ->
    when List.get nodes (Num.toU64 i) is
        Ok v -> v
        Err _ -> crash "Node index out of bounds during eval"

okOrUnreachable = \res, str ->
    when res is
        Ok v -> v
        Err _ -> crash "unreachable: $(str)"

runFromSource = \input ->
    input
    |> Str.toUtf8
    |> Lexer.lex
    |> Parser.parse
    |> okOrUnreachable "parse unexpectedly failed"
    |> eval
    |> .1

expect
    inputs = ["5", "10", "-5", "-10", "true", "false"]
    out = List.map inputs runFromSource

    expected = [Int 5, Int 10, Int -5, Int -10, True, False]
    valueListEq out expected

expect
    inputs = [
        "!true",
        "!false",
        "!5",
        "!!true",
        "!!false",
        "!!5",
    ]
    out = List.map inputs runFromSource

    expected = [
        False,
        True,
        False,
        True,
        False,
        True,
    ]
    valueListEq out expected

expect
    inputs = [
        "5 + 5 + 5 + 5 - 10",
        "2 * 2 * 2 * 2 * 2",
        "-50 + 100 + -50",
        "5 * 2 + 10",
        "5 + 2 * 10",
        "20 + 2 * -10",
        "50 / 2 * 2 + 10",
        "2 * (5 + 10)",
        "3 * 3 * 3 + 10",
        "3 * (3 * 3) + 10",
        "(5 + 10 * 2 + 15 / 3) * 2 + -10",
    ]
    out = List.map inputs runFromSource

    expected = [
        Int 10,
        Int 32,
        Int 0,
        Int 20,
        Int 25,
        Int 0,
        Int 60,
        Int 30,
        Int 37,
        Int 37,
        Int 50,
    ]
    valueListEq out expected

expect
    inputs = [
        "true == true",
        "false == false",
        "true == false",
        "true != false",
        "false != true",
        "(1 < 2) == true",
        "(1 < 2) == false",
        "(1 > 2) == true",
        "(1 > 2) == false",
    ]
    out = List.map inputs runFromSource

    expected = [
        True,
        True,
        False,
        True,
        True,
        True,
        False,
        False,
        True,
    ]
    valueListEq out expected

expect
    inputs = [
        "if (true) { 10 }",
        "if (false) { 10 }",
        "if (1) { 10 }",
        "if (1 < 2) { 10 }",
        "if (1 > 2) { 10 }",
        "if (1 < 2) { 10 } else { 20 }",
        "if (1 > 2) { 10 } else { 20 }",
    ]
    out = List.map inputs runFromSource

    expected = [
        Int 10,
        Null,
        Int 10,
        Int 10,
        Null,
        Int 10,
        Int 20,
    ]
    valueListEq out expected

expect
    inputs = [
        "return 10;",
        "return 10; 9",
        "return 2 * 5; 9",
        "9; return 10; 9",
        "if (10 > 1) { if (10 > 1) { return 10; } return 1; }",
    ]
    out = List.map inputs runFromSource

    expected = [
        Int 10,
        Int 10,
        Int 10,
        Int 10,
        Int 10,
    ]
    valueListEq out expected

expect
    inputs = [
        "let a = 5; a;",
        "let a = 5 * 5; a;",
        "let a = 5; let b = a; b;",
        "let a = 5; let b = a; let c = a + b + 5; c;",
    ]
    out = List.map inputs runFromSource

    expected = [
        Int 5,
        Int 25,
        Int 5,
        Int 15,
    ]
    valueListEq out expected

expect
    inputs = [
        "let identity = fn(x) { x; }; identity(5);",
        "let identity = fn(x) { return x; 12; }; identity(5);",
        "let double = fn(x) { 2 * x;  }; double(5);",
        "fn(x) {x} (5)",
        # TODO: why does this cause freeing a a pointer that wasn't allocated?
        # "let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));",
    ]
    out = List.map inputs runFromSource

    expected = [
        Int 5,
        Int 5,
        Int 10,
        Int 5,
        # Int 20,
    ]
    valueListEq out expected

expect
    input =
        """
        let newAdder = fn(x) {
          fn(y) { x + y };
        };

        let addTwo = newAdder(2);
        addTwo(2);
        """
    out = runFromSource input

    expected = Int 4
    valueEq out expected

expect
    input =
        """
        let crazy = fn() {
          let x = 1;
          return fn() { return x };
          let x = 2;
        };

        let closure = crazy();
        closure();
        """
    out = runFromSource input

    expected = Int 1
    valueEq out expected

expect
    input =
        """
        let crazy = fn() {
          let x = 1;
          let out = fn () { return x };
          let x = 2;
          return out;
        };

        let closure = crazy();
        closure();
        """
    out = runFromSource input

    expected = Int 2
    valueEq out expected

expect
    input =
        """
        let fibonacci = fn(x) {
          if (x == 0) {
            0
          } else {
            if (x == 1) {
              return 1;
            } else {
              fibonacci(x - 1) + fibonacci(x - 2);
            }
          }
        };

        fibonacci(10)
        """
    out = runFromSource input

    expected = Int 55
    valueEq out expected
