interface Eval
    exposes [eval, printValue]
    imports [Lexer, Parser.{ Index, Node, ParsedData }]

Value : [
    Int I64,
    True,
    False,
    Null,

    # Values that need to be propogated up and returned.
    RetInt I64,
    RetTrue,
    RetFalse,
    RetNull,

    # Errors are just strings.
    # They are boxed to not bloat Value.
    # TODO: Boxing here breaks tests if run.
    # It works fine in repl, so I guess this is just not testable for now.
    Error (Box Str),
]

makeError : Str -> Value
makeError = \str -> Error (Box.box str)

valueToType : Value -> Str
valueToType = \val ->
    when val is
        Int _ -> "INTEGER"
        True | False -> "BOOLEAN"
        Null -> "NULL"
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
        Error boxedStr -> Str.concat "ERROR: " (Box.unbox boxedStr)
        _ -> "Invalid ret value"

Evaluator : {
    nodes : List Node,
    # TODO: look into making this a vecmap.
    env : Dict Str Value,
}

setIdent : Evaluator, Str, Value -> (Evaluator, Value)
setIdent = \{ nodes, env }, ident, val ->
    nextEnv = Dict.insert env ident val
    ({ nodes, env: nextEnv }, val)

getIdent : Evaluator, Str -> Value
getIdent = \{ env }, ident ->
    when Dict.get env ident is
        Ok val -> val
        Err _ -> makeError "identifier not found: \(ident)"

eval : ParsedData -> Value
eval = \{ program, nodes } ->
    e0 = { nodes, env: Dict.withCapacity 128 }
    (_, out) = evalProgram e0 program
    out

evalProgram : Evaluator, List Index -> (Evaluator, Value)
evalProgram = \e0, statements ->
    List.walkUntil statements (e0, Null) \(e1, _), index ->
        (e2, val) = evalNode e1 index
        when val is
            RetInt int -> Break (e2, Int int)
            RetTrue -> Break (e2, True)
            RetFalse -> Break (e2, False)
            RetNull -> Break (e2, Null)
            Error e -> Break (e2, Error e)
            Int int -> Continue (e2, Int int)
            True -> Continue (e2, True)
            False -> Continue (e2, False)
            Null -> Continue (e2, Null)

evalBlock : Evaluator, List Index -> (Evaluator, Value)
evalBlock = \e0, statements ->
    List.walkUntil statements (e0, Null) \(e1, _), index ->
        (e2, val) = evalNode e1 index
        when val is
            RetInt int -> Break (e2, RetInt int)
            RetTrue -> Break (e2, RetTrue)
            RetFalse -> Break (e2, RetFalse)
            RetNull -> Break (e2, RetNull)
            Error e -> Break (e2, Error e)
            Int int -> Continue (e2, Int int)
            True -> Continue (e2, True)
            False -> Continue (e2, False)
            Null -> Continue (e2, Null)

evalNode : Evaluator, Index -> (Evaluator, Value)
evalNode = \e0, index ->
    node = loadOrCrash e0 index
    when node is
        Int int -> (e0, Int int)
        True -> (e0, True)
        False -> (e0, False)
        Not { expr } ->
            (e1, val) = evalNode e0 expr
            when val is
                True -> (e1, False)
                False -> (e1, True)
                Null -> (e1, True)
                Int _ -> (e1, False)
                Error e -> (e1, Error e)
                _ -> (e1, Null)

        Negate { expr } ->
            (e1, val) = evalNode e0 expr
            when val is
                Int int -> (e1, Int -int)
                Error e -> (e1, Error e)
                _ ->
                    type = valueToType val
                    (e1, makeError "unknown operator: -\(type)")

        Plus { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt + rhsInt))

                (_, Error e) | (Error e, _) ->
                    (e2, Error e)

                _ ->
                    (e2, infixError "+" lhsVal rhsVal)

        Minus { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt - rhsInt))

                (_, Error e) | (Error e, _) ->
                    (e2, Error e)

                _ ->
                    (e2, infixError "-" lhsVal rhsVal)

        Product { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt * rhsInt))

                (_, Error e) | (Error e, _) ->
                    (e2, Error e)

                _ ->
                    (e2, infixError "*" lhsVal rhsVal)

        Div { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt // rhsInt))

                (_, Error e) | (Error e, _) ->
                    (e2, Error e)

                _ ->
                    (e2, infixError "/" lhsVal rhsVal)

        Lt { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, (lhsInt < rhsInt) |> boolToValue)

                (_, Error e) | (Error e, _) ->
                    (e2, Error e)

                _ ->
                    (e2, infixError "<" lhsVal rhsVal)

        Gt { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, (lhsInt > rhsInt) |> boolToValue)

                (_, Error e) | (Error e, _) ->
                    (e2, Error e)

                _ ->
                    (e2, infixError ">" lhsVal rhsVal)

        Eq { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            (e2, (lhsVal == rhsVal) |> boolToValue)

        NotEq { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            (e2, (lhsVal != rhsVal) |> boolToValue)

        If { cond, consequence } ->
            (e1, condVal) = evalNode e0 cond
            when condVal is
                Error e -> (e1, Error e)
                _ ->
                    if isTruthy condVal then
                        evalNode e1 consequence
                    else
                        (e1, Null)

        IfElse { cond, consequence, alternative } ->
            (e1, condVal) = evalNode e0 cond
            when condVal is
                Error e -> (e1, Error e)
                _ ->
                    if isTruthy condVal then
                        evalNode e1 consequence
                    else
                        evalNode e1 alternative

        Block statements ->
            evalBlock e0 statements

        Return { expr } ->
            (e1, exprVal) = evalNode e0 expr
            when exprVal is
                Int int -> (e1, RetInt int)
                True -> (e1, RetTrue)
                False -> (e1, RetFalse)
                Null -> (e1, RetNull)
                Error e -> (e1, Error e)
                _ -> (e1, Null)

        Let { ident, expr } ->
            identNode = loadOrCrash e0 ident
            when identNode is
                Ident identStr ->
                    (e1, exprVal) = evalNode e0 expr
                    when exprVal is
                        Error e -> (e1, Error e)
                        _ -> setIdent e1 identStr exprVal

                _ -> crash "We already verified that we have an ident when parsing"

        Ident identStr ->
            (e0, getIdent e0 identStr)

        _ -> crash "not implemented yet"

infixError : Str, Value, Value -> Value
infixError = \op, lhs, rhs ->
    lhsType = valueToType lhs
    rhsType = valueToType rhs
    if lhsType != rhsType then
        makeError "type mismatch: \(lhsType) \(op) \(rhsType)"
    else
        makeError "unknown operator: \(lhsType) \(op) \(rhsType)"

isTruthy : Value -> Bool
isTruthy = \val ->
    when val is
        True -> Bool.true
        False -> Bool.false
        Null -> Bool.false
        Int _ -> Bool.true
        _ -> crash "ret values are not truthy"

loadOrCrash : Evaluator, Index -> Node
loadOrCrash = \{ nodes }, i ->
    when List.get nodes (Num.toNat i) is
        Ok v -> v
        Err _ -> crash "Node index out of bounds during eval"

okOrUnreachable = \res, str ->
    when res is
        Ok v -> v
        Err _ -> crash "unreachable: \(str)"

runFromSource = \input ->
    input
    |> Str.toUtf8
    |> Lexer.lex
    |> Parser.parse
    |> okOrUnreachable "parse unexpectedly failed"
    |> eval

expect
    inputs = ["5", "10", "-5", "-10", "true", "false"]
    out = List.map inputs runFromSource

    expected = [Int 5, Int 10, Int -5, Int -10, True, False]
    out == expected

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
    out == expected

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
    out == expected

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
    out == expected

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
    out == expected

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
    out == expected

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
    out == expected
