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
]

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
        _ -> "Invalid ret value"

Evaluator : {
    nodes : List Node,
}

eval : ParsedData -> Value
eval = \{ program, nodes } ->
    e0 = { nodes }
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
                _ -> (e1, Null)

        Negate { expr } ->
            (e1, val) = evalNode e0 expr
            when val is
                Int int -> (e1, Int -int)
                _ -> (e1, Null)

        Plus { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt + rhsInt))

                _ ->
                    (e2, Null)

        Minus { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt - rhsInt))

                _ ->
                    (e2, Null)

        Product { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt * rhsInt))

                _ ->
                    (e2, Null)

        Div { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, Int (lhsInt // rhsInt))

                _ ->
                    (e2, Null)

        Lt { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, (lhsInt < rhsInt) |> boolToValue)

                _ ->
                    (e2, Null)

        Gt { lhs, rhs } ->
            (e1, lhsVal) = evalNode e0 lhs
            (e2, rhsVal) = evalNode e1 rhs
            when (lhsVal, rhsVal) is
                (Int lhsInt, Int rhsInt) ->
                    (e2, (lhsInt > rhsInt) |> boolToValue)

                _ ->
                    (e2, Null)

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
            if isTruthy condVal then
                evalNode e1 consequence
            else
                (e1, Null)

        IfElse { cond, consequence, alternative } ->
            (e1, condVal) = evalNode e0 cond
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
                _ -> (e1, Null)

        _ -> crash "not implemented yet"

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
