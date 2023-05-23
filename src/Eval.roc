interface Eval
    exposes [eval]
    imports [Lexer, Parser.{ Index, Node, ParsedData }]

Value : [
    Int I64,
    True,
    False,
    Null,
]

Evaluator : {
    nodes : List Node,
}

eval : ParsedData -> Value
eval = \{ program, nodes } ->
    e0 = { nodes }
    (_, out) = evalStatements e0 program
    out

evalStatements : Evaluator, List Index -> (Evaluator, Value)
evalStatements = \e0, statements ->
    List.walk statements (e0, Null) \(e1, _), index ->
        evalNode e1 index

evalNode : Evaluator, Index -> (Evaluator, Value)
evalNode = \e0, index ->
    node = loadOrCrash e0 index
    when node is
        Int int -> (e0, Int int)
        _ -> crash "not implemented yet"

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
    inputs = ["5", "10"]
    out = List.map inputs runFromSource

    expected = [Int 5, Int 10]
    out == expected
