interface Parser
    exposes [parse]
    imports [Lexer.{ LexedData }]

Index : U32

# Note: program could be a node and may be worth changing later.
# It would just reference a range of nodes that make up the statements of the program.
# Would require collect all top level statements together in the nodes list.
Program : List Index

# We are skipping parsing into a error message friendly structure.
# In a proper setup, every node should reference a NodeIndex or TokenIndex,
# such that it can eventually resolve to an exact line/col number.
# The Monkey interpreter in the book does not track this info.
# Neither will we, at least for now.
# This structure is more setup for execution speed.
Node : [
    Let { ident : Index, expr : Index },

    # TODO: is it worth directly adding the Str to node? Maybe it should be boxed or in a side list?
    # The Str takes up 24 bytes and makes Node a less dense union overall.
    Ident Str,
    Int U64,

    # This is temporary and should be removed once full parsing is setup.
    None,
]

ParsedData : {
    program : Program,
    nodes : List Node,
}

# Given errors only occur on the sad path, I don't mind that they are just strings.
Errors : List Str

# When updating a field in the parser, always use one of the addNode, advanceTokens, or addError.
# They are written to ensure refcounts don't lead to accidental copies.
Parser : {
    nodes : List Node,
    remainingTokens : List Lexer.Token,
    bytes : List U8,
    errors : Errors,
}

addNode : Parser, Node -> (Parser, Index)
addNode = \{ nodes, remainingTokens, bytes, errors }, node ->
    index = List.len nodes
    nextNodes = List.append nodes node
    ({ nodes: nextNodes, remainingTokens, bytes, errors }, Num.toU32 index)

advanceTokens : Parser, Nat -> Parser
advanceTokens = \{ nodes, remainingTokens, bytes, errors }, n ->
    { nodes, remainingTokens: List.drop remainingTokens n, bytes, errors }

addError : Parser, Str -> Parser
addError = \{ nodes, remainingTokens, bytes, errors }, error ->
    { nodes, remainingTokens, bytes, errors: List.append errors error }

parse : LexedData -> Result ParsedData Errors
parse = \lexedData ->
    parser = {
        # Assume we will have ~1 node per token in Monkey.
        nodes: List.withCapacity (List.len lexedData.tokens),
        remainingTokens: lexedData.tokens,
        bytes: lexedData.bytes,
        errors: [],
    }
    program = List.withCapacity 128

    parseProgram parser program

parseProgram : Parser, Program -> Result ParsedData Errors
parseProgram = \p0, program ->
    when List.first p0.remainingTokens is
        Ok { kind: Eof } ->
            if List.isEmpty p0.errors then
                Ok { program, nodes: p0.nodes }
            else
                Err p0.errors

        Ok token ->
            (p1, statement) =
                when token.kind is
                    Let ->
                        parseLetStatement (advanceTokens p0 1)

                    _ ->
                        # These probably should be a parse error, but the book just skips them.
                        # I am just gonna follow along.
                        (advanceTokens p0 1, Err {})

            when statement is
                Ok index ->
                    parseProgram p1 (List.append program index)

                Err {} ->
                    parseProgram p1 program

        Err _ ->
            eofCrash {}

parseLetStatement : Parser -> (Parser, Result Index {})
parseLetStatement = \p0 ->
    when p0.remainingTokens is
        [{ kind: Ident, index: byteIndex }, { kind: Assign }, ..] ->
            ident =
                Lexer.getIdent p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable

            (p1, identIndex) = addNode p0 (Ident ident)
            (p2, exprRes) = parseExpression (advanceTokens p1 2)
            when exprRes is
                Ok exprIndex ->
                    (p3, letIndex) = addNode p2 (Let { ident: identIndex, expr: exprIndex })
                    (p3, Ok letIndex)

                Err {} ->
                    (p2, Err {})

        [{ kind: Ident }, token, ..] ->
            p0
            |> advanceTokens 1
            |> tokenMismatch "Assign" token
            |> \p1 -> (p1, Err {})

        [token, ..] ->
            p0
            |> tokenMismatch "Ident" token
            |> \p1 -> (p1, Err {})

        _ ->
            eofCrash {}

tokenMismatch : Parser, Str, Lexer.Token -> Parser
tokenMismatch = \p0, wanted, got ->
    debugStr =
        Lexer.debugPrintToken [] p0.bytes got
        |> Str.fromUtf8
        |> okOrUnreachable
    addError p0 "Expected next token to be \(wanted), instead got: \(debugStr)"

parseExpression : Parser -> (Parser, Result Index {})
parseExpression = \p0 ->
    # TODO: real impl
    p0
    |> skipToSemicolon
    |> addNode None
    |> \(p1, i) -> (p1, Ok i)

skipToSemicolon : Parser -> Parser
skipToSemicolon = \p0 ->
    when List.first p0.remainingTokens is
        Ok { kind: Semicolon } ->
            advanceTokens p0 1

        Ok { kind: Eof } ->
            p0

        Ok _ ->
            skipToSemicolon (advanceTokens p0 1)

        Err _ ->
            eofCrash {}

eofCrash = \{} ->
    crash "token list did not end with Eof"

okOrUnreachable = \res ->
    when res is
        Ok v -> v
        Err _ -> crash "unreachable"

expect
    input = Str.toUtf8
        """
        let x = 5;
        let y = 10;
        let foobar = 838383;
        """
    parsed =
        Lexer.lex input
        |> parse
        |> okOrUnreachable

    identNames =
        parsed.program
        |> List.map \letIndex ->
            letNode =
                when List.get parsed.nodes (Num.toNat letIndex) is
                    Ok v -> v
                    _ -> crash "let node outside of list bounds"

            identIndex =
                when letNode is
                    Let { ident } -> ident
                    _ -> crash "all statements in program should be let statements"

            identNode =
                when List.get parsed.nodes (Num.toNat identIndex) is
                    Ok v -> v
                    _ -> crash "ident node outside of list bounds"

            when identNode is
                Ident str -> str
                _ -> crash "must be ident node"

    expected = ["x", "y", "foobar"]

    identNames == expected
