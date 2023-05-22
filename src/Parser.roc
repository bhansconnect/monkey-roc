interface Parser
    exposes [parse, debugPrint]
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
    Return { expr : Index },

    # TODO: is it worth directly adding the Str to node? Maybe it should be boxed or in a side list?
    # The Str takes up 24 bytes and makes Node a less dense union overall.
    Ident Str,
    Int U64,
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

                    Return ->
                        parseReturnStatement (advanceTokens p0 1)

                    _ ->
                        parseExpressionStatement p0

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
                |> okOrUnreachable "Ident is not valid utf8"

            (p1, identIndex) = addNode p0 (Ident ident)
            (p2, exprRes) = parseExpression (advanceTokens p1 2) precLowest
            when exprRes is
                Ok exprIndex ->
                    (p3, letIndex) = addNode p2 (Let { ident: identIndex, expr: exprIndex })
                    (consumeOptionalSemicolon p3, Ok letIndex)

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

        [] ->
            eofCrash {}

parseReturnStatement : Parser -> (Parser, Result Index {})
parseReturnStatement = \p0 ->
    (p1, exprRes) = parseExpression p0 precLowest
    when exprRes is
        Ok exprIndex ->
            (p2, retIndex) = addNode p1 (Return { expr: exprIndex })
            (consumeOptionalSemicolon p2, Ok retIndex)

        Err {} ->
            (p1, Err {})

tokenMismatch : Parser, Str, Lexer.Token -> Parser
tokenMismatch = \p0, wanted, got ->
    debugStr =
        Lexer.debugPrintToken [] p0.bytes got
        |> Str.fromUtf8
        |> okOrUnreachable "token is not valid utf8"
    addError p0 "Expected next token to be \(wanted), instead got: \(debugStr)"

# We just parse this into an expression.
# No need to wrap it in a special node.
parseExpressionStatement : Parser -> (Parser, Result Index {})
parseExpressionStatement = \p0 ->
    (p1, res) = parseExpression p0 precLowest

    (consumeOptionalSemicolon p1, res)

Precedence := U32
precLowest = @Precedence 1
precEquals = @Precedence 2
precLessGreater = @Precedence 3
precSum = @Precedence 4
precProduct = @Precedence 5
precPrefix = @Precedence 6
precCall = @Precedence 7

parseExpression : Parser, Precedence -> (Parser, Result Index {})
parseExpression = \p0, @Precedence _precedence ->
    parsePrefix p0

parsePrefix : Parser -> (Parser, Result Index {})
parsePrefix = \p0 ->
    when List.first p0.remainingTokens is
        Ok { kind: Ident, index: byteIndex } ->
            ident =
                Lexer.getIdent p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable "ident is not valid utf8"

            p0
            |> advanceTokens 1
            |> addNode (Ident ident)
            |> \(p1, index) -> (p1, Ok index)

        Ok { kind: Int, index: byteIndex } ->
            intStr =
                Lexer.getInt p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable "int is not valid utf8"

            when Str.toU64 intStr is
                Ok int ->
                    p0
                    |> advanceTokens 1
                    |> addNode (Int int)
                    |> \(p1, index) -> (p1, Ok index)

                Err _ ->
                    p0
                    |> advanceTokens 1
                    |> addError "could not parse \(intStr) as integer"
                    |> \p1 -> (p1, Err {})

        Ok token ->
            debugStr =
                Lexer.debugPrintToken [] p0.bytes token
                |> Str.fromUtf8
                |> okOrUnreachable "token is not valid utf8"

            p0
            |> advanceTokens 1
            |> addError "no prefix parse function for \(debugStr) found"
            |> \p1 -> (p1, Err {})

        Err _ ->
            eofCrash {}

consumeOptionalSemicolon : Parser -> Parser
consumeOptionalSemicolon = \p0 ->
    when List.first p0.remainingTokens is
        Ok { kind: Semicolon } ->
            advanceTokens p0 1

        Ok _ ->
            p0

        Err _ ->
            eofCrash {}

eofCrash = \{} ->
    crash "token list did not end with Eof"

okOrUnreachable = \res, str ->
    when res is
        Ok v -> v
        Err _ -> crash "unreachable: \(str)"

debugPrint : Str, ParsedData -> Str
debugPrint = \buf, { nodes, program } ->
    List.walk program buf \b, index ->
        debugPrintNode b nodes index

debugPrintNode : Str, List Node, Index -> Str
debugPrintNode = \buf, nodes, index ->
    node =
        when List.get nodes (Num.toNat index) is
            Ok v -> v
            Err _ -> crash "node index out of bounds"

    when node is
        Let { ident, expr } ->
            buf
            |> Str.concat "let "
            |> debugPrintNode nodes ident
            |> Str.concat " = "
            |> debugPrintNode nodes expr
            |> Str.concat ";\n"

        Return { expr } ->
            buf
            |> Str.concat "return "
            |> debugPrintNode nodes expr
            |> Str.concat ";\n"

        Ident ident ->
            Str.concat buf ident

        Int int ->
            Str.concat buf (Num.toStr int)

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
        |> okOrUnreachable "parse unexpectedly failed"

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

expect
    input = Str.toUtf8
        """
        let x 5;
        let = 10;
        let 838383;
        """
    errors =
        Lexer.lex input
        |> parse
        |> \parsed ->
            when parsed is
                Ok _ -> crash "this should error"
                Err errs -> errs

    expected = [
        "Expected next token to be Assign, instead got: { kind: Int, value: 5 }",
        "Expected next token to be Ident, instead got: { kind: Assign }",
        "no prefix parse function for { kind: Assign } found",
        "Expected next token to be Ident, instead got: { kind: Int, value: 838383 }",
    ]
    errors == expected

expect
    input = Str.toUtf8
        """
        return 5;
        return 10;
        return 993322;
        """
    parsed =
        Lexer.lex input
        |> parse
        |> okOrUnreachable "parse unexpectedly failed"

    exprs =
        parsed.program
        |> List.map \retIndex ->
            retNode =
                when List.get parsed.nodes (Num.toNat retIndex) is
                    Ok v -> v
                    _ -> crash "let node outside of list bounds"

            when retNode is
                Return { expr } -> expr
                _ -> crash "all statements in program should be return statements"

    List.len exprs == 3

expect
    input =
        """
        let x = 5;
        let y = x;
        return 838383;
        """
    out =
        input
        |> Str.toUtf8
        |> Lexer.lex
        |> parse
        |> okOrUnreachable "parse unexpectedly failed"
        |> \parsed -> debugPrint "" parsed

    expected =
        """
        let x = 5;
        let y = x;
        return 838383;

        """
    out == expected

