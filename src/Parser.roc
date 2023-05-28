interface Parser
    exposes [parse, debugPrint, ParsedData, Index, Node]
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
# In the end, I decided to go with limiting this struct to 3 U64s worth of storage.
# This is a bit a laziness and a bit of avoiding bloat.
# This enables storing a List or Str directly in a node if it is the only value in a node.
# One thing we lose with this current setup in roc is knowledge around the nested tag type.
# Even though let must contain an Ident, Roc will force us to check the tag to extra the ident.
Node : [
    Fn { params : Index, body : Index },
    If { cond : Index, consequence : Index },
    IfElse { cond : Index, consequence : Index, alternative : Index },
    Block (List Index),
    Call { fn : Index, args : Index },
    CallArgs (List Index),
    Let { ident : Index, expr : Index },
    Return { expr : Index },
    Ident Str,
    IdentList (List Str),
    Int I64,
    True,
    False,
    Not { expr : Index },
    Negate { expr : Index },
    Plus { lhs : Index, rhs : Index },
    Minus { lhs : Index, rhs : Index },
    Eq { lhs : Index, rhs : Index },
    NotEq { lhs : Index, rhs : Index },
    Lt { lhs : Index, rhs : Index },
    Gt { lhs : Index, rhs : Index },
    Product { lhs : Index, rhs : Index },
    Div { lhs : Index, rhs : Index },
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

# Errors are collected in the Parser state.
ParseResult : Result (Parser, Index) Parser

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

unexpectedEof : Parser -> Parser
unexpectedEof = \p0 ->
    addError p0 "Unexpectly ran out of tokens"

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
    when p0.remainingTokens is
        [{ kind: Eof }, ..] ->
            if List.isEmpty p0.errors then
                Ok { program, nodes: p0.nodes }
            else
                Err p0.errors

        [token, ..] ->
            when parseStatement p0 token is
                Ok (p1, index) ->
                    parseProgram p1 (List.append program index)

                Err p1 ->
                    parseProgram p1 program

        [] ->
            eofCrash {}

parseStatement : Parser, Lexer.Token -> ParseResult
parseStatement = \p0, token ->
    when token.kind is
        Let ->
            p0
            |> advanceTokens 1
            |> parseLetStatement

        Return ->
            p0
            |> advanceTokens 1
            |> parseReturnStatement

        _ ->
            parseExpressionStatement p0

parseLetStatement : Parser -> ParseResult
parseLetStatement = \p0 ->
    when p0.remainingTokens is
        [{ kind: Ident, index: byteIndex }, { kind: Assign }, ..] ->
            ident =
                Lexer.getIdent p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable "Ident is not valid utf8"

            (p1, identIndex) = addNode p0 (Ident ident)
            (p2, exprIndex) <- parseExpression (advanceTokens p1 2) precLowest |> Result.map
            (p3, letIndex) = addNode p2 (Let { ident: identIndex, expr: exprIndex })
            (consumeOptionalSemicolon p3, letIndex)

        [{ kind: Ident }, token, ..] ->
            p0
            |> advanceTokens 1
            |> tokenMismatch "Assign" token
            |> Err

        [token, ..] ->
            p0
            |> tokenMismatch "Ident" token
            |> Err

        [] ->
            p0
            |> unexpectedEof
            |> Err

parseReturnStatement : Parser -> ParseResult
parseReturnStatement = \p0 ->
    (p1, exprIndex) <- parseExpression p0 precLowest |> Result.map
    (p2, retIndex) = addNode p1 (Return { expr: exprIndex })
    (consumeOptionalSemicolon p2, retIndex)

tokenMismatch : Parser, Str, Lexer.Token -> Parser
tokenMismatch = \p0, wanted, got ->
    debugStr =
        Lexer.debugPrintToken [] p0.bytes got
        |> Str.fromUtf8
        |> okOrUnreachable "token is not valid utf8"
    addError p0 "Expected next token to be \(wanted), instead got: \(debugStr)"

# We just parse this into an expression.
# No need to wrap it in a special node.
parseExpressionStatement : Parser -> ParseResult
parseExpressionStatement = \p0 ->
    (p1, exprRes) <- parseExpression p0 precLowest |> Result.map
    (consumeOptionalSemicolon p1, exprRes)

Precedence := U32
precLowest = @Precedence 1
precEquals = @Precedence 2
precLessGreater = @Precedence 3
precSum = @Precedence 4
precProduct = @Precedence 5
precPrefix = @Precedence 6
precCall = @Precedence 7

precGTE = \@Precedence lhs, @Precedence rhs -> lhs >= rhs

peekPrecedence : Parser -> Precedence
peekPrecedence = \p0 ->
    when List.first p0.remainingTokens is
        Ok { kind: Eq } -> precEquals
        Ok { kind: NotEq } -> precEquals
        Ok { kind: Gt } -> precLessGreater
        Ok { kind: Lt } -> precLessGreater
        Ok { kind: Plus } -> precSum
        Ok { kind: Minus } -> precSum
        Ok { kind: Asterisk } -> precProduct
        Ok { kind: Slash } -> precProduct
        Ok { kind: LParen } -> precCall
        _ -> precLowest

parseExpression : Parser, Precedence -> ParseResult
parseExpression = \p0, basePrec ->
    (p1, lhs) <- parsePrefix p0 |> Result.try
    parseInfix p1 lhs basePrec

parseInfix : Parser, Index, Precedence -> ParseResult
parseInfix = \p0, lhsIndex, basePrec ->
    nextPrec = peekPrecedence p0
    if precGTE basePrec nextPrec then
        Ok (p0, lhsIndex)
    else
        when p0.remainingTokens is
            [{ kind: LParen }, ..] ->
                (p1, argsIndex) <- parseCallArgs (advanceTokens p0 1) |> Result.try
                (p2, callIndex) = addNode p1 (Call { fn: lhsIndex, args: argsIndex })
                parseInfix p2 callIndex basePrec

            [token, ..] ->
                # parse standard infix
                binOpRes =
                    when token.kind is
                        Eq -> Ok Eq
                        NotEq -> Ok NotEq
                        Lt -> Ok Lt
                        Gt -> Ok Gt
                        Plus -> Ok Plus
                        Minus -> Ok Minus
                        Asterisk -> Ok Product
                        Slash -> Ok Div
                        _ -> Err NotInfix

                when binOpRes is
                    Ok binOp ->
                        (p1, rhsIndex) <- parseExpression (advanceTokens p0 1) nextPrec |> Result.try
                        (p2, binIndex) = addNode p1 (binOp { lhs: lhsIndex, rhs: rhsIndex })
                        parseInfix p2 binIndex basePrec

                    Err NotInfix ->
                        Ok (p0, lhsIndex)

            [] ->
                p0
                |> unexpectedEof
                |> Err

parseCallArgs : Parser -> ParseResult
parseCallArgs = \p0 ->
    when p0.remainingTokens is
        [{ kind: RParen }, ..] ->
            addNode (advanceTokens p0 1) (CallArgs [])
            |> Ok

        [_, ..] ->
            (p1, argIndex) <- parseExpression p0 precLowest |> Result.try
            parseCallArgsHelper p1 [argIndex]

        [] ->
            p0
            |> unexpectedEof
            |> Err

parseCallArgsHelper : Parser, List Index -> ParseResult
parseCallArgsHelper = \p0, args ->
    when p0.remainingTokens is
        [{ kind: RParen }, ..] ->
            addNode (advanceTokens p0 1) (CallArgs args)
            |> Ok

        [{ kind: Comma }, ..] ->
            (p1, argIndex) <- parseExpression (advanceTokens p0 1) precLowest |> Result.try
            parseCallArgsHelper p1 (List.append args argIndex)

        [token, ..] ->
            p0
            |> advanceTokens 1
            |> tokenMismatch "RParen or Comma" token
            |> Err

        [] ->
            p0
            |> unexpectedEof
            |> Err

parsePrefix : Parser -> ParseResult
parsePrefix = \p0 ->
    when p0.remainingTokens is
        [{ kind: Ident, index: byteIndex }, ..] ->
            ident =
                Lexer.getIdent p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable "ident is not valid utf8"

            p0
            |> advanceTokens 1
            |> addNode (Ident ident)
            |> Ok

        [{ kind: Int, index: byteIndex }, ..] ->
            intStr =
                Lexer.getInt p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable "int is not valid utf8"

            when Str.toI64 intStr is
                Ok int ->
                    p0
                    |> advanceTokens 1
                    |> addNode (Int int)
                    |> Ok

                Err _ ->
                    p0
                    |> advanceTokens 1
                    |> addError "could not parse \(intStr) as integer"
                    |> Err

        [{ kind: Bang, index: _ }, ..] ->
            (p1, exprIndex) <- parseExpression (advanceTokens p0 1) precPrefix |> Result.map
            addNode p1 (Not { expr: exprIndex })

        [{ kind: Minus, index: _ }, ..] ->
            (p1, exprIndex) <- parseExpression (advanceTokens p0 1) precPrefix |> Result.map
            addNode p1 (Negate { expr: exprIndex })

        [{ kind: LParen, index: _ }, ..] ->
            (p1, exprIndex) <- parseExpression (advanceTokens p0 1) precLowest |> Result.try
            when p1.remainingTokens is
                [{ kind: RParen }, ..] ->
                    Ok (advanceTokens p1 1, exprIndex)

                [token, ..] ->
                    p1
                    |> tokenMismatch "RParen" token
                    |> Err

                [] ->
                    p0
                    |> unexpectedEof
                    |> Err

        [{ kind: True, index: _ }, ..] ->
            p0
            |> advanceTokens 1
            |> addNode True
            |> Ok

        [{ kind: False, index: _ }, ..] ->
            p0
            |> advanceTokens 1
            |> addNode False
            |> Ok

        [{ kind: If, index: _ }, ..] ->
            parseIfExpression (advanceTokens p0 1)

        [{ kind: Function, index: _ }, ..] ->
            parseFnExpression (advanceTokens p0 1)

        [token, ..] ->
            debugStr =
                Lexer.debugPrintToken [] p0.bytes token
                |> Str.fromUtf8
                |> okOrUnreachable "token is not valid utf8"

            p0
            |> advanceTokens 1
            |> addError "no prefix parse function for \(debugStr) found"
            |> Err

        [] ->
            p0
            |> unexpectedEof
            |> Err

parseFnExpression : Parser -> ParseResult
parseFnExpression = \p0 ->
    when p0.remainingTokens is
        [{ kind: LParen }, ..] ->
            (p1, paramsIndex) <- parseFnParams (advanceTokens p0 1) [] |> Result.try
            when p1.remainingTokens is
                [{ kind: LBrace }, ..] ->
                    (p2, bodyIndex) <- parseBlock (advanceTokens p1 1) [] |> Result.map
                    addNode p2 (Fn { params: paramsIndex, body: bodyIndex })

                [token, ..] ->
                    p1
                    |> tokenMismatch "LBrace" token
                    |> Err

                [] ->
                    p1
                    |> unexpectedEof
                    |> Err

        [token, ..] ->
            p0
            |> tokenMismatch "LParen" token
            |> Err

        [] ->
            p0
            |> unexpectedEof
            |> Err

parseFnParams : Parser, List Str -> ParseResult
parseFnParams = \p0, idents ->
    when p0.remainingTokens is
        [{ kind: Ident, index: byteIndex }, { kind: Comma }, ..] ->
            ident =
                Lexer.getIdent p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable "Ident is not valid utf8"
            parseFnParams (advanceTokens p0 2) (List.append idents ident)

        [{ kind: Ident, index: byteIndex }, { kind: RParen }, ..] ->
            ident =
                Lexer.getIdent p0.bytes byteIndex
                |> Str.fromUtf8
                |> okOrUnreachable "Ident is not valid utf8"
            addNode (advanceTokens p0 2) (IdentList (List.append idents ident))
            |> Ok

        [{ kind: RParen }, ..] ->
            addNode (advanceTokens p0 1) (IdentList idents)
            |> Ok

        [token, ..] ->
            p0
            |> tokenMismatch "Ident" token
            |> Err

        [] ->
            p0
            |> unexpectedEof
            |> Err

# TODO: Add some sort of wrapper and backpassing or similar to avoid all the nesting here and in similar functions.
# This is just painfully deep.
parseIfExpression : Parser -> ParseResult
parseIfExpression = \p0 ->
    when p0.remainingTokens is
        [{ kind: LParen }, ..] ->
            (p1, condIndex) <- parseExpression (advanceTokens p0 1) precLowest |> Result.try
            when p1.remainingTokens is
                [{ kind: RParen }, { kind: LBrace }, ..] ->
                    (p2, consequenceIndex) <- parseBlock (advanceTokens p1 2) [] |> Result.try
                    when p2.remainingTokens is
                        [{ kind: Else }, { kind: LBrace }, ..] ->
                            (p3, alternativeIndex) <- parseBlock (advanceTokens p2 2) [] |> Result.map
                            addNode p3 (IfElse { cond: condIndex, consequence: consequenceIndex, alternative: alternativeIndex })

                        [_, ..] ->
                            addNode p2 (If { cond: condIndex, consequence: consequenceIndex })
                            |> Ok

                        [] ->
                            p2
                            |> unexpectedEof
                            |> Err

                [{ kind: RParen }, token, ..] ->
                    p1
                    |> advanceTokens 1
                    |> tokenMismatch "LBrace" token
                    |> Err

                [token, ..] ->
                    p1
                    |> tokenMismatch "RParen" token
                    |> Err

                [] ->
                    p1
                    |> unexpectedEof
                    |> Err

        [token, ..] ->
            p0
            |> tokenMismatch "LParen" token
            |> Err

        [] ->
            p0
            |> unexpectedEof
            |> Err

parseBlock : Parser, List Index -> ParseResult
parseBlock = \p0, statements ->
    when p0.remainingTokens is
        [{ kind: RBrace }, ..] ->
            p0
            |> advanceTokens 1
            |> addNode (Block statements)
            |> Ok

        [token, ..] ->
            when parseStatement p0 token is
                Ok (p1, index) ->
                    parseBlock p1 (List.append statements index)

                Err p1 ->
                    parseBlock p1 statements

        [] ->
            p0
            |> unexpectedEof
            |> Err

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
    debugPrintIndented buf nodes program ""

debugPrintIndented : Str, List Node, List Index, Str -> Str
debugPrintIndented = \buf, nodes, program, spaces ->
    List.walk program buf \b, index ->
        debugPrintNodeStatement b nodes index spaces

debugPrintNodeStatement : Str, List Node, Index, Str -> Str
debugPrintNodeStatement = \buf, nodes, index, spaces ->
    buf
    |> Str.concat spaces
    |> debugPrintNode nodes index spaces
    |> Str.concat ";\n"

debugPrintNode : Str, List Node, Index, Str -> Str
debugPrintNode = \buf, nodes, index, spaces ->
    node =
        when List.get nodes (Num.toNat index) is
            Ok v -> v
            Err _ -> crash "node index out of bounds"

    when node is
        Call { fn, args } ->
            buf
            |> debugPrintNode nodes fn spaces
            |> debugPrintNode nodes args spaces

        CallArgs args ->
            buf
            |> Str.concat "("
            |> \b ->
                args
                |> List.map \argIndex -> debugPrintNode "" nodes argIndex spaces
                |> List.intersperse ", "
                |> List.walk b Str.concat
            |> Str.concat ")"

        Fn { params, body } ->
            buf
            |> Str.concat "fn"
            |> debugPrintNode nodes params spaces
            |> Str.concat " "
            |> debugPrintNode nodes body spaces

        If { cond, consequence } ->
            buf
            |> Str.concat "if "
            |> debugPrintNode nodes cond spaces
            |> Str.concat " "
            |> debugPrintNode nodes consequence spaces

        IfElse { cond, consequence, alternative } ->
            buf
            |> Str.concat "if "
            |> debugPrintNode nodes cond spaces
            |> Str.concat " "
            |> debugPrintNode nodes consequence spaces
            |> Str.concat " else "
            |> debugPrintNode nodes alternative spaces

        Block statements ->
            buf
            |> Str.concat "{\n"
            |> debugPrintIndented nodes statements (Str.concat spaces "    ")
            |> Str.concat spaces
            |> Str.concat "}"

        Let { ident, expr } ->
            buf
            |> Str.concat "let "
            |> debugPrintNode nodes ident spaces
            |> Str.concat " = "
            |> debugPrintNode nodes expr spaces

        Return { expr } ->
            buf
            |> Str.concat "return "
            |> debugPrintNode nodes expr spaces

        IdentList idents ->
            buf
            |> Str.concat "("
            |> \b ->
                idents
                |> List.intersperse ", "
                |> List.walk b Str.concat
            |> Str.concat ")"

        Ident ident ->
            Str.concat buf ident

        True ->
            Str.concat buf "true"

        False ->
            Str.concat buf "false"

        Int int ->
            Str.concat buf (Num.toStr int)

        Not { expr } ->
            buf
            |> Str.concat "(!"
            |> debugPrintNode nodes expr spaces
            |> Str.concat ")"

        Negate { expr } ->
            buf
            |> Str.concat "(-"
            |> debugPrintNode nodes expr spaces
            |> Str.concat ")"

        Eq { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " == "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

        NotEq { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " != "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

        Lt { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " < "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

        Gt { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " > "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

        Plus { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " + "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

        Minus { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " - "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

        Product { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " * "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

        Div { lhs, rhs } ->
            buf
            |> Str.concat "("
            |> debugPrintNode nodes lhs spaces
            |> Str.concat " / "
            |> debugPrintNode nodes rhs spaces
            |> Str.concat ")"

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

formatedOutput = \input ->
    input
    |> Str.toUtf8
    |> Lexer.lex
    |> parse
    |> Result.map \parsed -> debugPrint "" parsed

expect
    input =
        """
        let x = 5;
        let y = x;
        return 838383;

        """
    out = formatedOutput input

    expected = Ok input
    out == expected

expect
    input =
        """
        !5;
        -15;

        """
    out = formatedOutput input

    expected = Ok
        """
        (!5);
        (-15);

        """
    out == expected

expect
    input =
        """
        5 + 5;
        5 - 5;
        5 * 5;
        5 / 5;
        5 > 5;
        5 < 5;
        5 == 5;
        5 != 5;

        """
    out = formatedOutput input

    expected = Ok
        """
        (5 + 5);
        (5 - 5);
        (5 * 5);
        (5 / 5);
        (5 > 5);
        (5 < 5);
        (5 == 5);
        (5 != 5);

        """
    out == expected

expect
    input =
        """
        -a * b
        !-a
        a + b + c
        a + b - c
        a * b * c
        a * b / c
        a + b / c
        a + b * c + d / e - f
        3 + 4; -5 * 5
        5 > 4 == 3 < 4
        5 < 4 != 3 > 4
        3 + 4 * 5 == 3 * 1 + 4 * 5
        """
    out = formatedOutput input

    expected = Ok
        """
        ((-a) * b);
        (!(-a));
        ((a + b) + c);
        ((a + b) - c);
        ((a * b) * c);
        ((a * b) / c);
        (a + (b / c));
        (((a + (b * c)) + (d / e)) - f);
        (3 + 4);
        ((-5) * 5);
        ((5 > 4) == (3 < 4));
        ((5 < 4) != (3 > 4));
        ((3 + (4 * 5)) == ((3 * 1) + (4 * 5)));

        """
    out == expected

expect
    input =
        """
        true;
        false;
        3 > 5 == false
        3 < 5 == true
        """
    out = formatedOutput input

    expected = Ok
        """
        true;
        false;
        ((3 > 5) == false);
        ((3 < 5) == true);

        """
    out == expected

expect
    input =
        """
        1 + (2 + 3) + 4;
        (5 + 5) * 2
        2 / (5 + 5);
        -(5 + 5)
        !(true == true)
        """
    out = formatedOutput input

    expected = Ok
        """
        ((1 + (2 + 3)) + 4);
        ((5 + 5) * 2);
        (2 / (5 + 5));
        (-(5 + 5));
        (!(true == true));

        """
    out == expected

expect
    input =
        "if (x < y) { x }"
    out = formatedOutput input

    expected = Ok
        """
        if (x < y) {
            x;
        };

        """
    out == expected

expect
    input =
        "if (x < y) { x } else { y }"
    out = formatedOutput input

    expected = Ok
        """
        if (x < y) {
            x;
        } else {
            y;
        };

        """
    out == expected

expect
    input =
        """
        fn() { }
        fn(x) { x }
        fn(x, y, z) { x + y + z }
        """
    out = formatedOutput input

    expected = Ok
        """
        fn() {
        };
        fn(x) {
            x;
        };
        fn(x, y, z) {
            ((x + y) + z);
        };

        """
    out == expected

expect
    input =
        """
        a + add(b * c) + d
        add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))
        add(a + b + c * d / f + g)
        """
    out = formatedOutput input

    expected = Ok
        """
        ((a + add((b * c))) + d);
        add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)));
        add((((a + b) + ((c * d) / f)) + g));

        """
    out == expected

