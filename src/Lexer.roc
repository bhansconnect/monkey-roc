interface Lexer
    exposes [lex]
    imports []

Kind : [
    Illegal,
    Eof,
    Ident,
    Int,
    Assign,
    Plus,
    Comma,
    Semicolon,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Function,
    Let,
]

Token : {
    kind : Kind,
    index : U32,
}

lex : List U8 -> List Token
lex = \bytes ->
    consumeToken = \{ tokens, remaining, index }, kind, size ->
        nextTokens = List.append tokens { kind, index }
        nextRemaining = List.drop remaining (Num.toNat size)
        nextIndex = index + size
        { tokens: nextTokens, remaining: nextRemaining, index: nextIndex }

    helper = \state ->
        # TODO: Investigate the perf of this compared to a state machine based parser.
        # This is a branching prefix tree.
        when state.remaining is
            [',', ..] ->
                consumeToken state Comma 1 |> helper

            [_, ..] ->
                consumeToken state Illegal 1 |> helper

            [] ->
                List.append state.tokens { kind: Eof, index: state.index }

    helper { tokens: List.withCapacity 1024, remaining: bytes, index: 0 }

expect
    input = ""
    expected = [{ kind: Eof, index: 0 }]

    lex (Str.toUtf8 input) == expected

