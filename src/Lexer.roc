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
    helper = \state ->
        # TODO: Investigate the perf of this compared to a state machine based parser.
        # This is a branching prefix tree.
        when state.remaining is
            ['l', 'e', 't', ..] ->
                consumeToken state Let 3 |> helper

            ['f', 'n', ..] ->
                consumeToken state Function 2 |> helper

            ['(', ..] ->
                consumeToken state LParen 1 |> helper

            [')', ..] ->
                consumeToken state RParen 1 |> helper

            ['{', ..] ->
                consumeToken state LBrace 1 |> helper

            ['}', ..] ->
                consumeToken state RBrace 1 |> helper

            ['=', ..] ->
                consumeToken state Assign 1 |> helper

            ['+', ..] ->
                consumeToken state Plus 1 |> helper

            [',', ..] ->
                consumeToken state Comma 1 |> helper

            [';', ..] ->
                consumeToken state Semicolon 1 |> helper

            ['\r', ..] | ['\n', ..] | ['\t', ..] | [' ', ..] ->
                nextRemaining = List.drop state.remaining 1
                nextIndex = state.index + 1
                { tokens: state.tokens, remaining: nextRemaining, index: nextIndex } |> helper

            [ch, ..] if isLetter ch ->
                consumeToken state Ident (identLength state.remaining 1) |> helper

            [ch, ..] if isDigit ch ->
                consumeToken state Int (intLength state.remaining 1) |> helper

            [_, ..] ->
                consumeToken state Illegal 1 |> helper

            [] ->
                List.append state.tokens { kind: Eof, index: state.index }

    helper { tokens: List.withCapacity 1024, remaining: bytes, index: 0 }

consumeToken = \{ tokens, remaining, index }, kind, size ->
    nextTokens = List.append tokens { kind, index }
    nextRemaining = List.drop remaining (Num.toNat size)
    nextIndex = index + size
    { tokens: nextTokens, remaining: nextRemaining, index: nextIndex }

identLength = \remaining, size ->
    when List.get remaining (Num.toNat size) is
        Ok ch if isLetter ch ->
            identLength remaining (size + 1)

        _ ->
            size

intLength = \remaining, size ->
    when List.get remaining (Num.toNat size) is
        Ok ch if isDigit ch ->
            identLength remaining (size + 1)

        _ ->
            size

isLetter = \ch ->
    (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') || ch == '_'

isDigit = \ch ->
    ch >= '0' && ch <= '9'

getIdent = \bytes, index ->
    len = identLength (List.drop bytes (Num.toNat index)) 1
    List.sublist bytes { start: Num.toNat index, len }

getInt = \bytes, index ->
    len = intLength (List.drop bytes (Num.toNat index)) 1
    List.sublist bytes { start: Num.toNat index, len }

expect
    lexed = lex (Str.toUtf8 "") |> List.map .kind
    expected = [Eof]

    lexed == expected

expect
    lexed = lex (Str.toUtf8 "=+(){},;") |> List.map .kind
    expected = [
        Assign,
        Plus,
        LParen,
        RParen,
        LBrace,
        RBrace,
        Comma,
        Semicolon,
        Eof,
    ]

    lexed == expected

expect
    bytes =
        Str.toUtf8
            """
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
                x + y;
            };
            let result = add(five, ten);
            """
    lexed = lex bytes
    kinds = List.map lexed .kind
    expectedKinds = [
        Let,
        Ident,
        Assign,
        Int,
        Semicolon,
        Let,
        Ident,
        Assign,
        Int,
        Semicolon,
        Let,
        Ident,
        Assign,
        Function,
        LParen,
        Ident,
        Comma,
        Ident,
        RParen,
        LBrace,
        Ident,
        Plus,
        Ident,
        Semicolon,
        RBrace,
        Semicolon,
        Let,
        Ident,
        Assign,
        Ident,
        LParen,
        Ident,
        Comma,
        Ident,
        RParen,
        Semicolon,
        Eof,
    ]

    idents =
        lexed
        |> List.keepIf \{ kind } -> kind == Ident
        |> List.map \{ index } -> getIdent bytes index

    expectedIdents = [
        Str.toUtf8 "five",
        Str.toUtf8 "ten",
        Str.toUtf8 "add",
        Str.toUtf8 "x",
        Str.toUtf8 "y",
        Str.toUtf8 "x",
        Str.toUtf8 "y",
        Str.toUtf8 "result",
        Str.toUtf8 "add",
        Str.toUtf8 "five",
        Str.toUtf8 "ten",
    ]

    ints =
        lexed
        |> List.keepIf \{ kind } -> kind == Int
        |> List.map \{ index } -> getInt bytes index

    expectedInts = [
        Str.toUtf8 "5",
        Str.toUtf8 "10",
    ]

    kinds == expectedKinds && idents == expectedIdents && ints == expectedInts
