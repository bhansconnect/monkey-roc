interface Repl
    exposes [run]
    imports [pf.Stdout, pf.Stdin, pf.Task, Lexer]

run =
    {} <- Task.loop {}

    {} <- Stdout.write ">> " |> Task.await
    line <- Stdin.line |> Task.await

    bytes = Str.toUtf8 line
    out =
        bytes
        |> Lexer.lex
        |> \tokens -> Lexer.debugPrint [] bytes tokens
        |> Str.fromUtf8
        |> Result.withDefault "Bad Utf8\n"
    {} <- Stdout.write out |> Task.await

    Task.succeed (Step {})
