interface Repl
    exposes [run]
    imports [pf.Stdout, pf.Stdin, pf.Task, Lexer]

run =
    {} <- Task.loop {}

    {} <- Stdout.write ">> " |> Task.await
    line <- Stdin.line |> Task.await

    out =
        line
        |> Str.toUtf8
        |> Lexer.lex
        |> \lexedData -> Lexer.debugPrint [] lexedData
        |> Str.fromUtf8
        |> Result.withDefault "Bad Utf8\n"
    {} <- Stdout.write out |> Task.await

    Task.succeed (Step {})
