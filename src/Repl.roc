interface Repl
    exposes [run]
    imports [pf.Stdout, pf.Stdin, pf.Task, Lexer, Parser, Eval]

run =
    {} <- Task.loop {}

    {} <- Stdout.write ">> " |> Task.await
    line <- Stdin.line |> Task.await

    parseResults =
        line
        |> Str.toUtf8
        |> Lexer.lex
        |> Parser.parse

    outputTask =
        when parseResults is
            Ok parsedData ->
                parsedData
                |> Eval.eval
                |> Eval.printValue
                |> Stdout.line

            Err errs ->
                errs
                |> Str.joinWith "\n\t"
                |> \e -> "Parse Errors:\n\t\(e)"
                |> Stdout.line

    {} <- outputTask |> Task.await

    Task.succeed (Step {})
