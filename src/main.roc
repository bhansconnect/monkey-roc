app "🐵🤘🏼"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.3.2/tE4xS_zLdmmxmHwHih9kHWQ7fsXtJr7W7h3425-eZFk.tar.br" }
    imports [pf.Arg, pf.File, pf.Path, pf.Process, pf.Stderr, pf.Stdout, pf.Task, Repl, Lexer]
    provides [main] to pf

main =
    # TODO: Add in arg parsing to enable more flexible use.
    task =
        args <- Arg.list |> Task.await
        when args is
            [_, monkeyFile] ->
                path = Path.fromStr monkeyFile
                bytes <- File.readBytes path |> Task.await
                {} <- Stderr.line "Lexed file is:" |> Task.await

                out =
                    bytes
                    |> Lexer.lex
                    |> \lexedData -> Lexer.debugPrint [] lexedData
                    |> Str.fromUtf8
                    |> Result.withDefault "Bad Utf8\n"
                Stderr.write out

            _ ->
                {} <- Stdout.line "Hello! This is the Monkey programming language!" |> Task.await
                {} <- Stdout.line "Feel free to type in commands" |> Task.await
                Repl.run

    result <- Task.attempt task
    when result is
        Ok {} ->
            Process.exit 0

        Err err ->
            msg =
                when err is
                    FileReadErr _ _ -> "Error reading input file"
                    NoFile -> "Please pass in a monkey file to run"

            {} <- Stderr.line msg |> Task.await
            Process.exit 1
