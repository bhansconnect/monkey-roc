app [main] { cli: platform "https://github.com/roc-lang/basic-cli/releases/download/0.15.0/SlwdbJ-3GR7uBWQo6zlmYWNYOxnvo8r6YABXD-45UOw.tar.br" }

import cli.Arg
import cli.File
import cli.Stderr
import cli.Stdout

import Repl
import Lexer
import Parser
import Eval

main =
    # TODO: Add in arg parsing to enable more flexible use.
    task =
        args = Arg.list! {}
        when args is
            [_, monkeyFile] ->
                bytes = File.readBytes! monkeyFile

                parseResults =
                    bytes
                    |> Lexer.lex
                    |> Parser.parse

                when parseResults is
                    Ok parsedData ->
                        parsedData
                        |> Eval.eval
                        |> .1
                        |> Eval.printValue
                        |> Stdout.line

                    Err errs ->
                        errs
                        |> Str.joinWith "\n\t"
                        |> \e -> "Parse Errors:\n\t$(e)"
                        |> Stderr.line

            _ ->
                Stdout.line! "Hello! This is the Monkey programming language!"
                Stdout.line! "Feel free to type in commands"
                Repl.run

    result = Task.result! task
    when result is
        Ok {} ->
            Task.ok {}

        Err err ->
            msg =
                when err is
                    FileReadErr _ _ -> "Error reading input file"
                    StdinErr _ -> "Error reading from stdin"
                    StdoutErr _ -> "Error printing to stdout"
                    StderrErr _ -> "Error printing to stderr"

            Stderr.line! msg
            Task.err (Exit 1 "")
