module [run]

import cli.Stdout
import cli.Stdin
import Lexer
import Parser
import Eval

run =
    Task.loop ([Eval.newEnv {}]) \envs ->

        Stdout.write! ">> "
        line = Stdin.line!

        parseResults =
            line
            |> Str.toUtf8
            |> Lexer.lex
            |> Parser.parse

        when parseResults is
            Ok parsedData ->
                (nextEnvs, val) =
                    parsedData
                    |> Eval.evalWithEnvs envs
                Stdout.line! (Eval.printValue val)

                Task.ok (Step nextEnvs)

            Err errs ->
                errs
                    |> Str.joinWith "\n\t"
                    |> \e -> "Parse Errors:\n\t$(e)"
                    |> Stdout.line!

                Task.ok (Step envs)
