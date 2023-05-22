interface Parser
    exposes [parse]
    imports [Lexer.{ LexedData }]

# TODO: program could be a node.
# It would just reference a range of nodes that make up the statements of the program.
Program : List U32

# We are skipping parsing into a error message friendly structure.
# In a proper setup, every node should reference a NodeIndex or TokenIndex,
# such that it can eventually resolve to an exact line/col number.
# The Monkey interpreter in the book does not track this info.
# Neither will we, at least for now.
# This structure is more setup for execution speed.
Node : [
    Let { ident : U32, expr : U32 },

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

parse : LexedData -> Result ParsedData Errors
parse = \_ -> Ok { program: [], nodes: [] }
