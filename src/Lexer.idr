module Lexer

public export
data Token : Type where
  INT : Int -> Token
  TBOOL : Token
  ELSE : Token
  FALSE : Token
  FST : Token
  FUN : Token
  IF : Token
  TINT : Token
  IS : Token
  LET : Token
  TLIST : Token
  MATCH : Token
  REC : Token
  SND : Token
  THEN : Token
  TRUE : Token
  QUIT : Token
  WITH : Token
  TARROW : Token
  DARROW : Token
  CONS : Token
  SEMICOLON2 : Token
  MOD : Token
  LPAREN : Token
  RPAREN : Token
  TIMES : Token
  PLUS : Token
  COMMA : Token
  MINUS : Token
  DIVIDE : Token
  COLON : Token
  LESS : Token
  EQUAL : Token
  LBRACK : Token
  RBRACK : Token
  ALTERNATIVE : Token
  VAR : String -> Token

keywords : List String
keywords = [
  "bool",
  "else",
  "false",
  "fst",
  "fun",
  "if",
  "int",
  "is",
  "let",
  "list",
  "match",
  "rec",
  "snd",
  "then",
  "true",
  "with"
]

varStart : List Char
varStart = unpack "_abcdefghijklmnopqrstuvwqyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

number : List Char
number = unpack "0123456789"

varRest : List Char
varRest = varStart ++ number

tokenize : String -> Maybe (List Token)
tokenize = identFirst . unpack
  where
    slurpVarRest : List Char -> (List Char, List Char)
    slurpVarRest = break (not . flip elem varRest)

    slurpNumber : List Char -> (Int, List Char)
    slurpNumber xs =
      case break (not . isDigit) xs of
        ([], rest) => (0, rest)
        (xs, rest) => (cast (pack xs), rest)

    go : List Char -> Maybe (List Token)
    go [] = Just []
    go ('\n' :: xs) = go xs
    go ('\t' :: xs) = go xs
    go (' ' :: xs) = go xs
    go ('b'::'o'::'o'::'l'::xs) = ((::) TBOOL) <$> go xs
    go ('e'::'l'::'s'::'e'::xs) = ((::) ELSE) <$> go xs
    go ('f'::'a'::'l'::'s'::'e'::xs) = ((::) FALSE) <$> go xs
    go ('f'::'s'::'t'::xs) = ((::) FST) <$> go xs
    go ('f'::'u'::'n'::xs) = ((::) FUN) <$> go xs
    go ('i'::'f'::xs) = ((::) IF) <$> go xs
    go ('i'::'n'::'t'::xs) = ((::) TINT) <$> go xs
    go ('i'::'s'::xs) = ((::) IS) <$> go xs
    go ('l'::'e'::'t'::xs) = ((::) LET) <$> go xs
    go ('l'::'i'::'s'::'t'::xs) = ((::) TLIST) <$> go xs
    go ('m'::'a'::'t'::'c'::'h'::xs) = ((::) MATCH) <$> go xs
    go ('r'::'e'::'c'::xs) = ((::) REC) <$> go xs
    go ('s'::'n'::'d'::xs) = ((::) SND) <$> go xs
    go ('t'::'h'::'e'::'n'::xs) = ((::) THEN) <$> go xs
    go ('t'::'r'::'u'::'e'::xs) = ((::) TRUE) <$> go xs
    go (':'::'q'::'u'::'i'::'t'::xs) = ((::) QUIT) <$> go xs
    go ('w'::'i'::'t'::'t'::xs) = ((::) WITH) <$> go xs
    go ('-'::'>'::xs) = ((::) TARROW) <$> go xs
    go ('='::'>'::xs) = ((::) DARROW) <$> go xs
    go (':'::':'::xs) = ((::) CONS) <$> go xs
    go (';'::';'::xs) = ((::) SEMICOLON2) <$> go xs
    go ('%'::xs) = ((::) MOD) <$> go xs
    go ('('::xs) = ((::) LPAREN) <$> go xs
    go (')'::xs) = ((::) RPAREN) <$> go xs
    go ('*'::xs) = ((::) TIMES) <$> go xs
    go ('+'::xs) = ((::) PLUS) <$> go xs
    go (','::xs) = ((::) COMMA) <$> go xs
    go ('-'::xs) = ((::) MINUS) <$> go xs
    go ('/'::xs) = ((::) DIVIDE) <$> go xs
    go (':'::xs) = ((::) COLON) <$> go xs
    go ('<'::xs) = ((::) LESS) <$> go xs
    go ('='::xs) = ((::) EQUAL) <$> go xs
    go ('['::xs) = ((::) LBRACK) <$> go xs
    go (']'::xs) = ((::) RBRACK) <$> go xs
    go ('|'::xs) = ((::) ALTERNATIVE) <$> go xs
    go (c::xs) =
     if c `elem` number
     then
       let
         (x, rest) = slurpNumber (c::xs)
       in
         ((::) (INT x)) <$> go rest
     else Nothing

    identFirst : List Char -> Maybe (List Token)
    identFirst [] = Just []
    identFirst (x :: xs) =
     if x `elem` varStart
     then
       let
         (varRest, rest) = slurpVarRest xs
         name = pack (x::varRest)
       in
         if name `elem` keywords
         then go (x::xs)
         else ((::) (VAR name)) <$> go rest
     else
       go (x::xs)
