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

public export
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

    mutual
      go : List Char -> Maybe (List Token)
      go [] = Just []
      go ('\n' :: xs) = identFirst xs
      go ('\t' :: xs) = identFirst xs
      go (' ' :: xs) = identFirst xs
      go ('b'::'o'::'o'::'l'::xs) = ((::) TBOOL) <$> identFirst xs
      go ('e'::'l'::'s'::'e'::xs) = ((::) ELSE) <$> identFirst xs
      go ('f'::'a'::'l'::'s'::'e'::xs) = ((::) FALSE) <$> identFirst xs
      go ('f'::'s'::'t'::xs) = ((::) FST) <$> identFirst xs
      go ('f'::'u'::'n'::xs) = ((::) FUN) <$> identFirst xs
      go ('i'::'f'::xs) = ((::) IF) <$> identFirst xs
      go ('i'::'n'::'t'::xs) = ((::) TINT) <$> identFirst xs
      go ('i'::'s'::xs) = ((::) IS) <$> identFirst xs
      go ('l'::'e'::'t'::xs) = ((::) LET) <$> identFirst xs
      go ('l'::'i'::'s'::'t'::xs) = ((::) TLIST) <$> identFirst xs
      go ('m'::'a'::'t'::'c'::'h'::xs) = ((::) MATCH) <$> identFirst xs
      go ('r'::'e'::'c'::xs) = ((::) REC) <$> identFirst xs
      go ('s'::'n'::'d'::xs) = ((::) SND) <$> identFirst xs
      go ('t'::'h'::'e'::'n'::xs) = ((::) THEN) <$> identFirst xs
      go ('t'::'r'::'u'::'e'::xs) = ((::) TRUE) <$> identFirst xs
      go (':'::'q'::'u'::'i'::'t'::xs) = ((::) QUIT) <$> identFirst xs
      go ('w'::'i'::'t'::'t'::xs) = ((::) WITH) <$> identFirst xs
      go ('-'::'>'::xs) = ((::) TARROW) <$> identFirst xs
      go ('='::'>'::xs) = ((::) DARROW) <$> identFirst xs
      go (':'::':'::xs) = ((::) CONS) <$> identFirst xs
      go (';'::';'::xs) = ((::) SEMICOLON2) <$> identFirst xs
      go ('%'::xs) = ((::) MOD) <$> identFirst xs
      go ('('::xs) = ((::) LPAREN) <$> identFirst xs
      go (')'::xs) = ((::) RPAREN) <$> identFirst xs
      go ('*'::xs) = ((::) TIMES) <$> identFirst xs
      go ('+'::xs) = ((::) PLUS) <$> identFirst xs
      go (','::xs) = ((::) COMMA) <$> identFirst xs
      go ('-'::xs) = ((::) MINUS) <$> identFirst xs
      go ('/'::xs) = ((::) DIVIDE) <$> identFirst xs
      go (':'::xs) = ((::) COLON) <$> identFirst xs
      go ('<'::xs) = ((::) LESS) <$> identFirst xs
      go ('='::xs) = ((::) EQUAL) <$> identFirst xs
      go ('['::xs) = ((::) LBRACK) <$> identFirst xs
      go (']'::xs) = ((::) RBRACK) <$> identFirst xs
      go ('|'::xs) = ((::) ALTERNATIVE) <$> identFirst xs
      go (c::xs) =
       if c `elem` number
       then
         let
           (x, rest) = slurpNumber (c::xs)
         in
           ((::) (INT x)) <$> identFirst rest
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
