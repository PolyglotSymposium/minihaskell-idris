module Parser

import Lexer
import Syntax

Parser : Type -> Type
Parser o = List Token -> Maybe (o, List Token)

alt : List (Parser a) -> List Token -> Maybe (a, List Token)
alt [] _ = Nothing
alt (p :: ps) toks =
  case p toks of
       e@(Just _) => e
       _ => alt ps toks

many : Parser a -> Parser (List a)
many p =
  \toks =>
          case p toks of
               (Just (r, [])) => Just ([r], [])
               (Just (r, (x::xs))) => case many p xs of
                                           Nothing => Just ([], toks)
                                           Just (rs, remainder) => Just (r::rs, remainder)
               Nothing => Just ([], toks)

nil : Parser Expr

parenExpr : Parser Expr

pair : Parser Expr

nonApp : Parser Expr
nonApp (VAR name::xs) = Just (Var name, xs)
nonApp (TRUE::xs) = Just (EBool True, xs)
nonApp (INT v::xs) = Just (EInt v, xs)
nonApp x = alt [nil, parenExpr, pair] x

app : Parser Expr
app (FST::rest) = case nonApp rest of
                       Just (e, rest) => Just (Fst e, rest)
                       Nothing => Nothing
app (SND::rest) = case nonApp rest of
                       Just (e, rest) => Just (Snd e, rest)
                       Nothing => Nothing
app toks = case nonApp toks of
                Just (e, rest) => case nonApp rest of
                                       Just (e2, remainder) => Just (Apply e e2, remainder)
                                       Nothing => Nothing
                Nothing => case app toks of
                                Just (e, rest) => case nonApp rest of
                                                       Just (e2, remainder) => Just (Apply e e2, remainder)
                                                       Nothing => Nothing
                                Nothing => ?help_1

arith : Parser Expr

boolean : Parser Expr

cons : Parser Expr

ifElse : Parser Expr

fun : Parser Expr

rec : Parser Expr

match : Parser Expr

expr : Parser Expr
expr = alt [nonApp, app, arith, boolean, cons, ifElse, fun, rec, match]

letTop : Parser ToplevelCommand
letTop (LET::(VAR name)::EQUAL::rest) =
  case expr rest of
       Just (e, remainder) => Just (TlDef name e, remainder)
       _ => Nothing

exprTop : Parser ToplevelCommand
cmdTop : Parser ToplevelCommand

parseFile : Parser (List ToplevelCommand)
parseFile [] = Just ([], [])
parseFile (x :: xs) =
  many (alt [letTop, exprTop, cmdTop]) (x :: xs)
