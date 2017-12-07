module Parser

import Lexer
import Syntax

%access public export

Parser : Type -> Type
Parser o = List Token -> Maybe (o, List Token)

alt : List (Parser a) -> List Token -> Maybe (a, List Token)
alt [] _ = Nothing
alt (p :: ps) toks =
  case p toks of
       e@(Just _) => e
       _ => alt ps toks

many : Parser a -> Parser (List a)
many p toks =
  case p toks of
       (Just (r, [])) => Just ([r], [])
       (Just (r, (x::xs))) => case many p xs of
                                   Just (rs, remainder) => Just (r::rs, remainder)
                                   _ => Just ([], toks)
       _ => Just ([], toks)

mutual
  expr : Parser Expr
  expr = alt [nonApp, app, arith, boolean, cons, ifElse, fun, rec, match]

  parenExpr : Parser Expr
  parenExpr (LPAREN::toks) =
    case expr toks of
       Just (e, RPAREN::moreToks) => Just (e, moreToks)
       _ => Nothing
  parenExpr _ = Nothing

  pair : Parser Expr
  pair (LPAREN::toks) =
    case expr toks of
       Just (e1, COMMA::toks') =>
         case expr toks' of
            Just (e2, RPAREN::finalToks) => Just (Pair e1 e2, finalToks)
            _ => Nothing
       _ => Nothing
  pair _ = Nothing

  nonApp : Parser Expr
  nonApp (VAR name::xs) = Just (Var name, xs)
  nonApp (TRUE::xs) = Just (EBool True, xs)
  nonApp (INT v::xs) = Just (EInt v, xs)
  nonApp x = alt [nil, parenExpr, pair] x

  app : Parser Expr
  app (FST::rest) = case nonApp rest of
                         Just (e, rest) => Just (Fst e, rest)
                         _ => Nothing
  app (SND::rest) = case nonApp rest of
                         Just (e, rest) => Just (Snd e, rest)
                         _ => Nothing
  app toks = case nonApp toks of
                  Just (e, rest) => case nonApp rest of
                                         Just (e2, remainder) => Just (Apply e e2, remainder)
                                         _ => Nothing
                  _ => case app toks of
                                  Just (e, rest) => case nonApp rest of
                                                         Just (e2, remainder) => Just (Apply e e2, remainder)
                                                         _ => Nothing
                                  _ => Nothing

  nil : Parser Expr
  nil (LBRACK::toks) =
    case ty toks of
       Just (t, RBRACK::moreToks) => Just (ENil t, moreToks)
       _ => Nothing
  nil _ = Nothing

  arith : Parser Expr
  arith (MINUS::INT v::rest) = Just (EInt (-v), rest)
  arith toks =
    case expr toks of
         Just (e1, PLUS::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Plus e1 e2, finalToks)
                             _ => Nothing
         Just (e1, MINUS::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Minus e1 e2, finalToks)
                             _ => Nothing
         Just (e1, TIMES::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Times e1 e2, finalToks)
                             _ => Nothing
         Just (e1, DIVIDE::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Divide e1 e2, finalToks)

                             _ => Nothing
         Just (e1, MOD::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Mod e1 e2, finalToks)
                             _ => Nothing
         _ => Nothing

  boolean : Parser Expr
  boolean toks =
    case expr toks of
         Just (e1, EQUAL::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Equal e1 e2, finalToks)
                             _ => Nothing
         Just (e1, LESS::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Less e1 e2, finalToks)
                             _ => Nothing
         _ => Nothing

  cons : Parser Expr
  cons toks =
    case expr toks of
         Just (e1, CONS::moreToks) =>
                        case expr moreToks of
                             Just (e2, finalToks) => Just (Cons e1 e2, finalToks)
                             _ => Nothing
         _ => Nothing

  ifElse : Parser Expr
  ifElse (IF::toks) =
    case expr toks of
         Just (e1, THEN::moreToks) =>
                        case expr moreToks of
                             Just (e2, ELSE::yetMoreToks) =>
                                             case expr yetMoreToks of
                                                  Just (e3, finalToks) => Just (If e1 e2 e3, finalToks)
                                                  _ => Nothing
                             _ => Nothing
         _ => Nothing
  ifElse _ = Nothing

  tyListForReal : Parser HType
  tyListForReal toks =
    case tyList toks of
      Just (t, TLIST::toks) => Just (TList t, toks)
      _ => Nothing

  tySimple : Parser HType
  tySimple (TBOOL::toks) = Just (TBool, toks)
  tySimple (TINT::toks) = Just (TInt, toks)
  tySimple (LPAREN::toks) =
    case ty toks of
      Just (t, RPAREN::toks) => Just (t, toks)
      _ => Nothing
  tySimple _ = Nothing

  tyList : Parser HType
  tyList = alt [tySimple, tyListForReal]

  tyTimesForReal : Parser HType
  tyTimesForReal toks =
    case tyTimes toks of
      Just (t1, TIMES::toks') =>
        case tyTimes toks' of
           Just (t2, finalToks) => Just (TTimes t1 t2, finalToks)
           _ => Nothing
      _ => Nothing

  tyTimes : Parser HType
  tyTimes = alt [tyList, tyTimesForReal]

  arrow : Parser HType
  arrow toks =
    case tyTimes toks of
      Just (t1, TARROW::toks') =>
        case ty toks' of
           Just (t2, finalToks) => Just (TArrow t1 t2, finalToks)
           _ => Nothing
      _ => Nothing

  ty : Parser HType
  ty = alt [tyTimes, arrow]

  fun : Parser Expr
  fun (FUN::VAR name::COLON::toks) =
    case ty toks of
         Just (t, DARROW::moreToks) =>
                        case expr moreToks of
                             Just (e, finalToks) => Just (Fun name t e, finalToks)
                             _ => Nothing
         _ => Nothing
  fun _ = Nothing

  rec : Parser Expr
  rec (REC::VAR name::COLON::toks) =
    case ty toks of
         Just (t, IS::moreToks) =>
                        case expr moreToks of
                             Just (e, finalToks) => Just (Rec name t e, finalToks)
                             _ => Nothing
         _ => Nothing
  rec _ = Nothing

  match : Parser Expr
  match (MATCH::toks) =
    case expr toks of
      Just (e1, WITH::toks') =>
        case nil toks' of
          Just (ENil t, DARROW::toks'') =>
            case expr toks'' of
              Just (e2, ALTERNATIVE::VAR n1::CONS::VAR n2::DARROW::toks''') =>
                case expr toks''' of
                  Just (e3, finalToks) => Just (Match e1 t e2 n1 n2 e3, finalToks)
                  _ => Nothing
              _ => Nothing
          _ => Nothing
      _ => Nothing
  match _ = Nothing

letTop : Parser ToplevelCommand
letTop (LET::(VAR name)::EQUAL::rest) =
  case expr rest of
       Just (e, SEMICOLON2::remainder) => Just (TlDef name e, remainder)
       _ => Nothing
letTop _ = Nothing

exprTop : Parser ToplevelCommand
exprTop toks =
  case expr toks of
       Just (e, SEMICOLON2::remainder) => Just (TlExpr e, remainder)
       _ => Nothing

cmdTop : Parser ToplevelCommand
cmdTop (QUIT::remainder) = Just (TlQuit, remainder)
cmdTop _ = Nothing

parseFile : Parser (List ToplevelCommand)
parseFile [] = Just ([], [])
parseFile (x :: xs) =
  many (alt [letTop, exprTop, cmdTop]) (x :: xs)
