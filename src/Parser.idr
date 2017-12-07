module Parser

import Lexer
import Syntax

%access public export

Parser : Type -> Type
Parser o = List Token -> Either String (o, List Token)

alt : List (Parser a) -> Parser a
alt [] _ = Left "No alternatives matched"
alt (p :: ps) toks =
  case p toks of
       e@(Right _) => e
       _ => alt ps toks

many : Parser a -> Parser (List a)
many p toks =
  case p toks of
    (Right (r, [])) => Right ([r], [])
    (Right (r, xs)) =>
      case many p xs of
        Right (rs, remainder) => Right (r::rs, remainder)
        _ => Right ([r], xs)
    _ => Right ([], toks)

mutual
  expr : Parser Expr
  expr = alt [nonApp, app, arith, boolean, cons, ifElse, fun, rec, match]

  parenExpr : Parser Expr
  parenExpr (LPAREN::toks) =
    case expr toks of
       Right (e, RPAREN::moreToks) => Right (e, moreToks)
       Right _ => Left "No closing paren"
       Left e => Left e
  parenExpr _ = Left "No open paren"

  pair : Parser Expr
  pair (LPAREN::toks) =
    case expr toks of
       Right (e1, COMMA::toks') =>
         case expr toks' of
            Right (e2, RPAREN::finalToks) => Right (Pair e1 e2, finalToks)
            Left e => Left e
       Left e => Left e
  pair _ = Left "No open paren"

  nonApp : Parser Expr
  nonApp (VAR name::xs) = Right (Var name, xs)
  nonApp (TRUE::xs) = Right (EBool True, xs)
  nonApp (FALSE::xs) = Right (EBool False, xs)
  nonApp (INT v::xs) = Right (EInt v, xs)
  nonApp x = alt [nil, parenExpr, pair] x

  app : Parser Expr
  app (FST::rest) = case nonApp rest of
                         Right (e, rest) => Right (Fst e, rest)
                         Left e => Left e
  app (SND::rest) = case nonApp rest of
                         Right (e, rest) => Right (Snd e, rest)
                         Left e => Left e
  app toks = case nonApp toks of
                  Right (e, rest) => case nonApp rest of
                                         Right (e2, remainder) => Right (Apply e e2, remainder)
                                         Left e => Left e
                  _ => case app toks of
                                  Right (e, rest) => case nonApp rest of
                                                         Right (e2, remainder) => Right (Apply e e2, remainder)
                                                         Left e => Left e
                                  Left e => Left e

  nil : Parser Expr
  nil (LBRACK::toks) =
    case ty toks of
       Right (t, RBRACK::moreToks) => Right (ENil t, moreToks)
       Right _ => Left "No right bracket"
       Left e => Left e
  nil _ = Left "No left bracket"

  arith : Parser Expr
  arith (MINUS::INT v::rest) = Right (EInt (-v), rest)
  arith toks =
    case expr toks of
         Right (e1, PLUS::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Plus e1 e2, finalToks)
                             Left e => Left e
         Right (e1, MINUS::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Minus e1 e2, finalToks)
                             Left e => Left e
         Right (e1, TIMES::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Times e1 e2, finalToks)
                             Left e => Left e
         Right (e1, DIVIDE::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Divide e1 e2, finalToks)
                             Left e => Left e
         Right (e1, MOD::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Mod e1 e2, finalToks)
                             Left e => Left e
         Left e => Left e

  boolean : Parser Expr
  boolean toks =
    case expr toks of
         Right (e1, EQUAL::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Equal e1 e2, finalToks)
                             Left e => Left e
         Right (e1, LESS::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Less e1 e2, finalToks)
                             Left e => Left e
         Right _ => Left "No boolean operator"
         Left e => Left e

  cons : Parser Expr
  cons toks =
    case expr toks of
         Right (e1, CONS::moreToks) =>
                        case expr moreToks of
                             Right (e2, finalToks) => Right (Cons e1 e2, finalToks)
                             Left e => Left e
         Right _ => Left "No cons"
         Left e => Left e

  ifElse : Parser Expr
  ifElse (IF::toks) =
    case expr toks of
      Right (e1, THEN::moreToks) =>
        case expr moreToks of
          Right (e2, ELSE::yetMoreToks) =>
            case expr yetMoreToks of
              Right (e3, finalToks) => Right (If e1 e2 e3, finalToks)
              Left e => Left e
          Right _ => Left "No else"
          Left e => Left e
      Right _ => Left "No then"
      Left e => Left e
  ifElse _ = Left "No if"

  tyListForReal : Parser HType
  tyListForReal toks =
    case tyList toks of
      Right (t, TLIST::toks) => Right (TList t, toks)
      Right _ => Left "No Tlist"
      Left e => Left e

  tySimple : Parser HType
  tySimple (TBOOL::toks) = Right (TBool, toks)
  tySimple (TINT::toks) = Right (TInt, toks)
  tySimple (LPAREN::toks) =
    case ty toks of
      Right (t, RPAREN::toks) => Right (t, toks)
      Right _ => Left "No closing paren"
      Left e => Left e
  tySimple _ = Left "No type starters"

  tyList : Parser HType
  tyList = alt [tySimple, tyListForReal]

  tyTimesForReal : Parser HType
  tyTimesForReal toks =
    case tyTimes toks of
      Right (t1, TIMES::toks') =>
        case tyTimes toks' of
           Right (t2, finalToks) => Right (TTimes t1 t2, finalToks)
           Left e => Left e
      Right _ => Left "No times"
      Left e => Left e

  tyTimes : Parser HType
  tyTimes = alt [tyList, tyTimesForReal]

  arrow : Parser HType
  arrow toks =
    case tyTimes toks of
      Right (t1, TARROW::toks') =>
        case ty toks' of
           Right (t2, finalToks) => Right (TArrow t1 t2, finalToks)
           Left e => Left e
      Right _ => Left "No arrow"
      Left e => Left e

  ty : Parser HType
  ty = alt [tyTimes, arrow]

  fun : Parser Expr
  fun (FUN::VAR name::COLON::toks) =
    case ty toks of
         Right (t, DARROW::moreToks) =>
                        case expr moreToks of
                             Right (e, finalToks) => Right (Fun name t e, finalToks)
                             Left e => Left e
         Right _ => Left "No arrow"
         Left e => Left e
  fun _ = Left "No fun"

  rec : Parser Expr
  rec (REC::VAR name::COLON::toks) =
    case ty toks of
         Right (t, IS::moreToks) =>
                        case expr moreToks of
                             Right (e, finalToks) => Right (Rec name t e, finalToks)
                             Left e => Left e
         Right _ => Left "No is"
         Left e => Left e
  rec _ = Left "No rec"

  match : Parser Expr
  match (MATCH::toks) =
    case expr toks of
      Right (e1, WITH::toks') =>
        case nil toks' of
          Right (ENil t, DARROW::toks'') =>
            case expr toks'' of
              Right (e2, ALTERNATIVE::VAR n1::CONS::VAR n2::DARROW::toks''') =>
                case expr toks''' of
                  Right (e3, finalToks) => Right (Match e1 t e2 n1 n2 e3, finalToks)
                  Left e => Left e
              Left e => Left e
          Left e => Left e
      Left e => Left e
  match _ = Left "No match"

letTop : Parser ToplevelCommand
letTop (LET::(VAR name)::EQUAL::rest) =
  case expr rest of
       Right (e, SEMICOLON2::remainder) => Right (TlDef name e, remainder)
       Right _ => Left "Missing ;;"
       Left e => Left e
letTop _ = Left "No let"

exprTop : Parser ToplevelCommand
exprTop toks =
  case expr toks of
       Right (e, SEMICOLON2::remainder) => Right (TlExpr e, remainder)
       Right _ => Left "Missing ;;"
       Left e => Left e

cmdTop : Parser ToplevelCommand
cmdTop (QUIT::remainder) = Right (TlQuit, remainder)
cmdTop _ = Left "No command"

parseFile : Parser (List ToplevelCommand)
parseFile [] = Right ([], [])
parseFile (x :: xs) =
  many (alt [letTop, exprTop, cmdTop]) (x :: xs)
