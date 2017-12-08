module Main

import TypeCheck
import Syntax
import Lexer
import Parser
import Interpret

parse : String -> Either String (List ToplevelCommand)
parse text =
  case tokenize text of
    Just toks => fst <$> parseFile toks
    Nothing => Left "Tokenizer error"

exec : Context -> Env -> ToplevelCommand -> IO (Maybe (Context, Env))
exec ctx env (TlExpr e) =
  case typeOf ctx e of
       Just ty =>
                 case interp env e of
                      Just v => do
                        putStrLn $ concat ["- : ",  stringOfType ty, " = "]
                        putStrLn $ concat $ intersperse "\n" $ printResult 20 v
                        putStrLn $ "@."
                        pure (Just (ctx, env))
                      _ => pure Nothing
       _ => pure Nothing
exec ctx env (TlDef x e) =
  case typeOf ctx e of
       Just ty => do
         putStrLn $ concat ["val ", x, " : ", stringOfType ty]
         pure $ Just ((x, ty)::ctx, (x, VClosure env e)::env)
       _ => pure Nothing
exec _ _ _ = pure Nothing

execAll : Context -> Env -> List ToplevelCommand -> IO (Context, Env)
execAll ctx env [] = pure (ctx, env)
execAll ctx env (c :: cmds) = do
  r <- exec ctx env c
  case r of
    Just (ctx', env') => execAll ctx' env' cmds
    _ => pure (ctx, env)

repl : Context -> Env -> IO ()
repl ctx env = do
  line <- getLine
  case parse line of
    Right cmds => do
      (ctx', env') <- execAll ctx env cmds
      repl ctx' env'
    Left e => do
      putStrLn e
      repl ctx env

main : IO ()
main = repl [] []
