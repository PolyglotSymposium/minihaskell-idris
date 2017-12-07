module Main

import TypeCheck
import Syntax
import Lexer
import Parser
import Interpret

parse : String -> Maybe (List ToplevelCommand)
parse text = fst <$> tokenize text >>= parseFile

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
                      Nothing => pure Nothing
exec ctx env (TlDef x e) =
  case typeOf ctx e of
       Just ty => do
         putStrLn $ concat ["val ", x, " : ", stringOfType ty]
         pure $ Just ((x, ty)::ctx, (x, VClosure env e)::env)
       Nothing => pure Nothing
exec ctx env _ = pure Nothing

execAll : List ToplevelCommand -> IO ()
execAll xs = go [] [] xs
  where
    go : Env -> Context -> List ToplevelCommand -> IO ()
    go env ctx [] = pure ()
    go env ctx (c :: cmds) = do
      r <- exec ctx env c
      case r of
           Nothing => pure ()
           (Just (ctx', env')) => go env' ctx' cmds

main : IO ()
main = do
  args <- getArgs
  case args of
       _::file::[] => do
         res <- readFile file
         case res of
              (Left _) => putStrLn "Cannot read file"
              (Right text) =>
                             case parse text of
                                  Just cmds => execAll cmds
                                  Nothing => putStrLn "Parse error"
       _ => putStrLn "Needed some args"
