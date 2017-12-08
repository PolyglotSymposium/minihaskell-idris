module Interpret

import Syntax

%access public export

mutual
  data Value : Type where
    VInt : Int -> Value
    VBool : Bool -> Value
    VNil : HType -> Value
    VClosure : Env -> Expr -> Value

  Env : Type
  Env = List (Name, Value)

runtimeError : Maybe a
runtimeError = Nothing

interp : Env -> Expr -> Maybe Value
interp x (Var y) =
  case lookup y x of
    Just (VClosure env' e) =>
      do
        v <- interp env' e
        interp ((y, v)::x) e

    Just v => Just v
    Nothing => runtimeError
interp x (EInt y) = Just $ VInt y
interp x (EBool y) = Just $ VBool y
interp x (Times y z) =
  case (interp x y, interp x z) of
    (Just (VInt a), Just (VInt b)) => Just (VInt (a * b))
    _ => runtimeError
interp x (Divide y z) =
  case (interp x y, interp x z) of
    (Just (VInt a), Just (VInt 0)) => runtimeError
    (Just (VInt a), Just (VInt b)) => Just (VInt (a `div` b))
    _ => runtimeError
interp x (Mod y z) =
  case (interp x y, interp x z) of
    (Just (VInt a), Just (VInt 0)) => runtimeError
    (Just (VInt a), Just (VInt b)) => Just (VInt (a `mod` b))
    _ => runtimeError
interp x (Plus y z) =
  case (interp x y, interp x z) of
    (Just (VInt a), Just (VInt b)) => Just (VInt (a + b))
    _ => runtimeError
interp x (Minus y z) =
  case (interp x y, interp x z) of
    (Just (VInt a), Just (VInt b)) => Just (VInt (a - b))
    _ => runtimeError
interp x (Equal y z) =
  case (interp x y, interp x z) of
    (Just (VInt a), Just (VInt b)) => Just (VBool (a == b))
    _ => runtimeError
interp x (Less y z) =
  case (interp x y, interp x z) of
    (Just (VInt a), Just (VInt b)) => Just (VBool (a < b))
    _ => runtimeError
interp x (If y z w) =
  case interp x y of
    Just (VBool True) => interp x z
    Just (VBool False) => interp x w
    _ => runtimeError
interp x e@(Fun y z w) = Just $ VClosure x e
interp env (Apply e1 e2) =
  case interp env e1 of
    Just (VClosure env' (Fun x _ e)) => interp ((x, VClosure env e2)::env') e
    _ => runtimeError

interp x e@(Pair y z) = Just $ VClosure x e
interp x (Fst y) =
  case interp x y of
    Just (VClosure env' (Syntax.Pair e1 e2)) => interp env' e1
    _ => runtimeError
interp x (Snd y) =
  case interp x y of
    Just (VClosure env' (Syntax.Pair e1 e2)) => interp env' e2
    _ => runtimeError
interp env (Rec x _ e) = interp env' e
  where
    env' = (x, VClosure env' e) :: env
interp x (ENil y) = Just $ VNil y
interp x e@(Cons y z) = Just $ VClosure x e
interp env (Match e1 _ e2 x y e3) =
  case interp env e1 of
    Just (VNil _) => interp env e2
    Just (VClosure env' (Cons d1 d2)) =>
			interp ((x, VClosure env' d1)::(y, VClosure env' d2)::env) e3
    _ => runtimeError

printResult : Nat -> Value -> List String
printResult Z _ = ["..."]
printResult (S k) (VInt x) = [show x]
printResult (S k) (VBool True) = ["true"]
printResult (S k) (VBool False) = ["false"]
printResult (S k) (VNil x) = ["[" ++ stringOfType x ++ "]"]
printResult (S k) (VClosure env (Cons e1 e2)) =
  case interp env e1 of
    Just v1@(VClosure _ (Cons _ _)) =>
      ["("] ++ printResult ((S k) `divNat` 2) v1 ++ [")"]
    Just x =>
      case interp env e2 of
        Just y => printResult ((S k) `divNat` 2) x ++ [" :: "] ++ printResult k y
        _ => ["error!"]
    Nothing => ["error!"]
printResult (S k) (VClosure xs (Fun x y z)) = ["<fun>"]
printResult (S k) _ = ["?"]
