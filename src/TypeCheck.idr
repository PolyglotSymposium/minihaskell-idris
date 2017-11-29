module TypeCheck

import Syntax

typeError : Maybe a
typeError = Nothing

Context : Type
Context = List (Name, HType)

mutual
  check : Context -> HType -> Expr -> Maybe ()
  check ctx ty e =
    case typeOf ctx e of
      Just ty' => 
        if ty' /= ty
        then typeError
        else Just ()
      _ => typeError

  typeOf : Context -> Expr -> Maybe HType
  typeOf x (Var y) = lookup y x
  typeOf x (EInt y) = Just TInt
  typeOf x (Bool y) = Just TBool
  typeOf x (ENil y) = Just $ TList y
  typeOf x (Times y z) = do
     _ <- check x TInt y
     _ <- check x TInt z
     Just TInt
  typeOf x (Divide y z) = do
     _ <- check x TInt y
     _ <- check x TInt z
     Just TInt
  typeOf x (Mod y z) = do
     _ <- check x TInt y
     _ <- check x TInt z
     Just TInt
  typeOf x (Plus y z) = do
     _ <- check x TInt y
     _ <- check x TInt z
     Just TInt
  typeOf ctx (Cons e1 e2) = do
    ty <- typeOf ctx e1
    _ <- check ctx (TList ty) e2 
    pure (TList ty)
  typeOf x (Minus y z) = do
     _ <- check x TInt y
     _ <- check x TInt z
     Just TInt
  typeOf x (Equal y z) = do
     _ <- check x TInt y
     _ <- check x TInt z
     Just TInt
  typeOf x (Less y z) = do
     _ <- check x TInt y
     _ <- check x TInt z
     Just TInt
  typeOf ctx (If e1 e2 e3) = do
    _ <- check ctx Syntax.TBool e1
    ty <- typeOf ctx e2
    _ <- check ctx ty e3
    pure ty

  typeOf ctx (Fun x ty e) = TArrow ty <$> (typeOf ((x, ty)::ctx) e)
  typeOf ctx (Apply e1 e2) = do
    v <- typeOf ctx e1
    case v of
      TArrow ty1 ty2 => do
        _ <- check ctx ty1 e2
        pure ty2
      _ => typeError

  typeOf ctx (Pair e1 e2) = do
    t1 <- typeOf ctx e1
    t2 <- typeOf ctx e2
    pure $ TTimes t1 t2
  typeOf ctx (Fst e) = do
    r <- typeOf ctx e
    case r of
      TTimes ty1 _ => pure ty1
      _ => typeError

  typeOf ctx (Snd e) = do
    r <- typeOf ctx e
    case r of
      TTimes _ ty2 => pure ty2
      _ => typeError

  typeOf ctx (Rec x ty e) = do
    _ <- check ((x, ty)::ctx) ty e
    pure ty
  typeOf ctx (Match e1 ty e2 x y e3) = 
    case typeOf ctx e1 of
      Just (TList ty1) => do
        _ <- check ctx (TList ty) e1
        ty2 <- typeOf ctx e2
        _ <- check ((x, ty)::(y, TList ty)::ctx) ty2 e3
        pure ty2
      _ => typeError
