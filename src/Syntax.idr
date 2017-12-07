module Syntax

%default total

public export
Name : Type
Name = String

public export
data HType : Type where
  TInt : HType
  TBool : HType
  TTimes : HType -> HType -> HType
  TArrow : HType -> HType -> HType
  TList : HType -> HType

public export
Eq HType where
  TInt == TInt = True
  TBool == TBool = True
  (TTimes x1 y1) == (TTimes x2 y2) = x1 == x2 && y1 == y2
  (TArrow x1 y1) == (TArrow x2 y2) = x1 == x2 && y1 == y2
  (TList x1) == (TList x2) = x1 == x2
  _ == _ = False

public export
data Expr : Type where
  Var : Name -> Expr
  EInt : Int -> Expr
  EBool : Bool -> Expr
  Times : Expr -> Expr -> Expr
  Divide : Expr -> Expr -> Expr
  Mod : Expr -> Expr -> Expr
  Plus : Expr -> Expr -> Expr
  Minus : Expr -> Expr -> Expr
  Equal : Expr -> Expr -> Expr
  Less : Expr -> Expr -> Expr
  If : Expr -> Expr -> Expr -> Expr
  Fun : Name -> HType -> Expr -> Expr
  Apply : Expr -> Expr -> Expr
  Pair : Expr -> Expr -> Expr
  Fst : Expr -> Expr
  Snd : Expr -> Expr
  Rec : Name -> HType -> Expr -> Expr
  ENil : HType -> Expr
  Cons : Expr -> Expr -> Expr
  Match : Expr -> HType -> Expr -> Name -> Name -> Expr -> Expr

public export
data ToplevelCommand : Type where
  TlExpr : Expr -> ToplevelCommand
  TlDef : Name -> Expr -> ToplevelCommand
  TlQuit : ToplevelCommand

public export
stringOfType : HType -> String
stringOfType = toStr (-1)
  where
    toStr : Int -> HType -> String
    toStr n ty =
      case go ty of
       (m, str) => if m > n then str else "(" ++ str ++ ")"

      where
        go : HType -> (Int, String)
        go TInt = (4, "int")
        go TBool = (4, "bool")
        go (TList x) = (3, toStr 3 x ++ " list")
        go (TTimes x y) = (2, toStr 2 x ++ " * " ++ toStr 2 y)
        go (TArrow x y) = (1, toStr 1 x ++ " -> " ++ toStr 0 y)

stringOfExpr : Expr -> String
stringOfExpr = toStr (-1)
  where
    toStr : Int -> Expr -> String
    toStr n e =
      case go e of
       (m, str) => if m > n then str else "(" ++ str ++ ")"

      where
        go : Expr -> (Int, String)
        go (EInt x) = (10, cast x)
        go (EBool x) = (10, show x)
        go (Var x) = (10, x)
        go (Pair x y) = (10, "(" ++ toStr 0 x ++ ", " ++ toStr 0 y ++ ")")
        go (ENil x) = (10, "[" ++ (stringOfType x) ++ "]")
        go (Fst x) = (9, "fst " ++ toStr 9 x)
        go (Snd x) = (9, "snd " ++ toStr 9 x)
        go (Apply x y) = (10, "<app>")
        go (Times x y) = (8, toStr 7 x ++ " * " ++ toStr 8 y)
        go (Divide x y) = (8, toStr 7 x ++ " / " ++ toStr 8 y)
        go (Mod x y) = (8, toStr 7 x ++ " % " ++ toStr 8 y)
        go (Plus x y) = (7, toStr 6 x ++ " + " ++ toStr 7 y)
        go (Minus x y) = (7, toStr 6 x ++ " - " ++ toStr 7 y)
        go (Cons x y) = (6, toStr 6 x ++ " :: " ++ toStr 5 y)
        go (Equal x y) = (5, toStr 5 x ++ " = " ++ toStr 5 y)
        go (Less x y) = (5, toStr 5 x ++ " < " ++ toStr 5 y)
        go (If x y z) = (4, "if " ++ toStr 4 x ++ " then " ++ toStr 4 y ++ " else " ++ toStr 4 z)
        go (Match e1 ty e2 x y e3) =
					(3, "match " ++ toStr 3 e1 ++ " with " ++
						 "[" ++ stringOfType ty ++ "] -> " ++ toStr 3 e2 ++ " | " ++
						 x ++ "::" ++ y ++ " -> " ++ toStr 3 e3)
        go (Fun x y z) = (10, "<fun>")
        go (Rec x y z) = (10, "<rec>")

removeAssoc : Eq a => a -> List (a, b) -> List (a, b)
removeAssoc _ [] = []
removeAssoc sought ((key, e) :: rest) =
  if key == sought
  then rest
  else (key, e)::removeAssoc sought rest

substr : List (Name, Expr) -> Expr -> Maybe Expr
substr xs (Var x) = lookup x xs
substr xs e@(EInt _) = Just e
substr xs e@(EBool _) = Just e
substr xs e@(ENil x) = Just e
substr xs (Times x y) = Times <$> substr xs x <*> substr xs y
substr xs (Divide x y) = Divide <$> substr xs x <*> substr xs y
substr xs (Mod x y) = Mod <$> substr xs x <*> substr xs y
substr xs (Plus x y) = Plus <$> substr xs x <*> substr xs y
substr xs (Minus x y) = Minus <$> substr xs x <*> substr xs y
substr xs (Equal x y) = Equal <$> substr xs x <*> substr xs y
substr xs (Cons x y) = Cons <$> substr xs x <*> substr xs y
substr xs (Less x y) = Less <$> substr xs x <*> substr xs y
substr xs (If x y z) = If <$> substr xs x <*> substr xs y <*> substr xs z
substr xs (Fun x y z) =
  let newXs = removeAssoc x xs in Fun x y <$> substr newXs z

substr xs (Apply x y) = Apply <$> substr xs x <*> substr xs y
substr xs (Pair x y) = Pair <$> substr xs x <*> substr xs y
substr xs (Fst x) = Fst <$> substr xs x
substr xs (Snd x) = Snd <$> substr xs x
substr xs (Rec x y z) =
  let newXs = removeAssoc x xs in Rec x y <$> substr newXs z
substr xs (Match x y z w s t) =
  let
    newXs = removeAssoc s (removeAssoc w xs)
  in
    Match <$> substr xs x <*> pure y <*> substr xs z <*> pure w <*> pure s <*> substr newXs t
