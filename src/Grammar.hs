{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Grammar where

import Prelude hiding (Word)

data Cat = N | V | D | T | C
         | Cat :\: Cat
         | Cat :/: Cat
         | Effectful Cat
         | Bound Cat Cat
  deriving (Eq, Show)

type a \\ b = a ':\: b
type a // b = a ':/: b

data CatWitness (c :: Cat) where
  NW :: CatWitness 'N
  VW :: CatWitness 'V
  DW :: CatWitness 'D
  TW :: CatWitness 'T
  CW :: CatWitness 'C
  (::\::) :: CatWitness a -> CatWitness b -> CatWitness (a \\ b)
  (::/::) :: CatWitness a -> CatWitness b -> CatWitness (a // b)
  EffectfulW :: CatWitness a -> CatWitness (Effectful a)
  BoundW :: CatWitness a -> CatWitness b -> CatWitness (Bound a b)


data EqCats (c :: Cat) (c' :: Cat) where
  Refl :: EqCats c c

eqCats :: CatWitness c -> CatWitness c' -> Maybe (EqCats c c')
eqCats NW NW = Just Refl
eqCats VW VW = Just Refl
eqCats DW DW = Just Refl
eqCats TW TW = Just Refl
eqCats CW CW = Just Refl
eqCats (a ::\:: b) (c ::\:: d) = case eqCats a c of
                                   Just Refl -> case eqCats b d of
                                                  Just Refl -> Just Refl
                                                  _ -> Nothing
                                   _ -> Nothing
eqCats (a ::/:: b) (c ::/:: d) = case eqCats a c of
                                   Just Refl -> case eqCats b d of
                                                  Just Refl -> Just Refl
                                                  _ -> Nothing
                                   _ -> Nothing
eqCats (EffectfulW c) (EffectfulW c') = case eqCats c c' of
                                          Just Refl -> Just Refl
                                          _ -> Nothing
eqCats (BoundW a b) (BoundW c d) = case eqCats a c of
                                     Just Refl -> case eqCats b d of
                                                    Just Refl -> Just Refl
                                                    _ -> Nothing
                                     _ -> Nothing
eqCats _ _ = Nothing

a \\ b = a ::\:: b
a // b = a ::/:: b

data Word (c :: Cat) = Word (CatWitness c) String
data Expr (c :: Cat) where
  Lex :: Word c -> Expr c
  AppL :: Expr a -> Expr (a \\ b) -> Expr b
  AppR :: Expr (a // b) -> Expr b -> Expr a
  Trace :: CatWitness c -> Int -> Expr c
  Bind :: Int -> CatWitness c' -> Expr c -> Expr (Bound c' c)
  Scope :: Expr (Effectful c')
        -> Expr (Bound c' (Effectful c))
        -> Expr (Effectful c)
  Lift :: Expr c -> Expr (Effectful c)
