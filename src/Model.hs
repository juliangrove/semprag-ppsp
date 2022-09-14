{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Model where

import Examples
import Grammar
import Prelude hiding (Word)

data Entity = Ent Int deriving (Eq, Show)
instance Enum Entity where
  toEnum n = Ent n
  fromEnum (Ent n) = n

entities :: [Entity]
entities = [Ent 1..Ent 40]

iota :: (Entity -> Bool) -> Maybe Entity
iota pred = case filter pred entities of
              [x] -> Just x
              _ -> Nothing

-- | entities
theo :: Entity
theo = Ent 1

-- | 1-place preds
bro, suit :: Entity -> Bool
bro _ = False
suit = \case
  Ent 5 -> True
  _ -> False

-- | 2-place preds
bring, have :: Entity -> Entity -> Bool
bring _ _ = False
have _ _ = False

-- | connectives
if' :: Maybe Bool -> Maybe Bool -> Maybe Bool
if' (Just True) q = q
if' (Just False) _ = Just True
if' Nothing _ = Nothing

-- | interpretation

type family Semtype (c :: Cat) where
  Semtype 'N = Entity -> Bool
  Semtype 'V = Entity -> Bool
  Semtype 'D = Entity
  Semtype 'T = Bool
  Semtype 'C = Bool
  Semtype (a \\ b) = Semtype a -> Semtype b
  Semtype (a // b) = Semtype b -> Semtype a
  Semtype (Effectful a) = Maybe (Semtype a)
  Semtype (Evaluated a) = Maybe (Semtype a)
  Semtype (Bound a b) = Semtype a -> Semtype b

interpWord :: Word c -> Semtype c
interpWord = \case
  Has_a_brother -> bro
  Brings -> bring
  Theo -> theo
  His_wetsuit -> iota (\x -> suit x && have x theo)
  If -> if'

interpExpr :: (forall (c' :: Cat).(CatWitness c', Int) -> Semtype c')
           -> Expr c -> Semtype c
interpExpr g = \case
  Lex (interpWord -> w) -> w
  AppL (iwg -> m) (iwg -> n) -> n m
  AppR (iwg -> m) (iwg -> n) -> m n
  Trace c i -> g (c, i)
  Bind i c e -> \x ->
    let g' :: (CatWitness c', Int) -> Semtype c'
        g' (c', i') = case eqCats c c' of
                        Just Refl -> if i' == i
                                     then x
                                     else g (c', i')
                        Nothing -> g (c', i')
    in interpExpr g' e
  Scope1 (iwg -> m) (iwg -> k) -> m >>= k
  Scope2 (iwg -> m) (iwg -> k) -> m >>= k
  Lift (iwg -> v) -> pure v
  Eval (iwg -> m) -> m
  where iwg :: Expr c -> Semtype c
        iwg = interpExpr g
