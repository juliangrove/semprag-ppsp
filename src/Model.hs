{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

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
bro x = False
suit = \case
  Ent 5 -> True
  _ -> False

-- | 2-place preds
bring, have :: Entity -> Entity -> Bool
bring x y = False
have x y = False

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
  Semtype (Bound a b) = Semtype a -> Semtype b

interp_word :: Word c -> Semtype c
interp_word = \case
  Has_a_brother -> bro
  Brings -> bring
  Theo -> theo
  His_wetsuit -> iota (\x -> suit x && have x theo)
  If -> if'

interp_expr :: Expr c
       -> (forall (c' :: Cat).(CatWitness c', Int) -> Semtype c')
       -> Semtype c
interp_expr (Lex w) g = interp_word w
interp_expr (AppL m n) g = interp_expr n g $ interp_expr m g
interp_expr (AppR m n) g = interp_expr m g $ interp_expr n g
interp_expr (Trace c i) g = g (c, i)
interp_expr (Bind i c e) g = \x -> interp_expr e $ \case
  (c', i') -> case eqCats c c' of
                Just Refl -> x
                Nothing -> g (c', i')
interp_expr (Scope m k) g = interp_expr m g >>= interp_expr k g
interp_expr (Lift m) g = return $ interp_expr m g

-- >>> :set -XLambdaCase -XEmptyCase
-- >>> interp_expr if_brother_wetsuit1 (\case)
-- Just True
