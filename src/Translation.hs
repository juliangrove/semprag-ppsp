{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Translation where

import Examples as Ex
import Grammar as Gr
import Prelude hiding (Word)
import Terms as Te


--------------------------------------------------------------------------------
-- | Translations of examples into λ-calculus

-- | entities
theo, mary, john, mary's_parents :: γ ⊢ 'E
theo = Con Te.Theo
mary = Con Te.Mary
john = Con Te.John
mary's_parents = Con Te.MaryPnts

-- | individual concepts
his_wetsuit :: γ ⊢ ('I ⟶ 'Maybe 'E)
his_wetsuit = Lam (Con Iota @@ (Lam (Con Suit @@ Var Get @@ Var (Weaken Get))))

-- | 1-place preds
bro, suit, in_bed :: γ ⊢ ('E ⟶ 'I ⟶ 'Te.T)
bro = Con Bro
suit = Con Suit
in_bed = Con InBed

-- | 2-place preds
bring, have, lost :: γ ⊢ ('E ⟶ 'E ⟶ 'I ⟶ 'Te.T)
bring = Con Bring
have = Con Have
lost = Con Lose

-- | adverbs
also :: γ ⊢ (('E ⟶ 'I ⟶ 'Te.T) ⟶ 'E ⟶ 'I ⟶ 'Maybe ('I ⟶ 'Te.T))
also = Lam (Lam (Lam (Match (Con Delta @@ (Var (Weaken (Weaken Get)) @@
                                           Con Te.John @@
                                           Var Get))
                      (Defined (Var (Weaken (Weaken (Weaken Get))) @@
                                Var (Weaken (Weaken Get))))
                      Undefined)))

-- >>> also
-- (λx.(λy.(λz.(match δ(x(j)(z)) with [u] => [x(y)]; # => #))))


-- | connectives
if' :: γ ⊢ (('I ⟶ 'Maybe ('I ⟶ 'Te.T)) ⟶
            ('I ⟶ 'Maybe ('I ⟶ 'Te.T)) ⟶
             'I ⟶ 'Maybe 'Te.T)
if' = Lam (Lam (Lam (Con ImpM @@ (eval1 (Var (Weaken (Weaken Get))) @@ Var Get)
                     @@ (eval1 (Var (Weaken Get)) @@ Var Get))))
      
-- | monadic stuff

bind0 :: γ ⊢ 'Maybe α -> γ ⊢ (α ⟶ 'Maybe β) -> γ ⊢ 'Maybe β
bind0 m k = Match m (wkn k @@ Var Get) Undefined

pure0 :: γ ⊢ α -> γ ⊢ 'Maybe α
pure0 = Defined

bind1 :: γ ⊢ ('I ⟶ 'Maybe α) -> γ ⊢ (α ⟶ 'I ⟶ 'Maybe β) -> γ ⊢ ('I ⟶ 'Maybe β)
bind1 m k = Lam (wkn m @@ Var Get `bind0`
                 Lam (wkn (wkn k) @@ (Var Get) @@ Var (Weaken Get)))

pure1 :: γ ⊢ α -> γ ⊢ ('I ⟶ 'Maybe α)
pure1 v = Lam (pure0 (wkn v))

eval1 :: γ ⊢ ('I ⟶ 'Maybe ('I ⟶ 'Te.T)) -> γ ⊢ ('I ⟶ 'Maybe 'Te.T)
eval1 m = Lam (Match (wkn m @@ Var Get)
               (Defined (Var Get @@ Var (Weaken Get)))
               Undefined)

-- | interpretation

type family Semtype (c :: Cat) where
  Semtype 'N = 'E ⟶ 'I ⟶ 'Te.T
  Semtype 'V = 'E ⟶ 'I ⟶ 'Te.T
  Semtype 'D = 'E
  Semtype 'Gr.T = 'I ⟶ 'Te.T
  Semtype 'C = 'I ⟶ 'Te.T
  Semtype (a \\ b) = Semtype a ⟶ Semtype b
  Semtype (a // b) = Semtype b ⟶ Semtype a
  Semtype ('Effectful a) = 'I ⟶ 'Maybe (Semtype a)
  Semtype ('Evaluated 'Gr.T) = 'I ⟶ 'Maybe ('Te.T)
  Semtype ('Bound a b) = Semtype a ⟶ Semtype b

interpWord :: Word c -> γ ⊢ (Semtype c)
interpWord = \case
  Has_a_brother -> bro
  Brings -> bring
  Lost -> lost
  In_bed -> in_bed
  Ex.Theo -> theo
  Ex.Mary -> mary
  Ex.John -> john
  Ex.Mary's_parents -> mary's_parents
  His_wetsuit ->
    Lam (Con Iota @@
          (Lam (Con And @@
                 (Con Suit @@ Var Get @@ Var (Weaken Get)) @@
                 (Con Have @@ Var Get @@ Con Te.Theo @@ Var (Weaken Get)))))
  If -> if'
  Believes ->
    Lam (Lam (Lam
              (Con ForallM @@
               (Lam (Con ImpM @@
                     Defined (Con Dox @@
                              Var (Weaken (Weaken Get)) @@
                              Var (Weaken  Get) @@
                              Var Get) @@
                     (Var (Weaken (Weaken (Weaken Get))) @@ Var Get))))))
  Also -> also
  w -> error $ "can't interpret " ++ show w

interpExpr :: forall γ c.
              (forall (c' :: Cat).(CatWitness c', Int) -> γ ⊢ Semtype c')
           -> Expr c -> γ ⊢ Semtype c
interpExpr g = \case
  Lex (interpWord -> w) -> w
  AppL (ieg -> m) (ieg -> n) -> n @@ m
  AppR (ieg -> m) (ieg -> n) -> m @@ n
  Trace c i -> g (c, i)
  Bind i (c'' :: CatWitness c'') e ->
    let g' :: (CatWitness c', Int) -> γ × (Semtype c'') ⊢ Semtype c'
        g' (c', i') = case eqCats c' c'' of
                        Just Refl -> if i' == i
                                     then Var Get
                                     else wkn (g (c', i'))
                        Nothing -> wkn (g (c', i'))
    in Lam (interpExpr g' e)
  Scope1 (ieg -> m) (ieg -> k) -> m `bind1` k
  Scope2 (ieg -> m) (ieg -> k) -> m `bind1` k
  Lift (ieg -> v) -> pure1 v
  Eval (ieg -> m) -> eval1 m
  where ieg :: Expr c' -> γ ⊢ Semtype c'
        ieg = interpExpr g
          
-- >>> :set -XLambdaCase -XEmptyCase
-- >>> betaReduce $ interpExpr (\case) also_wide
-- (λx.(match (match δ(inBed(j)(x)) with [y] => [inBed(m)]; # => #) with [y] => (∀#z : ([dox(pnts(m))(x)(z)] ⇒ [y(z)])); # => #))
