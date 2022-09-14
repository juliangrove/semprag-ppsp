{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

module Examples where

import Grammar
import Prelude hiding (Word)

-- | example lexicon

pattern Has_a_brother = Word (DW ::\:: TW) "has a brother"
pattern Brings = Word ((DW ::\:: TW) ::/:: DW) "will bring"
pattern Theo = Word DW "theo"
pattern His_wetsuit = Word (EffectfulW DW) "his wetsuit"
pattern If = Word ((EvaluatedW TW ::/:: EvaluatedW TW) ::/:: EvaluatedW TW) "if"

-- | example derivations

theo_bring_wetsuit1 :: Expr ('Effectful 'T)
theo_bring_wetsuit1 = 
  Lex His_wetsuit
  `Scope1` Bind 1 DW (Lift (Lex Theo `AppL` (Lex Brings `AppR` (Trace DW 1))))

theo_bring_wetsuit2 :: Expr ('Effectful ('Effectful 'T))
theo_bring_wetsuit2 =
  Lex His_wetsuit
  `Scope1` Bind 1 DW
  (Lift (Lift (Lex Theo `AppL` (Lex Brings `AppR` (Trace DW 1)))))

theo_has_brother :: Expr 'T
theo_has_brother = Lex Theo `AppL` Lex Has_a_brother

if_brother_wetsuit1 :: Expr ('Evaluated 'T)
if_brother_wetsuit1 =
  Lex If `AppR` -- if
  Eval (Lift theo_has_brother) `AppR` -- Theo has a brother
  Eval theo_bring_wetsuit1            -- he'll bring his wetsuit

if_brother_wetsuit2 :: Expr ('Evaluated 'T)
if_brother_wetsuit2 =
  theo_bring_wetsuit2 -- he'll bring his wetsuit
  `Scope2` Bind 2 (EffectfulW TW)
  (Lex If `AppR` -- if
   Eval (Lift theo_has_brother) `AppR` -- Theo has a brother
   Eval (Trace (EffectfulW TW) 2))     -- trace

if_brother_wetsuit3 :: Expr ('Evaluated 'T)
if_brother_wetsuit3 =
  Lift theo_bring_wetsuit1 -- he'll bring his wetsuit
  `Scope2` Bind 2 (EffectfulW TW)
  (Lex If `AppR` -- if
   Eval (Lift theo_has_brother) `AppR` -- Theo has a brother
   Eval (Trace (EffectfulW TW) 2))     -- trace
