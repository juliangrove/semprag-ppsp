{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

module Examples where

import Grammar
import Prelude hiding (Word)

-- | example lexicon

pattern Has_a_brother = Word (DW ::\:: TW) "has a brother"
pattern Brings = Word ((DW ::\:: TW) ::/:: DW) "will bring"
pattern Theo = Word DW "theo"
pattern His_wetsuit = Word (EffectfulW DW) "his wetsuit"
pattern If = Word ((EffectfulW TW ::/:: EffectfulW TW) ::/:: EffectfulW TW) "if"

-- | example derivations

theo_bring_wetsuit1 :: Expr ('Effectful 'T)
theo_bring_wetsuit1 =
  Lex His_wetsuit
  `Scope` Bind 1 DW (Lift (Lex Theo `AppL` (Lex Brings `AppR` (Trace DW 1))))

theo_bring_wetsuit2 :: Expr ('Effectful ('Effectful 'T))
theo_bring_wetsuit2 =
  Lex His_wetsuit
  `Scope` Bind 1 DW (Lift (Lift (Lex Theo `AppL` (Lex Brings `AppR` (Trace DW 1)))))

theo_has_brother :: Expr 'T
theo_has_brother = Lex Theo `AppL` Lex Has_a_brother

if_brother_wetsuit1 :: Expr ('Effectful 'T)
if_brother_wetsuit1 = Lex If `AppR` Lift theo_has_brother `AppR` theo_bring_wetsuit1
