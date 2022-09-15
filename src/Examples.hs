{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

module Examples where

import Grammar
import Prelude hiding (Word)


--------------------------------------------------------------------------------
-- | Lexicon and examples from paper

-- | example lexicon
pattern Has_a_brother = Word (DW ::\:: TW) "has a brother"
pattern Brings = Word ((DW ::\:: TW) ::/:: DW) "will bring"
pattern Lost = Word ((DW ::\:: TW) ::/:: DW) "lost"
pattern Theo = Word DW "Theo"
pattern John = Word DW "John"
pattern Mary = Word DW "Mary"
pattern Mary's_parents = Word DW "Mary's parents"
pattern His_wetsuit = Word (EffectfulW DW) "his wetsuit"
pattern If = Word ((EvaluatedW TW ::/:: EffectfulW TW) ::/:: EffectfulW TW) "if"
pattern Believes = Word ((DW ::\:: EvaluatedW TW) ::/:: EvaluatedW TW) "believes"
pattern Also = Word ((DW ::\:: EffectfulW TW) ::/:: (DW ::\:: TW)) "also"
pattern In_bed = Word (DW ::\:: TW) "is in bed"

-- | example derivations

figure5 :: Expr ('Evaluated 'T)
figure5 =
  Lex If `AppR` Lift (Lex Theo `AppL` Lex Has_a_brother) `AppR` -- if Theo has a brother
  (Lex His_wetsuit                                              -- he'll bring his wetsuit
  `Scope1` Bind 1 DW (Lift (Lex Theo `AppL` (Lex Brings `AppR` (Trace DW 1)))))

figure6 :: Expr ('Evaluated 'T)
figure6 =
  (Lex His_wetsuit -- he'll bring his wetsuit
  `Scope1` Bind 1 DW
  (Lift (Lift (Lex Theo `AppL` (Lex Brings `AppR` (Trace DW 1))))))
  `Scope2` Bind 2 (EffectfulW TW)
  (Lex If `AppR` Lift (Lex Theo `AppL` Lex Has_a_brother) `AppR` -- if Theo has a brother
   Trace (EffectfulW TW) 2)                                      -- trace

reconstruction_example :: Expr ('Evaluated 'T)
reconstruction_example =
  (Lift (Lex His_wetsuit -- he'll bring his wetsuit
  `Scope1` Bind 1 DW
  (Lift (Lex Theo `AppL` (Lex Brings `AppR` (Trace DW 1))))))
  `Scope2` Bind 2 (EffectfulW TW)
  (Lex If `AppR` Lift (Lex Theo `AppL` Lex Has_a_brother) `AppR` -- if Theo has a brother
   Trace (EffectfulW TW) 2)                                      -- trace

figure9 :: Expr ('Evaluated 'T)
figure9 =
  Lex Theo `AppL` (Lex Believes `AppR` Eval -- Theo believes
                   (Lex His_wetsuit -- he lost his wetsuit
                    `Scope1` Bind 1 DW
                    (Lift (Lex Theo `AppL` (Lex Lost `AppR` (Trace DW 1))))))

figure10 :: Expr ('Evaluated 'T)
figure10 =
  (Lex His_wetsuit -- he lost his wetsuit
  `Scope1` Bind 1 DW
  (Lift (Lex Theo `AppL` (Lex Lost `AppR` (Trace DW 1)))))
  `Scope2` Bind 2 TW
  (Lex Theo `AppL` (Lex Believes `AppR` Eval (Lift (Trace TW 2)))) -- Theo believes trace

also_narrow :: Expr ('Evaluated 'T)
also_narrow =
  Lex Mary's_parents `AppL` -- Mary's parents believe
  (Lex Believes `AppR` (Eval (Lex Mary `AppL` (Lex Also `AppR` Lex In_bed)))) -- Mary also is in bed

also_wide :: Expr ('Evaluated 'T)
also_wide =
  Lex Mary `AppL` (Lex Also `AppR` Lex In_bed) -- Mary also is in bed
  `Scope2` Bind 1 TW
  (Lex Mary's_parents `AppL` (Lex Believes `AppR` (Eval (Lift (Trace TW 1))))) -- Mary's parents believe trace

-- >>> also_narrow
-- [ Mary's parents [ believes [↓ [ Mary [ also is in bed ] ] ] ] ]
