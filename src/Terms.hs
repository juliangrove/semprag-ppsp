{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Terms where


--------------------------------------------------------------------------------
-- | λ-calculus types and terms

-- | Atomic types for entities, truth values, and indices. Arrows, products,
-- and maybe types.
data Type = E | T | I
          | Type :-> Type
          | Unit
          | Type :× Type
          | Maybe Type

type α × β = α ':× β
type α ⟶ β = α ':-> β
infixr ⟶
infixr :->

-- | Variables
data (α :: Type) ∈ (γ :: Type) where
  Get :: α ∈ (γ × α)
  Weaken :: α ∈ γ -> α ∈ (γ × β)
deriving instance Show (α ∈ γ)
deriving instance Eq (α ∈ γ)

-- | Constants
data Con α where
  -- Logical constants
  Tru :: Con 'T
  Fal :: Con 'T
  And :: Con ('T ⟶ 'T ⟶ 'T)
  Or :: Con ('T ⟶ 'T ⟶ 'T)
  Imp :: Con ('T ⟶ 'T ⟶ 'T)
  ImpM :: Con ('Maybe 'T ⟶ 'Maybe 'T ⟶ 'Maybe 'T)
  Forall :: Con ((α ⟶ 'T) ⟶ 'T)
  ForallM :: Con ((α ⟶ 'Maybe 'T) ⟶ 'Maybe 'T)
  Exists :: Con ((α ⟶ 'T) ⟶ 'T)
  ExistsM :: Con ((α ⟶ 'Maybe 'T) ⟶ 'Maybe 'T)
  Iota :: Con (('E ⟶ 'T) ⟶ 'Maybe 'E)
  Equals :: Con (α ⟶ α ⟶ 'T)
  -- Non-logical constants
  Theo :: Con 'E
  Bro :: Con ('E ⟶ 'I ⟶ 'T)
  Suit :: Con ('E ⟶ 'I ⟶ 'T)
  Bring :: Con ('E ⟶ 'E ⟶ 'I ⟶ 'T)
  Have :: Con ('E ⟶ 'E ⟶ 'I ⟶ 'T)
  Map :: Con ((α ⟶ β) ⟶ 'Maybe α ⟶ 'Maybe β)

-- | Well-typed terms.
data γ ⊢ α where
  Var :: α ∈ γ -> γ ⊢ α
  Con :: Con α -> γ ⊢ α
  App :: γ ⊢ (α ⟶ β) -> γ ⊢ α -> γ ⊢ β
  Lam :: (γ × α) ⊢ β -> γ ⊢ (α ⟶ β)
  Fst :: γ ⊢ (α × β) -> γ ⊢ α
  Snd :: γ ⊢ (α × β) -> γ ⊢ β
  TT :: γ ⊢ 'Unit
  Pair :: γ ⊢ α -> γ ⊢ β -> γ ⊢ (α × β)
  Defined :: γ ⊢ α -> γ ⊢ 'Maybe α
  Undefined :: γ ⊢ 'Maybe α
  Match :: γ ⊢ ('Maybe α) -> (γ × α) ⊢ β -> γ ⊢ β -> γ ⊢ β

infixl `App`
(@@) :: γ ⊢ (α ⟶ β) -> γ ⊢ α -> γ ⊢ β
(@@) = App

infixl `Pair`
(&) :: γ ⊢ α -> γ ⊢ β -> γ ⊢ (α × β)
(&) = Pair

-- | Neutral terms (no constructors, except in arguments).
data Neutral γ α where
  NeuVar :: α ∈ γ -> Neutral γ α
  NeuCon :: Con α -> Neutral γ α
  NeuApp :: Neutral γ (α ⟶ β) -> NF γ α -> Neutral γ β
  NeuFst :: Neutral γ (α × β) -> Neutral γ α
  NeuSnd :: Neutral γ (α × β) -> Neutral γ β
  NeuTT :: Neutral γ 'Unit
  NeuMatch :: Neutral γ ('Maybe α)
           -> NF (γ × α) β -> NF γ β -> Neutral γ β
  
  
-- | Terms in normal form.
data NF γ α where
  NFLam :: NF (γ × α) β -> NF γ (α ⟶ β)
  NFPair :: NF γ α -> NF γ β -> NF γ (α × β)
  NFDefined :: NF γ α -> NF γ ('Maybe α)
  NFUndefined :: NF γ ('Maybe α)
  Neu :: Neutral γ α -> NF γ α

instance Show (Con α) where
  show Tru = "⊤"
  show Fal = "⊥"
  show And = "(∧)"
  show Or = "(∨)"
  show Imp = "(→)"
  show ImpM = "(⇒)"
  show Forall = "∀"
  show ForallM = "∀#"
  show Exists = "∃"
  show ExistsM = "∃#"
  show Iota = "ι"
  show Equals = "(=)"
  show Suit = "suit"
  show Bro = "bro"
  show Bring = "bring"
  show Have = "have"
  show Theo = "t"
  show Map = "map"

lft :: (α ∈ γ -> α ∈ δ) -> α ∈ (γ × β) -> α ∈ (δ × β)
lft f = \case
  Get -> Get
  Weaken i -> Weaken $ f i

rename :: (forall α. α ∈ γ -> α ∈ δ) -> γ ⊢ β -> δ ⊢ β
rename f = \case
  Var i -> Var $ f i
  Con c -> Con c
  App (rename f -> m) (rename f -> n) -> App m n
  Lam (rename (lft f) -> m) -> Lam m
  Fst (rename f -> m) -> Fst m
  Snd (rename f -> m) -> Snd m
  TT -> TT
  Pair (rename f -> m) (rename f -> n) -> Pair m n
  Defined (rename f -> m) -> Defined m
  Undefined -> Undefined
  Match (rename f -> m) (rename (lft f) -> n) (rename f -> o) -> Match m n o

wkn :: γ ⊢ α -> (γ × β) ⊢ α
wkn = rename Weaken

exch :: ((γ × α) × β) ⊢ ω -> ((γ × β) × α) ⊢ ω
exch = rename $ \case
  Get -> Weaken Get
  Weaken Get -> Get
  Weaken (Weaken i) -> Weaken (Weaken i)

contr :: (γ × α × α) ⊢ β -> (γ × α) ⊢ β
contr = rename $ \case
  Get -> Get
  Weaken i -> i

renameNeu :: (forall α. α ∈ γ -> α ∈ δ) -> Neutral γ α -> Neutral δ α
renameNeu f = \case
  NeuVar i -> NeuVar $ f i
  NeuCon c -> NeuCon c
  NeuApp (renameNeu f -> m) (renameNF f -> n) -> NeuApp m n
  NeuFst (renameNeu f -> m) -> NeuFst m
  NeuSnd (renameNeu f -> m) -> NeuSnd m
  NeuTT -> NeuTT
  NeuMatch
    (renameNeu f -> m)
    (renameNF (lft f) -> n)
    (renameNF f -> o) -> NeuMatch m n o

renameNF :: (forall α. α ∈ γ -> α ∈ δ) -> NF γ α -> NF δ α
renameNF f = \case
  NFLam (renameNF (lft f) -> m) -> NFLam m
  NFPair (renameNF f -> m) (renameNF f -> n) -> NFPair m n
  NFDefined (renameNF f -> m) -> NFDefined m
  NFUndefined -> NFUndefined
  Neu t -> Neu $ renameNeu f t

wknNF :: NF γ α -> NF (γ × β) α
wknNF = renameNF Weaken

exchNF :: NF ((γ × α) × β) ω -> NF ((γ × β) × α) ω
exchNF = renameNF $ \case
  Get -> Weaken Get
  Weaken Get -> Get
  Weaken (Weaken i) -> Weaken $ Weaken i

app' :: NF γ (α ⟶ β) -> NF γ α -> NF γ β
app' t u = case t of
             NFLam m' -> substNF0 m' u -- β rule
             Neu m' -> deflt
               where deflt = Neu (NeuApp m' u)

fst' :: NF γ (α × β) -> NF γ α
fst' = \case
  NFPair m _ -> m
  Neu m -> Neu $ NeuFst m

snd' :: NF γ (α × β) -> NF γ β
snd' = \case
  NFPair _ n -> n
  Neu m -> Neu $ NeuSnd m

match' :: NF γ ('Maybe α) -> NF (γ × α) β -> NF γ β -> NF γ β
match' = \case
  NFDefined m -> \n _ -> substNF0 n m
  NFUndefined -> \_ o -> o
  Neu m -> \n o -> Neu $ NeuMatch m n o

substNeu :: forall γ δ α.Neutral γ α -> (forall β.β ∈ γ -> NF δ β) -> NF δ α
substNeu (NeuVar i) f = f i
substNeu (NeuCon c) _ = Neu $ NeuCon c
substNeu (NeuApp m n) f = app' (substNeu m f) (substNF n f)
substNeu (NeuFst m) f = fst' (substNeu m f)
substNeu (NeuSnd m) f = snd' (substNeu m f)
substNeu NeuTT _ = Neu NeuTT
substNeu (NeuMatch m n o) f = match' (substNeu m f) (substNF n f') (substNF o f)
  where f' :: forall β α0.β ∈ (γ × α0) -> NF (δ × α0) β
        f' Get = Neu $ NeuVar Get
        f' (Weaken i) = wknNF $ f i
                 
substNF :: NF γ α -> (forall β.β ∈ γ -> NF δ β) -> NF δ α
substNF (NFLam m) f = NFLam $ substNF m $ \case
  Get -> Neu $ NeuVar Get
  Weaken i -> wknNF $ f i
substNF (NFPair m n) f = NFPair (substNF m f) (substNF n f)
substNF (NFDefined m) f = NFDefined (substNF m f)
substNF NFUndefined f = NFUndefined
substNF (Neu m) f = substNeu m f

substNF0 :: NF (γ × α) β -> NF γ α -> NF γ β
substNF0 m t = substNF m $ \case
  Get -> t
  Weaken i -> Neu $ NeuVar i

normalForm :: γ ⊢ α -> NF γ α
normalForm = \case
  Var i -> Neu $ NeuVar i
  Con c -> Neu $ NeuCon c
  Lam (normalForm -> m) -> NFLam m
  App (normalForm -> m) (normalForm -> n) -> app' m n
  Pair (normalForm -> m) (normalForm -> n) -> NFPair m n
  TT -> Neu NeuTT
  Fst (normalForm -> m) -> fst' m
  Snd (normalForm -> m) -> snd' m
  Defined (normalForm -> m) -> NFDefined m
  Undefined -> NFUndefined
  Match (normalForm -> m) (normalForm -> n) (normalForm -> o) -> match' m n o

nfToλ :: NF γ α -> γ ⊢ α
nfToλ = \case
  Neu (neuToλ -> m) -> m
  NFLam (nfToλ -> m) -> Lam m
  NFPair (nfToλ -> m) (nfToλ -> n) -> Pair m n
  NFDefined (nfToλ -> m) -> Defined m
  NFUndefined -> Undefined

neuToλ :: Neutral γ α -> γ ⊢ α
neuToλ = \case
  NeuVar i -> Var i
  NeuCon c -> Con c
  NeuApp (neuToλ -> m) (nfToλ -> n) -> App m n
  NeuFst (neuToλ -> m) -> Fst m
  NeuSnd (neuToλ -> m) -> Snd m
  NeuTT -> TT
  NeuMatch (neuToλ -> m) (nfToλ -> n) (nfToλ -> o) -> Match m n o

betaReduce :: γ ⊢ α -> γ ⊢ α
betaReduce = nfToλ . normalForm

printTerm :: forall γ α.
             [String] -> (forall x. x ∈ γ -> String) -> γ ⊢ α -> String
printTerm fs ρ t =
 let dd :: forall β. γ ⊢ β -> String
     dd = printTerm fs ρ
 in case t of
  Var v -> ρ v
  App (App (Con And) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " ∧ " ++ q ++ ")"
  App (App (Con Or) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " ∨ " ++ q ++ ")"
  App (App (Con Imp) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " → " ++ q ++ ")"
  App (App (Con ImpM) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " ⇒ " ++ q ++ ")"
  App (App (Con Equals) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " = " ++ n ++ ")"
  App (Con Forall) (Lam t') -> case fs of
    fresh:rest -> "(∀" ++ fresh ++ " : " ++ printTerm rest (\case
                                                               Get -> fresh
                                                               Weaken x -> ρ x)
                  t' ++ ")"
  App (Con ForallM) (Lam t') -> case fs of
    fresh:rest -> "(∀#" ++ fresh ++ " : " ++ printTerm rest (\case
                                                                Get -> fresh
                                                                Weaken x -> ρ x)
                  t' ++ ")"
  App (Con Exists) (Lam t') -> case fs of
    fresh:rest -> "(∃" ++ fresh ++ " : " ++ printTerm rest (\case
                                                               Get -> fresh
                                                               Weaken x -> ρ x)
                  t' ++ ")"
  App (Con ExistsM) (Lam t') -> case fs of
    fresh:rest -> "(∃#" ++ fresh ++ " : " ++ printTerm rest (\case
                                                                Get -> fresh
                                                                Weaken x -> ρ x)
                  t' ++ ")"
  App (Con Iota) (Lam t') -> case fs of
    fresh:rest -> "(ι" ++ fresh ++ " : " ++ printTerm rest (\case
                                                               Get -> fresh
                                                               Weaken x -> ρ x)
                  t' ++ ")"
  App (Con Iota) t' -> case fs of
    fresh:rest -> "(ι" ++ fresh ++ " : " ++ printTerm rest ρ t' ++
                  "(" ++ fresh ++ "))"
  App (dd -> m) n@(dd -> n') -> m ++ case n of
                                       Lam _ -> n'
                                       Fst _ -> n'
                                       Snd _ -> n'
                                       _ -> "(" ++ n' ++ ")"
  Con (show -> c) -> c
  Lam t' -> case fs of
    fresh:rest -> "(λ" ++ fresh ++ "." ++ printTerm rest (\case
                                                             Get -> fresh
                                                             Weaken x -> ρ x)
                  t' ++ ")"
    _ -> error "printTerm: ran out of fresh variables."
  Fst (dd -> m) -> "(π₁ " ++ m ++ ")"
  Snd (dd -> m) -> "(π₂ " ++ m ++ ")"
  TT -> "⋄"
  Pair (dd -> m) (dd -> n) -> "⟨" ++ m ++ ", " ++ n ++ "⟩"
  Defined (dd -> m) -> "[" ++ m ++ "]"
  Undefined -> "#"
  Match (dd -> m) n (dd -> o) -> case fs of
    fresh:rest -> "(match " ++ m ++ " with " ++ "[" ++ fresh ++ "] => " ++
                  printTerm rest (\case
                                     Get -> fresh
                                     Weaken x -> ρ x)
                  n ++ "; # => " ++ o ++ ")"
  

instance Show (γ ⊢ α) where
  show t = printTerm freshes (\case) t
    where freshes :: [String]
          freshes = "" : map show ints >>= \i ->
            map (:i) ['x', 'y', 'z', 'u', 'v', 'w']
          ints = 1 : map succ ints

instance Show (NF γ α) where
  show = show . nfToλ
