module Experiment where

-- Types: one base type and arrow
data Ty : Set where
  ι   : Ty
  _→_ : Ty -> Ty -> Ty

-- Contexts: left-to-right sequences of types
data Con : Set where
  ε   : Con
  _<_ : Con -> Ty -> Con

-- Concatenation of contexts
_+_ : Con -> Con -> Con
Γ + ε       = Γ
Γ + (Δ < σ) = (Γ + Δ) < σ

-- Well-typed de Bruijn indices
data Var : Con -> Ty -> Set where
  vZ : forall {Γ σ}   -> Var (Γ < σ) σ
  vS : forall {Γ σ τ} -> Var Γ σ -> Var (Γ < τ) σ

-- Well-typed lambda terms: (de B) variable, lambda or application
data Tm : Con -> Ty -> Set where
  var  : forall {Γ σ}   -> Var Γ σ      -> Tm Γ σ
  λ    : forall {Γ σ τ} -> Tm (Γ < σ) τ -> Tm Γ (σ → τ)
  _$_  : forall {Γ σ τ} -> Tm Γ (σ → τ) -> Tm Γ σ -> Tm Γ τ

-- Well-typed substitutions: left-to-right sequences of terms
data Sub : Con -> Con -> Set where
  ε   : forall {Γ}     -> Sub Γ ε
  _<_ : forall {Γ Δ σ} -> Sub Γ Δ -> Tm Γ σ -> Sub Γ (Δ < σ)

-- project from a substitution
lookup : forall {Γ Δ σ} -> Var Δ σ -> Sub Γ Δ -> Tm Γ σ
lookup vZ     (ts < t) = t 
lookup (vS x) (ts < t) = lookup x ts  

-- thinning (introduce a fresh variable somewhere in the context)
thinVar : forall {Γ σ} Δ τ -> Var (Γ + Δ) σ -> Var ((Γ < τ) + Δ) σ
thinVar ε       τ x      = vS x
thinVar (Δ < σ) τ vZ     = vZ
thinVar (Δ < σ) τ (vS x) = vS (thinVar Δ τ x) 

thinTm : forall {Γ σ} Δ τ -> Tm (Γ + Δ) σ -> Tm ((Γ < τ) + Δ) σ
thinTm Δ τ (var x) = var (thinVar Δ τ x)
thinTm Δ τ (λ t)   = λ (thinTm (Δ < _) τ t)
thinTm Δ τ (t $ u) = thinTm Δ τ t $ thinTm Δ τ u

thinSub : forall {Γ Σ} Δ τ -> Sub (Γ + Δ) Σ -> Sub ((Γ < τ) + Δ) Σ
thinSub Δ τ ε        = ε
thinSub Δ τ (ts < t) = thinSub Δ τ ts < thinTm Δ τ t

-- weakening substitution
weakSub : forall {Γ Δ τ} -> Sub Γ Δ -> Sub (Γ < τ) (Δ < τ)
weakSub ts = thinSub ε _ ts < var vZ

-- Substitution
_[_] : forall {Γ Δ σ} -> Tm Δ σ -> Sub Γ Δ -> Tm Γ σ
var x   [ ts ] = lookup x ts 
λ t     [ ts ] = λ (t [ weakSub ts ]) 
(t $ u) [ ts ] = t [ ts ] $ u [ ts ]