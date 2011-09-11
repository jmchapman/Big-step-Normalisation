{-# OPTIONS --no-termination-check #-}

module BasicSystem.RecursiveNormaliser where
open import BasicSystem.Syntax
open import BasicSystem.OPE

mutual
  eval : forall {Γ Δ σ} -> Tm Δ σ -> Env Γ Δ -> Val Γ σ
  eval top        (vs << v) = v
  eval (t [ ts ]) vs        = eval t (evalˢ ts vs)
  eval (λt t)     vs        = λv t vs
  eval (t $ u)    vs        = eval t vs $$ eval u vs

  _$$_ : forall {Γ σ τ} -> Val Γ (σ ⇒ τ) -> Val Γ σ -> Val Γ τ
  λv t vs $$ v = eval t (vs << v)
  nev n   $$ v = nev (appV n v)

  evalˢ : forall {Γ Δ Σ} -> Sub Δ Σ -> Env Γ Δ -> Env Γ Σ
  evalˢ (pop σ)   (vs << v) = vs
  evalˢ (ts < t)  vs        = evalˢ ts vs << eval t vs
  evalˢ id        vs        = vs
  evalˢ (ts ○ us) vs        = evalˢ ts (evalˢ us vs)

mutual
  quot : forall {Γ σ} -> Val Γ σ -> Nf Γ σ
  quot {σ = σ ⇒ τ} f       = λn (quot (vwk σ f $$ nev (varV vZ)))
  quot {σ = ι}     (nev n) = ne (quotⁿ n)

  quotⁿ : forall {Γ σ} -> NeV Γ σ -> NeN Γ σ
  quotⁿ (varV x)   = varN x
  quotⁿ (appV n v) = appN (quotⁿ n) (quot v)

open import BasicSystem.IdentityEnvironment

nf : forall {Γ σ} -> Tm Γ σ -> Nf Γ σ
nf t = quot (eval t vid)
