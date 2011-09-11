{-# OPTIONS --no-termination-check #-}

module FiniteProducts.RecursiveNormaliser where
open import FiniteProducts.Syntax
open import FiniteProducts.OPE

mutual
  eval : forall {Γ Δ σ} -> Tm Δ σ -> Env Γ Δ -> Val Γ σ
  eval top        (vs << v) = v
  eval (t [ ts ]) vs        = eval t (evalˢ ts vs)
  eval (λt t)     vs        = λv t vs
  eval (t $ u)    vs        = eval t vs $$ eval u vs
  eval void       vs        = voidv
  eval < t , u >  vs        = < eval t vs , eval u vs >v
  eval (fst t)    vs        = vfst (eval t vs) 
  eval (snd t)    vs        = vsnd (eval t vs) 

  vfst : forall {Γ σ τ} -> Val Γ (σ × τ) -> Val Γ σ
  vfst < v , w >v = v
  vfst (nev n)    = nev (fstV n)

  vsnd : forall {Γ σ τ} -> Val Γ (σ × τ) -> Val Γ τ
  vsnd < v , w >v = w
  vsnd (nev n)    = nev (sndV n)

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
  quot {σ = ι}     (nev n) = ne (quotⁿ n)
  quot {σ = σ ⇒ τ} f       = λn (quot (vwk σ f $$ nev (varV vZ)))
  quot {σ = One}   _   = voidn
  quot {σ = σ × τ} p   = < quot (vfst p) , quot (vsnd p) >n   

  -- shouldn't quot return voidn for anything of type One?
  -- but then what happens to neutral terms? Aren't there any?

  quotⁿ : forall {Γ σ} -> NeV Γ σ -> NeN Γ σ
  quotⁿ (varV x)   = varN x
  quotⁿ (appV n v) = appN (quotⁿ n) (quot v)
  quotⁿ (fstV n)   = fstN (quotⁿ n) 
  quotⁿ (sndV n)   = sndN (quotⁿ n) 

open import FiniteProducts.IdentityEnvironment

nf : forall {Γ σ} -> Tm Γ σ -> Nf Γ σ
nf t = quot (eval t vid)
