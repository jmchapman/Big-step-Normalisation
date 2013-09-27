{-# OPTIONS --no-termination-check #-}

module FullSystem.RecursiveNormaliser where
open import FullSystem.Syntax
open import FullSystem.OPE

mutual
  eval : forall {Γ Δ σ} -> Tm Δ σ -> Env Γ Δ -> Val Γ σ
  eval top          (vs << v) = v
  eval (t [ ts ])   vs        = eval t (evalˢ ts vs)
  eval (λt t)       vs        = λv t vs
  eval (t $ u)      vs        = eval t vs $$ eval u vs
  eval zero         vs        = zerov
  eval (suc t)      vs        = sucv (eval t vs)
  eval (prim z s n) vs        = vprim (eval z vs) (eval s vs) (eval n vs) 
  eval void       vs        = voidv
  eval < t , u >  vs        = < eval t vs , eval u vs >v
  eval (fst t)    vs        = vfst (eval t vs) 
  eval (snd t)    vs        = vsnd (eval t vs) 


  vprim : forall {Γ σ} -> Val Γ σ -> Val Γ (N ⇒ σ ⇒ σ) -> Val Γ N -> Val Γ σ
  vprim z f (nev n)  = nev (primV z f n) 
  vprim z f zerov    = z 
  vprim z f (sucv v) = (f $$ v) $$ (vprim z f v) 

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
  quot {σ = ι}     (nev n)   = neι (quotⁿ n)
  quot {σ = σ ⇒ τ} f         = λn (quot (vwk σ f $$ nev (varV vZ)))
  quot {σ = N}     zerov     = zeron 
  quot {σ = N}     (sucv v)  = sucn (quot v) 
  quot {σ = N}     (nev n)   = neN (quotⁿ n)
  quot {σ = One}   _   = voidn
  quot {σ = σ × τ} p   = < quot (vfst p) , quot (vsnd p) >n   

  quotⁿ : forall {Γ σ} -> NeV Γ σ -> NeN Γ σ
  quotⁿ (varV x)      = varN x
  quotⁿ (appV n v)    = appN (quotⁿ n) (quot v)
  quotⁿ (primV z s n) = primN (quot z) (quot s) (quotⁿ n)
  quotⁿ (fstV n)   = fstN (quotⁿ n) 
  quotⁿ (sndV n)   = sndN (quotⁿ n) 

open import FullSystem.IdentityEnvironment

nf : forall {Γ σ} -> Tm Γ σ -> Nf Γ σ
nf t = quot (eval t vid)
