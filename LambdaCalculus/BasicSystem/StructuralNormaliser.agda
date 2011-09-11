module BasicSystem.StructuralNormaliser where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.BigStepSemantics

mutual
  eval : forall {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ){v : Val Γ σ} ->
         eval t & vs ⇓ v -> Σ (Val Γ σ) \v' -> v == v'
  eval .(λt t) vs       (rlam {t = t})                 = sig (λv t vs) refl⁼  
  eval .top .(_ << v) (rvar {v = v})        = sig v refl⁼  
  eval .(t [ ts ]) vs  (rsubs {t = t}{ts = ts} p p')  with evalˢ ts vs p
  ... | sig ws refl⁼ = eval t ws p'
  eval .(t $ u) vs     (rapp {t = t}{u = u} p p' p'') with eval t vs p | eval u vs p'
  ... | sig f refl⁼ | sig a refl⁼ = f $$ a & p''

  _$$_&_ : forall {Γ σ τ}(f : Val Γ (σ ⇒ τ))(a : Val Γ σ){v : Val Γ τ} ->
           f $$ a ⇓ v -> Σ (Val Γ τ) \v' -> v == v'
  .(λv t vs) $$ a & r$lam {t = t}{vs = vs} p = eval t (vs << a) p  
  .(nev n)   $$ a & r$ne {n = n}             = sig (nev (appV n a)) refl⁼  

  evalˢ : forall {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ){ws : Env B Δ} ->
          evalˢ ts & vs ⇓ ws -> Σ (Env B Δ) \ws' -> ws == ws'
  evalˢ .(pop _)  .(vs << v) (rˢpop {vs = vs}{v = v})         = sig vs refl⁼  
  evalˢ .(ts < t)  vs        (rˢcons {ts = ts}{t = t} p p') with evalˢ ts vs p | eval t vs p'
  ... | sig ws refl⁼ | sig w refl⁼ = sig (ws << w) refl⁼ 
  evalˢ .id        vs        rˢid                             = sig vs refl⁼ 
  evalˢ .(ts ○ us) vs        (rˢcomp {ts = ts}{us = us} p p') with evalˢ us vs p
  ... | sig ws refl⁼ = evalˢ ts ws p' 

mutual
  quot : forall {Γ σ}(v : Val Γ σ){n : Nf Γ σ} -> 
          quot v ⇓ n -> Σ (Nf Γ σ) \n' -> n == n'
  quot f        (qarr p p')       with vwk _ f $$ nev (varV vZ) & p
  ... | sig v refl⁼ with quot v p' 
  ... | sig n refl⁼ = sig (λn n) refl⁼ 
  quot .(nev m) (qbase {m = m} p) with quotⁿ m p
  ... | sig n refl⁼ = sig (ne n) refl⁼ 

  quotⁿ : forall {Γ σ}(n : NeV Γ σ){n' : NeN Γ σ} -> 
          quotⁿ n ⇓ n' -> Σ (NeN Γ σ) \n'' -> n' == n''
  quotⁿ .(varV x)   (qⁿvar {x = x})             = sig (varN x) refl⁼ 
  quotⁿ .(appV m v) (qⁿapp {m = m}{v = v} p p') with quotⁿ m p | quot v p'
  ... | sig n refl⁼ | sig n' refl⁼ = sig (appN n n') refl⁼

open import BasicSystem.IdentityEnvironment

nf : forall {Γ σ}(t : Tm Γ σ){n : Nf Γ σ} ->
     nf t ⇓ n -> Σ (Nf Γ σ) \n' -> n == n'
nf t (norm⇓ p p') with eval t vid p 
... | sig v refl⁼ = quot v p'

