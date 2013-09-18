module FullSystem.StructuralNormaliser where
open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.OPE
open import FullSystem.BigStepSemantics

mutual
  eval : forall {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ){v : Val Γ σ} ->
         eval t & vs ⇓ v -> Σ (Val Γ σ) \v' -> v == v'
  eval .(λt t) vs       (rlam {t = t})                 = sig (λv t vs) refl⁼  
  eval .top .(_ << v) (rvar {v = v})        = sig v refl⁼  
  eval .(t [ ts ]) vs  (rsubs {t = t}{ts = ts} p p')  with evalˢ ts vs p
  ... | sig ws refl⁼ = eval t ws p'
  eval .(t $ u) vs     (rapp {t = t}{u = u} p p' p'') with eval t vs p | eval u vs p'
  ... | sig f refl⁼ | sig a refl⁼ = f $$ a & p''
  eval .zero vs rzero = sig zerov refl⁼ 
  eval .(suc t) vs (rsuc {t = t} p) with eval t vs p
  ... | sig v refl⁼ = sig (sucv v) refl⁼
  eval .(prim z s t) vs (rprim {z = z}{s = s}{t = t} p p' p'' p''') with eval z vs p | eval s vs p' | eval t vs p''
  ... | sig z' refl⁼ | sig s' refl⁼ | sig v refl⁼ = vprim z' s' v p''' 
  eval .void vs rvoid = sig voidv refl⁼  
  eval .(< t , u >) vs (r<,> {t = t}{u = u} p p') with eval t vs p | eval u vs p'
  ... | sig v refl⁼ | sig w refl⁼ = sig < v , w >v refl⁼   
  eval .(fst t) vs (rfst {t = t} p p') with eval t vs p
  ... | sig v refl⁼ = vfst v p' 
  eval .(snd t) vs (rsnd {t = t} p p') with eval t vs p
  ... | sig v refl⁼ = vsnd v p' 

  vprim : forall {Γ σ}(z : Val Γ σ)(s : Val Γ (N ⇒ σ ⇒ σ))(v : Val Γ N)
          {w : Val Γ σ} -> prim z & s & v ⇓ w -> Σ (Val Γ σ) \w' -> w == w'
  vprim z s .(nev n)  (rprn {n = n}) = sig (nev (primV z s n)) refl⁼ 
  vprim z s .zerov    rprz           = sig z refl⁼ 
  vprim z s .(sucv v) (rprs {v = v} p p' p'') with s $$ v & p | vprim z s v p'
  ... | sig f refl⁼ | sig w refl⁼ = f $$ w & p'' 

  vfst : forall {Γ σ τ}(v : Val Γ (σ × τ)){w : Val Γ σ} -> vfst v ⇓ w ->
         Σ (Val Γ σ) \w' -> w == w'
  vfst .(< v , w >v) (rfst<,> {v = v}{w = w}) = sig v refl⁼  
  vfst .(nev n)      (rfstnev {n = n})        = sig (nev (fstV n)) refl⁼  

  vsnd : forall {Γ σ τ}(v : Val Γ (σ × τ)){w : Val Γ τ} -> vsnd v ⇓ w ->
         Σ (Val Γ τ) \w' -> w == w'
  vsnd .(< v , w >v) (rsnd<,> {v = v}{w = w}) = sig w refl⁼
  vsnd .(nev n)      (rsndnev {n = n})        = sig (nev (sndV n)) refl⁼ 

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
  quot .(nev m) (qbase {m = m} p) with quotⁿ m p
  ... | sig n refl⁼ = sig (neι n) refl⁼ 
  quot f        (qarr p p')       with vwk _ f $$ nev (varV vZ) & p
  ... | sig v refl⁼ with quot v p' 
  ... | sig n refl⁼ = sig (λn n) refl⁼ 
  quot .zerov    qNz             = sig zeron refl⁼ 
  quot .(sucv v) (qNs {v = v} p) with quot v p
  ... | sig n refl⁼ = sig (sucn n) refl⁼
  quot .(nev n)  (qNn {n = n} p) with quotⁿ n p
  ... | sig n' refl⁼ = sig (neN n') refl⁼

  quotⁿ : forall {Γ σ}(n : NeV Γ σ){n' : NeN Γ σ} -> 
          quotⁿ n ⇓ n' -> Σ (NeN Γ σ) \n'' -> n' == n''
  quotⁿ .(varV x)   (qⁿvar {x = x})             = sig (varN x) refl⁼ 
  quotⁿ .(appV m v) (qⁿapp {m = m}{v} p p') with quotⁿ m p | quot v p'
  ... | sig n refl⁼ | sig n' refl⁼ = sig (appN n n') refl⁼
  quotⁿ .(primV z s n) (qⁿprim {z = z}{s}{n} p p' p'') with quot z p | quot s p' | quotⁿ n p''
  ... | sig z' refl⁼ | sig s' refl⁼ | sig n' refl⁼  = sig (primN z' s' n') refl⁼ 

open import FullSystem.IdentityEnvironment

nf : forall {Γ σ}(t : Tm Γ σ){n : Nf Γ σ} ->
     nf t ⇓ n -> Σ (Nf Γ σ) \n' -> n == n'
nf t (norm⇓ p p') with eval t vid p 
... | sig v refl⁼ = quot v p'

