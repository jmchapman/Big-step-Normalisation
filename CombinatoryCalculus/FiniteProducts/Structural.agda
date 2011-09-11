module FiniteProducts.Structural where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep
open import FiniteProducts.StrongComp

_$$⁼_&_ : forall {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} -> f $ⁿ a ⇓ n ->
          Σ (Nf τ) \n' -> n' == n
.Kⁿ        $$⁼ x & rKⁿ            = sig (Kⁿ¹ x) refl⁼ 
.(Kⁿ¹ x)   $$⁼ y & rKⁿ¹ {x = x}   = sig x  refl⁼  
.Sⁿ        $$⁼ x & rSⁿ            = sig (Sⁿ¹ x) refl⁼  
.(Sⁿ¹ x)   $$⁼ y & rSⁿ¹ {x = x}   = sig (Sⁿ² x y) refl⁼  
.(Sⁿ² x y) $$⁼ z & rSⁿ² {x = x}{y = y} p q r with x $$⁼ z & p | y $$⁼ z & q
... | sig u refl⁼ | sig v refl⁼ = u $$⁼ v & r 
.prⁿ       $$⁼ x & rprⁿ           = sig (prⁿ¹ x) refl⁼  
.(prⁿ¹ x)  $$⁼ y & rprⁿ¹ {x = x}  = sig (prⁿ² x y) refl⁼  
.fstⁿ      $$⁼ (prⁿ² x y) & rfstⁿ = sig x refl⁼ 
.sndⁿ      $$⁼ (prⁿ² x y) & rsndⁿ = sig y refl⁼ 

nf⁼ : forall {σ}(t : Tm σ){n} -> t ⇓ n -> Σ (Nf σ) \n' -> n' == n
nf⁼ .K rK = sig Kⁿ refl⁼ 
nf⁼ .S rS = sig Sⁿ refl⁼
nf⁼ .(t $ u) (r$ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | sig f refl⁼ | sig a refl⁼ = f $$⁼ a & r
nf⁼ .void rvoid = sig voidⁿ refl⁼ 
nf⁼ .pr rpr = sig prⁿ refl⁼ 
nf⁼ .fst  rfst = sig fstⁿ refl⁼ 
nf⁼ .snd  rsnd = sig sndⁿ refl⁼ 

nf : forall {σ} -> Tm σ -> Nf σ
nf t = σ₀ (nf⁼ t (π₀ (σ₁ (prop2 t))))