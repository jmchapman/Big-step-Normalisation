module NaturalNumbers.Structural where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep
open import NaturalNumbers.StrongComp

_$$⁼_&_ : forall {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} -> f $ⁿ a ⇓ n ->
          Σ (Nf τ) \n' -> n' == n
.Kⁿ        $$⁼ x & rKⁿ          = sig (Kⁿ¹ x) refl⁼ 
.(Kⁿ¹ x)   $$⁼ y & rKⁿ¹ {x = x} = sig x  refl⁼  
.Sⁿ        $$⁼ x & rSⁿ          = sig (Sⁿ¹ x) refl⁼  
.(Sⁿ¹ x)   $$⁼ y & rSⁿ¹ {x = x} = sig (Sⁿ² x y) refl⁼  
.(Sⁿ² x y) $$⁼ z & rSⁿ² {x = x}{y = y} p q r with x $$⁼ z & p | y $$⁼ z & q
... | sig u refl⁼ | sig v refl⁼ = u $$⁼ v & r 
.sucⁿ      $$⁼ n & rsucⁿ        = sig (sucⁿ¹ n) refl⁼  
.Rⁿ        $$⁼ z & rRⁿ          = sig (Rⁿ¹ z) refl⁼  
.(Rⁿ¹ z)   $$⁼ f & rRⁿ¹ {z = z} = sig (Rⁿ² z f) refl⁼ 
.(Rⁿ² z f) $$⁼ .zeroⁿ     & rRⁿ²z {z = z}{f = f} = sig z refl⁼ 
.(Rⁿ² z f) $$⁼ .(sucⁿ¹ n) & rRⁿ²f {z = z}{f = f}{n = n} p q r with f $$⁼ n & p | Rⁿ² z f $$⁼ n & q
... | sig fn refl⁼ | sig rn refl⁼ = fn $$⁼ rn & r 

nf⁼ : forall {σ}(t : Tm σ){n} -> t ⇓ n -> Σ (Nf σ) \n' -> n' == n
nf⁼ .K rK = sig Kⁿ refl⁼ 
nf⁼ .S rS = sig Sⁿ refl⁼
nf⁼ .(t $ u) (r$ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | sig f refl⁼ | sig a refl⁼ = f $$⁼ a & r
nf⁼ .zero rzero = sig zeroⁿ refl⁼ 
nf⁼ .suc rsuc   = sig sucⁿ refl⁼ 
nf⁼ .R rR       = sig Rⁿ refl⁼ 

nf : forall {σ} -> Tm σ -> Nf σ
nf t = σ₀ (nf⁼ t (π₀ (σ₁ (prop2 t))))