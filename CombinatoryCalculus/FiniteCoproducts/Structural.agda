module FiniteCoproducts.Structural where
open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.BigStep
open import FiniteCoproducts.StrongComp

_$$⁼_&_ : forall {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} -> f $ⁿ a ⇓ n ->
          Σ (Nf τ) \n' -> n' == n
.Kⁿ        $$⁼ x & rKⁿ           = sig (Kⁿ¹ x) refl⁼ 
.(Kⁿ¹ x)   $$⁼ y & rKⁿ¹ {x = x}  = sig x  refl⁼  
.Sⁿ        $$⁼ x & rSⁿ           = sig (Sⁿ¹ x) refl⁼  
.(Sⁿ¹ x)   $$⁼ y & rSⁿ¹ {x = x}  = sig (Sⁿ² x y) refl⁼  
.(Sⁿ² x y) $$⁼ z & rSⁿ² {x = x}{y = y} p q r with x $$⁼ z & p | y $$⁼ z & q
... | sig u refl⁼ | sig v refl⁼  = u $$⁼ v & r 
.inlⁿ      $$⁼ x & rinl          = sig (inlⁿ¹ x) refl⁼
.inrⁿ      $$⁼ x & rinr          = sig (inrⁿ¹ x) refl⁼
.Cⁿ        $$⁼ l  & rCⁿ          = sig (Cⁿ¹ l) refl⁼  
.(Cⁿ¹ l)   $$⁼ r  & rCⁿ¹ {l = l} = sig (Cⁿ² l r) refl⁼  
.(Cⁿ² l r) $$⁼ .(inlⁿ¹ x) & rCⁿ²ˡ {l = l}{r = r}{x = x} p = l $$⁼ x & p
.(Cⁿ² l r) $$⁼ .(inrⁿ¹ x) & rCⁿ²ʳ {l = l}{r = r}{x = x} p = r $$⁼ x & p

nf⁼ : forall {σ}(t : Tm σ){n} -> t ⇓ n -> Σ (Nf σ) \n' -> n' == n
nf⁼ .K rK = sig Kⁿ refl⁼ 
nf⁼ .S rS = sig Sⁿ refl⁼
nf⁼ .(t $ u) (r$ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | sig f refl⁼ | sig a refl⁼ = f $$⁼ a & r
nf⁼ .NE rNE = sig NEⁿ refl⁼ 
nf⁼ .inl rinl = sig inlⁿ refl⁼
nf⁼ .inr rinr = sig inrⁿ refl⁼
nf⁼ .C rC = sig Cⁿ refl⁼ 

nf : forall {σ} -> Tm σ -> Nf σ
nf t = σ₀ (nf⁼ t (π₀ (σ₁ (prop2 t))))