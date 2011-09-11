module BasicSystem.Structural where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep
open import BasicSystem.StrongComp

_$$⁼_&_ : forall {σ τ}(f : Nf (σ ⇒ τ))(a : Nf σ){n} -> f $ⁿ a ⇓ n ->
          Σ (Nf τ) \n' -> n' == n
.Kⁿ        $$⁼ x & rKⁿ          = sig (Kⁿ¹ x) refl⁼ 
.(Kⁿ¹ x)   $$⁼ y & rKⁿ¹ {x = x} = sig x  refl⁼  
.Sⁿ        $$⁼ x & rSⁿ          = sig (Sⁿ¹ x) refl⁼  
.(Sⁿ¹ x)   $$⁼ y & rSⁿ¹ {x = x} = sig (Sⁿ² x y) refl⁼  
.(Sⁿ² x y) $$⁼ z & rSⁿ² {x = x}{y = y} p q r with x $$⁼ z & p | y $$⁼ z & q
... | sig u refl⁼ | sig v refl⁼ = u $$⁼ v & r 

nf⁼ : forall {σ}(t : Tm σ){n} -> t ⇓ n -> Σ (Nf σ) \n' -> n' == n
nf⁼ .K rK = sig Kⁿ refl⁼ 
nf⁼ .S rS = sig Sⁿ refl⁼
nf⁼ .(t $ u) (r$ {t = t} p {u = u} q r) with nf⁼ t p | nf⁼ u q
... | sig f refl⁼ | sig a refl⁼ = f $$⁼ a & r

nf : forall {σ} -> Tm σ -> Nf σ
nf t = σ₀ (nf⁼ t (π₀ (σ₁ (prop2 t))))

complete : forall {σ}(t : Tm σ) -> t ≡ ⌜ nf t ⌝ 
complete t with nf⁼ t (π₀ (σ₁ (prop2 t)))
... | (sig ._ refl⁼) = π₂ (σ₁(prop2 t)) 