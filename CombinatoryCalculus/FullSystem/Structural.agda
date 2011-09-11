module FullSystem.Structural where
open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.BigStep
open import FullSystem.StrongComp

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
.inlⁿ      $$⁼ x & rinl          = sig (inlⁿ¹ x) refl⁼
.inrⁿ      $$⁼ x & rinr          = sig (inrⁿ¹ x) refl⁼
.Cⁿ        $$⁼ l  & rCⁿ          = sig (Cⁿ¹ l) refl⁼  
.(Cⁿ¹ l)   $$⁼ r  & rCⁿ¹ {l = l} = sig (Cⁿ² l r) refl⁼  
.(Cⁿ² l r) $$⁼ .(inlⁿ¹ x) & rCⁿ²ˡ {l = l}{r = r}{x = x} p = l $$⁼ x & p
.(Cⁿ² l r) $$⁼ .(inrⁿ¹ x) & rCⁿ²ʳ {l = l}{r = r}{x = x} p = r $$⁼ x & p
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
nf⁼ .void rvoid = sig voidⁿ refl⁼ 
nf⁼ .pr rpr = sig prⁿ refl⁼ 
nf⁼ .fst  rfst = sig fstⁿ refl⁼ 
nf⁼ .snd  rsnd = sig sndⁿ refl⁼ 
nf⁼ .NE rNE = sig NEⁿ refl⁼ 
nf⁼ .inl rinl = sig inlⁿ refl⁼
nf⁼ .inr rinr = sig inrⁿ refl⁼
nf⁼ .C rC = sig Cⁿ refl⁼ 
nf⁼ .zero rzero = sig zeroⁿ refl⁼ 
nf⁼ .suc rsuc   = sig sucⁿ refl⁼ 
nf⁼ .R rR       = sig Rⁿ refl⁼ 

nf : forall {σ} -> Tm σ -> Nf σ
nf t = σ₀ (nf⁼ t (π₀ (σ₁ (prop2 t))))