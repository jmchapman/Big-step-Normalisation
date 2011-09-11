module BasicSystem.BigStep where
open import BasicSystem.Syntax

-- Big step semantics (the graph of the recursive function)
data _$ⁿ_⇓_ : {σ τ : Ty} -> Nf (σ ⇒ τ) -> Nf σ -> Nf τ -> Set where
  rKⁿ  : {σ τ : Ty}{x : Nf σ} -> Kⁿ {σ} {τ} $ⁿ x ⇓ Kⁿ¹ x
  rKⁿ¹ : {σ τ : Ty}{x : Nf σ} -> {y : Nf τ} -> Kⁿ¹ x $ⁿ y ⇓ x
  rSⁿ  : {σ τ ρ : Ty} {x : Nf (σ ⇒ τ ⇒ ρ)} -> Sⁿ $ⁿ x ⇓ Sⁿ¹ x
  rSⁿ¹ : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)} -> 
         Sⁿ¹ x $ⁿ y ⇓ Sⁿ² x y
  rSⁿ² : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)}{z : Nf σ}
         {u : Nf (τ ⇒ ρ)} -> x $ⁿ z ⇓ u -> {v : Nf τ} -> y $ⁿ z ⇓ v -> 
         {w : Nf ρ} -> u $ⁿ v ⇓ w -> Sⁿ² x y $ⁿ z ⇓ w 

data _⇓_ : {σ : Ty} -> Tm σ -> Nf σ -> Set where
  rK : {σ τ : Ty} -> K {σ} {τ} ⇓ Kⁿ
  rS : {σ τ ρ : Ty} -> S {σ} {τ} {ρ} ⇓ Sⁿ
  r$ : forall {σ τ}{t : Tm (σ ⇒ τ)}{f} -> t ⇓ f -> {u : Tm σ}
       {a : Nf σ} -> u ⇓ a -> {v : Nf τ} -> f $ⁿ a ⇓ v  -> (t $ u) ⇓ v
          