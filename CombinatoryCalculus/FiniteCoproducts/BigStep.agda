module FiniteCoproducts.BigStep where
open import FiniteCoproducts.Syntax

-- Big step semantics (the graph of the recursive function)
data _$ⁿ_⇓_ : {σ τ : Ty} -> Nf (σ ⇒ τ) -> Nf σ -> Nf τ -> Set where
  rKⁿ    : {σ τ : Ty}{x : Nf σ} -> Kⁿ {σ} {τ} $ⁿ x ⇓ Kⁿ¹ x
  rKⁿ¹   : {σ τ : Ty}{x : Nf σ} -> {y : Nf τ} -> Kⁿ¹ x $ⁿ y ⇓ x
  rSⁿ    : {σ τ ρ : Ty} {x : Nf (σ ⇒ τ ⇒ ρ)} -> Sⁿ $ⁿ x ⇓ Sⁿ¹ x
  rSⁿ¹   : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)} -> 
            Sⁿ¹ x $ⁿ y ⇓ Sⁿ² x y
  rSⁿ²   : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)}{z : Nf σ}
           {u : Nf (τ ⇒ ρ)} -> x $ⁿ z ⇓ u -> {v : Nf τ} -> y $ⁿ z ⇓ v -> 
           {w : Nf ρ} -> u $ⁿ v ⇓ w -> Sⁿ² x y $ⁿ z ⇓ w 
  rCⁿ    : forall {σ τ ρ}{l : Nf (σ ⇒ ρ)} -> Cⁿ {τ = τ}  $ⁿ l ⇓ Cⁿ¹ l
  rCⁿ¹   : forall {σ τ ρ}{l : Nf (σ ⇒ ρ)}{r : Nf (τ ⇒ ρ)} -> 
           Cⁿ¹ l $ⁿ r ⇓ Cⁿ² l r
  rCⁿ²ˡ  : {σ τ ρ : Ty}{l : Nf (σ ⇒ ρ)}{r : Nf (τ ⇒ ρ)}{x : Nf σ}{y : Nf ρ} ->
           l $ⁿ x ⇓ y -> Cⁿ² l r $ⁿ inlⁿ¹ x ⇓ y 
  rCⁿ²ʳ  : {σ τ ρ : Ty}{l : Nf (σ ⇒ ρ)}{r : Nf (τ ⇒ ρ)}{x : Nf τ}{y : Nf ρ} ->
           r $ⁿ x ⇓ y -> Cⁿ² l r $ⁿ inrⁿ¹ x ⇓ y 
  rinl : forall {σ τ}{x : Nf σ} -> inlⁿ {τ = τ} $ⁿ x ⇓ inlⁿ¹ x
  rinr : forall {σ τ}{x : Nf τ} -> inrⁿ {σ = σ} $ⁿ x ⇓ inrⁿ¹ x

data _⇓_ : {σ : Ty} -> Tm σ -> Nf σ -> Set where
  rK   : {σ τ : Ty} -> K {σ} {τ} ⇓ Kⁿ
  rS   : {σ τ ρ : Ty} -> S {σ} {τ} {ρ} ⇓ Sⁿ
  r$   : forall {σ τ}{t : Tm (σ ⇒ τ)}{f} -> t ⇓ f -> {u : Tm σ}
         {a : Nf σ} -> u ⇓ a -> {v : Nf τ} -> f $ⁿ a ⇓ v  -> (t $ u) ⇓ v
  rNE  : forall {σ} -> NE {σ} ⇓ NEⁿ
  rinl : forall {σ τ} -> inl {σ}{τ} ⇓ inlⁿ
  rinr : forall {σ τ} -> inr {σ}{τ} ⇓ inrⁿ
  rC   : forall {σ τ ρ} -> C {σ} {τ} {ρ} ⇓ Cⁿ