module NaturalNumbers.BigStep where
open import NaturalNumbers.Syntax

-- Big step semantics (the graph of the recursive function)
data _$ⁿ_⇓_ : {σ τ : Ty} -> Nf (σ ⇒ τ) -> Nf σ -> Nf τ -> Set where
  rKⁿ   : {σ τ : Ty}{x : Nf σ} -> Kⁿ {σ} {τ} $ⁿ x ⇓ Kⁿ¹ x
  rKⁿ¹  : {σ τ : Ty}{x : Nf σ} -> {y : Nf τ} -> Kⁿ¹ x $ⁿ y ⇓ x
  rSⁿ   : {σ τ ρ : Ty} {x : Nf (σ ⇒ τ ⇒ ρ)} -> Sⁿ $ⁿ x ⇓ Sⁿ¹ x
  rSⁿ¹  : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)} -> 
          Sⁿ¹ x $ⁿ y ⇓ Sⁿ² x y
  rSⁿ²  : {σ τ ρ : Ty}{x : Nf (σ ⇒ τ ⇒ ρ)}{y : Nf (σ ⇒ τ)}{z : Nf σ}
          {u : Nf (τ ⇒ ρ)} -> x $ⁿ z ⇓ u -> {v : Nf τ} -> y $ⁿ z ⇓ v -> 
          {w : Nf ρ} -> u $ⁿ v ⇓ w -> Sⁿ² x y $ⁿ z ⇓ w 
  rsucⁿ : {n : Nf N} -> sucⁿ $ⁿ n ⇓ sucⁿ¹ n
  rRⁿ   : {σ : Ty}{z : Nf σ} -> Rⁿ $ⁿ z ⇓ Rⁿ¹ z
  rRⁿ¹  : {σ : Ty}{z : Nf σ}{f : Nf (N ⇒ σ ⇒ σ)} -> Rⁿ¹ z $ⁿ f ⇓ Rⁿ² z f
  rRⁿ²z : {σ : Ty}{z : Nf σ}{f : Nf (N ⇒ σ ⇒ σ)} -> 
          Rⁿ² z f $ⁿ zeroⁿ ⇓ z
  rRⁿ²f : {σ : Ty}{z : Nf σ}{f : Nf (N ⇒ σ ⇒ σ)}{n : Nf N}
          {fn : Nf (σ ⇒ σ)} -> f $ⁿ n ⇓ fn -> 
          {rn : Nf σ} -> Rⁿ² z f $ⁿ n ⇓ rn -> 
          {rsn : Nf σ} -> fn $ⁿ rn ⇓ rsn -> Rⁿ² z f $ⁿ sucⁿ¹ n ⇓ rsn

data _⇓_ : {σ : Ty} -> Tm σ -> Nf σ -> Set where
  rK    : {σ τ : Ty} -> K {σ} {τ} ⇓ Kⁿ
  rS    : {σ τ ρ : Ty} -> S {σ} {τ} {ρ} ⇓ Sⁿ
  r$    : forall {σ τ}{t : Tm (σ ⇒ τ)}{f} -> t ⇓ f -> {u : Tm σ}
          {a : Nf σ} -> u ⇓ a -> {v : Nf τ} -> f $ⁿ a ⇓ v  -> (t $ u) ⇓ v
  rzero : zero ⇓ zeroⁿ
  rsuc  : suc ⇓ sucⁿ
  rR    : forall {σ} -> R {σ} ⇓ Rⁿ