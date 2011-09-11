module BasicSystem.Syntax where

-- Types
data Ty : Set where
  ι : Ty
  _⇒_ : Ty -> Ty -> Ty

infixr 50 _⇒_

-- Terms
data Tm : Ty -> Set where
  K : forall {σ τ} -> Tm (σ ⇒ τ ⇒ σ)
  S : forall {σ τ ρ} -> Tm ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  _$_ : forall {σ τ} -> Tm (σ ⇒ τ) -> Tm σ -> Tm τ

infixl 50 _$_

-- Definitional Equality
data _≡_ : forall {σ} -> Tm σ -> Tm σ -> Set where
  refl  : forall {σ}{t : Tm σ} -> t ≡ t
  sym   : forall {σ}{t t' : Tm σ} -> t ≡ t' -> t' ≡ t
  trans : forall {σ}{t t' t'' : Tm σ} -> t ≡ t' -> t' ≡ t'' -> t ≡ t''
  K≡    : forall {σ τ}{x : Tm σ}{y : Tm τ} -> K $ x $ y ≡ x
  S≡    : forall {σ τ ρ}{x : Tm (σ ⇒ τ ⇒ ρ)}{y : Tm (σ ⇒ τ)}{z : Tm σ} ->
          S $ x $ y $ z ≡ x $ z $ (y $ z)
  $≡    : forall {σ}{τ}{t t' : Tm (σ ⇒ τ)}{u u' : Tm σ} -> t ≡ t' -> u ≡ u' ->
          t $ u ≡ t' $ u'

-- Normal forms
data Nf : Ty -> Set where
  Kⁿ   : forall {σ τ} -> Nf (σ ⇒ τ ⇒ σ)
  Kⁿ¹  : forall {σ τ} -> Nf σ -> Nf (τ ⇒ σ)
  Sⁿ   : forall {σ τ ρ} -> Nf ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ¹  : forall {σ τ ρ} -> Nf (σ ⇒ τ ⇒ ρ) -> Nf ((σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ²  : forall {σ τ ρ} -> Nf (σ ⇒ τ ⇒ ρ) -> Nf (σ ⇒ τ) -> Nf (σ ⇒ ρ)

-- inclusion of normal forms in terms
⌜_⌝ : forall {σ} -> Nf σ -> Tm σ
⌜ Kⁿ      ⌝ = K
⌜ Kⁿ¹ x   ⌝ = K $ ⌜ x ⌝
⌜ Sⁿ      ⌝ = S
⌜ Sⁿ¹ x   ⌝ = S $ ⌜ x ⌝
⌜ Sⁿ² x y ⌝ = S $ ⌜ x ⌝ $ ⌜ y ⌝
