module FullSystem.Syntax where

-- Types
data Ty : Set where
  ι : Ty
  N : Ty
  One : Ty
  Zero : Ty
  _⇒_  : Ty -> Ty -> Ty
  _×_ : Ty -> Ty -> Ty
  _+_  : Ty -> Ty -> Ty

infixr 50 _⇒_

-- Terms
data Tm : Ty -> Set where
  K    : forall {σ τ} -> Tm (σ ⇒ τ ⇒ σ)
  S    : forall {σ τ ρ} -> Tm ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  _$_  : forall {σ τ} -> Tm (σ ⇒ τ) -> Tm σ -> Tm τ
  void : Tm One
  pr   : forall {σ τ} -> Tm (σ ⇒ τ ⇒ (σ × τ))
  fst  : forall {σ τ} -> Tm ((σ × τ) ⇒ σ)
  snd  : forall {σ τ} -> Tm ((σ × τ) ⇒ τ)
  NE   : forall {σ} -> Tm (Zero ⇒ σ) 
  inl  : forall {σ τ} -> Tm (σ ⇒ (σ + τ))
  inr  : forall {σ τ} -> Tm (τ ⇒ (σ + τ))
  C : forall {σ τ ρ} -> Tm ((σ ⇒ ρ) ⇒ (τ ⇒ ρ) ⇒ (σ + τ) ⇒ ρ)
  zero : Tm N
  suc  : Tm (N ⇒ N)
  R    : forall {σ} -> Tm (σ ⇒ (N ⇒ σ ⇒ σ) ⇒ N ⇒ σ)
 
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
  fst≡  : forall {σ τ}{t : Tm σ}{u : Tm τ} -> fst $ (pr $ t $ u) ≡ t
  snd≡  : forall {σ τ}{t : Tm σ}{u : Tm τ} -> snd $ (pr $ t $ u) ≡ u
  Cl : forall {σ τ ρ}{l : Tm (σ ⇒ ρ)}{r : Tm (τ ⇒ ρ)}{c : Tm σ} -> C $ l $ r $ (inl $ c) ≡ l $ c
  Cr : forall {σ τ ρ}{l : Tm (σ ⇒ ρ)}{r : Tm (τ ⇒ ρ)}{c : Tm τ} -> C $ l $ r $ (inr $ c) ≡ r $ c
  Rzero≡ : forall {σ}{z : Tm σ}{s : Tm (N ⇒ σ ⇒ σ)} -> R $ z $ s $ zero ≡ z
  Rsuc≡  : forall {σ}{z : Tm σ}{s : Tm (N ⇒ σ ⇒ σ)}{n : Tm N} -> 
           R $ z $ s $ (suc $ n) ≡ s $ n $ (R $ z $ s $ n)

-- Normal forms
data Nf : Ty -> Set where
  Kⁿ    : forall {σ τ} -> Nf (σ ⇒ τ ⇒ σ)
  Kⁿ¹   : forall {σ τ} -> Nf σ -> Nf (τ ⇒ σ)
  Sⁿ    : forall {σ τ ρ} -> Nf ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ¹   : forall {σ τ ρ} -> Nf (σ ⇒ τ ⇒ ρ) -> Nf ((σ ⇒ τ) ⇒ σ ⇒ ρ)
  Sⁿ²   : forall {σ τ ρ} -> Nf (σ ⇒ τ ⇒ ρ) -> Nf (σ ⇒ τ) -> Nf (σ ⇒ ρ)
  voidⁿ : Nf One
  prⁿ   : forall {σ τ} -> Nf (σ ⇒ τ ⇒ (σ × τ))
  prⁿ¹  : forall {σ τ} -> Nf σ -> Nf (τ ⇒ (σ × τ))
  prⁿ²  : forall {σ τ} -> Nf σ -> Nf τ -> Nf (σ × τ)
  fstⁿ  : forall {σ τ} -> Nf ((σ × τ) ⇒ σ)
  sndⁿ  : forall {σ τ} -> Nf ((σ × τ) ⇒ τ)
  NEⁿ  : forall {σ} -> Nf (Zero ⇒ σ)
  inlⁿ  : forall {σ τ} -> Nf (σ ⇒ (σ + τ))
  inlⁿ¹ : forall {σ τ} -> Nf σ -> Nf (σ + τ)
  inrⁿ  : forall {σ τ} -> Nf (τ ⇒ (σ + τ))
  inrⁿ¹ : forall {σ τ} -> Nf τ -> Nf (σ + τ)
  Cⁿ : forall {σ τ ρ} -> Nf ((σ ⇒ ρ) ⇒ (τ ⇒ ρ) ⇒ (σ + τ) ⇒ ρ)
  Cⁿ¹ : forall {σ τ ρ} -> Nf (σ ⇒ ρ) -> Nf ((τ ⇒ ρ) ⇒ (σ + τ) ⇒ ρ)
  Cⁿ² : forall {σ τ ρ} -> Nf (σ ⇒ ρ) -> Nf (τ ⇒ ρ) -> Nf ((σ + τ) ⇒ ρ)
  zeroⁿ : Nf N
  sucⁿ  : Nf (N ⇒ N)
  sucⁿ¹ : Nf N -> Nf N
  Rⁿ    : forall {σ} -> Nf (σ ⇒ (N ⇒ σ ⇒ σ) ⇒ N ⇒ σ)
  Rⁿ¹   : forall {σ} -> Nf σ -> Nf ((N ⇒ σ ⇒ σ) ⇒ N ⇒ σ)
  Rⁿ²   : forall {σ} -> Nf σ -> Nf (N ⇒ σ ⇒ σ) -> Nf (N ⇒ σ)

-- inclusion of normal forms in terms
⌜_⌝ : forall {σ} -> Nf σ -> Tm σ
⌜ Kⁿ       ⌝ = K
⌜ Kⁿ¹ x    ⌝ = K $ ⌜ x ⌝
⌜ Sⁿ       ⌝ = S
⌜ Sⁿ¹ x    ⌝ = S $ ⌜ x ⌝
⌜ Sⁿ² x y  ⌝ = S $ ⌜ x ⌝ $ ⌜ y ⌝
⌜ voidⁿ    ⌝ = void
⌜ prⁿ      ⌝ = pr 
⌜ prⁿ¹ x   ⌝ = pr $ ⌜ x ⌝
⌜ prⁿ² x y ⌝ = pr $ ⌜ x ⌝ $ ⌜ y ⌝
⌜ fstⁿ     ⌝ = fst
⌜ sndⁿ     ⌝ = snd 
⌜ NEⁿ     ⌝ = NE
⌜ inlⁿ¹ x ⌝ = inl $ ⌜ x ⌝
⌜ inlⁿ    ⌝ = inl
⌜ inrⁿ¹ x ⌝ = inr $ ⌜ x ⌝
⌜ inrⁿ    ⌝ = inr
⌜ Cⁿ      ⌝ = C
⌜ Cⁿ¹ l   ⌝ = C $ ⌜ l ⌝
⌜ Cⁿ² l r ⌝ = C $ ⌜ l ⌝ $ ⌜ r ⌝
⌜ zeroⁿ   ⌝ = zero
⌜ sucⁿ    ⌝ = suc
⌜ sucⁿ¹ n ⌝ = suc $ ⌜ n ⌝
⌜ Rⁿ      ⌝ = R
⌜ Rⁿ¹ z   ⌝ = R $ ⌜ z ⌝
⌜ Rⁿ² z f ⌝ = R $ ⌜ z ⌝ $ ⌜ f ⌝
