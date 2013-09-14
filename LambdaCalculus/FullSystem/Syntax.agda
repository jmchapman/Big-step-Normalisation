module FullSystem.Syntax where

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty -> Ty -> Ty
  N   : Ty
  One : Ty
  _×_ : Ty -> Ty -> Ty


infixr 10 _⇒_

data Con : Set where
  ε   : Con
  _<_ : Con -> Ty -> Con

mutual
  data Tm : Con -> Ty -> Set where
    top  : forall {Γ σ} -> Tm (Γ < σ) σ
    _[_] : forall {Γ Δ σ} -> Tm Δ σ -> Sub Γ Δ -> Tm Γ σ
    λt    : forall {Γ σ τ} -> Tm (Γ < σ) τ -> Tm Γ (σ ⇒ τ)
    _$_  : forall {Γ σ τ} -> Tm Γ (σ ⇒ τ) -> Tm Γ σ -> Tm Γ τ
    zero : forall {Γ} -> Tm Γ N
    suc  : forall {Γ} -> Tm Γ N -> Tm Γ N
    prim : forall {Γ σ} -> Tm Γ σ -> Tm Γ (N ⇒ σ ⇒ σ) -> Tm Γ N -> Tm Γ σ
    void  : forall {Γ} -> Tm Γ One
    <_,_> : forall {Γ σ τ} -> Tm Γ σ -> Tm Γ τ -> Tm Γ (σ × τ)
    fst   : forall {Γ σ τ} -> Tm Γ (σ × τ) -> Tm Γ σ
    snd   : forall {Γ σ τ} -> Tm Γ (σ × τ) -> Tm Γ τ

  data Sub : Con -> Con -> Set where
    pop  : forall {Γ} σ -> Sub (Γ < σ) Γ
    _<_ : forall {Γ Δ σ} -> Sub Γ Δ -> Tm Γ σ -> Sub Γ (Δ < σ)
    id   : forall {Γ} -> Sub Γ Γ
    _○_  : forall {B Γ Δ} -> Sub Γ Δ -> Sub B Γ -> Sub B Δ

data Var : Con -> Ty -> Set where
  vZ : forall {Γ σ} -> Var (Γ < σ) σ
  vS : forall {Γ σ} τ -> Var Γ σ -> Var (Γ < τ) σ

mutual
  data Val : Con -> Ty -> Set where
    λv  : forall {Γ Δ σ τ} -> Tm (Δ < σ) τ -> Env Γ Δ -> 
          Val Γ (σ ⇒ τ)
    nev : forall {Γ σ} -> NeV Γ σ -> Val Γ σ
    zerov : forall {Γ} -> Val Γ N
    sucv  : forall {Γ} -> Val Γ N -> Val Γ N
    voidv  : forall {Γ} -> Val Γ One
    <_,_>v : forall {Γ σ τ} -> Val Γ σ -> Val Γ τ -> Val Γ (σ × τ)

  data Env : Con -> Con -> Set where
    ε   : forall {Γ} -> Env Γ ε
    _<<_ : forall {Γ Δ σ} -> Env Γ Δ -> Val Γ σ -> Env Γ (Δ < σ)

  data NeV : Con -> Ty -> Set where
    varV  : forall {Γ σ} -> Var Γ σ -> NeV Γ σ
    appV  : forall {Γ σ τ} -> NeV Γ (σ ⇒ τ) -> Val Γ σ -> NeV Γ τ
    primV : forall {Γ σ} -> Val Γ σ -> Val Γ (N ⇒ σ ⇒ σ) -> NeV Γ N -> NeV Γ σ
    fstV : forall {Γ σ τ} -> NeV Γ (σ × τ) -> NeV Γ σ
    sndV : forall {Γ σ τ} -> NeV Γ (σ × τ) -> NeV Γ τ

mutual
  data Nf : Con -> Ty -> Set where
    λn    : forall {Γ σ τ} -> Nf (Γ < σ) τ -> Nf Γ (σ ⇒ τ)
    neι   : forall {Γ} -> NeN Γ ι -> Nf Γ ι
    neN   : forall {Γ} -> NeN Γ N -> Nf Γ N
    zeron : forall {Γ} -> Nf Γ N
    sucn  : forall {Γ} -> Nf Γ N -> Nf Γ N
    voidn  : forall {Γ} -> Nf Γ One
    <_,_>n : forall {Γ σ τ} -> Nf Γ σ -> Nf Γ τ -> Nf Γ (σ × τ)

  data NeN : Con -> Ty -> Set where
    varN  : forall {Γ σ} -> Var Γ σ -> NeN Γ σ
    appN  : forall {Γ σ τ} -> NeN Γ (σ ⇒ τ) -> Nf Γ σ -> NeN Γ τ
    primN : forall {Γ σ} -> Nf Γ σ -> Nf Γ (N ⇒ σ ⇒ σ) -> NeN Γ N -> NeN Γ σ
    fstN : forall {Γ σ τ} -> NeN Γ (σ × τ) -> NeN Γ σ
    sndN : forall {Γ σ τ} -> NeN Γ (σ × τ) -> NeN Γ τ
