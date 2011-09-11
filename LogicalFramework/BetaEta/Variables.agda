module BetaEta.Variables where
open import BetaEta.Syntax

data Var : forall Γ -> Ty Γ -> Set where
  vZ : forall {Γ σ} -> Var (Γ , σ) (σ [ pop σ ]⁺)
  vS : forall {Γ σ} -> Var Γ σ -> (τ : Ty Γ) -> Var (Γ , τ) (σ [ pop τ ]⁺)

embˣ : forall {Γ σ} -> Var Γ σ -> Tm Γ σ
embˣ vZ     = top
embˣ (vS x τ) = embˣ x [ pop τ ]