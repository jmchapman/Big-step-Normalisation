module BasicSystem.Value where
open import BasicSystem.Syntax
open import BasicSystem.SyntacticLemmas
open import BasicSystem.Variables

mutual
  data Val : forall Γ -> Ty Γ -> Set where
    λv    : forall {Γ Δ σ τ} -> Tm (Δ , σ) τ -> (vs : Env Γ Δ) ->
            Val Γ (Π σ τ [ embˢ vs ]⁺)
    nev   : forall {Γ σ} -> NeV Γ σ -> Val Γ σ
    coev  : forall {Γ Γ' σ σ'} -> Val Γ σ -> σ ≡⁺ σ' -> Val Γ' σ'

  emb : forall {Γ σ} -> Val Γ σ -> Tm Γ σ
  emb (λv t vs)    = λt t [ embˢ vs ]
  emb (nev n)      = embⁿ n
  emb (coev v p)   = coe (emb v) p

  data NeV : forall Γ -> Ty Γ -> Set where
    var  : forall {Γ σ} -> Var Γ σ -> NeV Γ σ
    app  : forall {Γ σ τ} -> NeV Γ (Π σ τ) ->
           (v : Val Γ σ) -> NeV Γ (τ [ id < emb v [ id ] ]⁺)
    coen : forall {Γ Γ' σ σ'} -> NeV Γ σ -> σ ≡⁺ σ' -> NeV Γ' σ'

  embⁿ : forall {Γ σ} -> NeV Γ σ -> Tm Γ σ
  embⁿ (var x)    = embˣ x 
  embⁿ (app n v)  = embⁿ n $ emb v 
  embⁿ (coen n p) = coe (embⁿ n) p

  data Env (Γ : Con) : Con -> Set where
    e    : Env Γ ε
    _<<_ : forall {Δ σ}(vs : Env Γ Δ) -> Val Γ (σ [ embˢ vs ]⁺) -> 
           Env Γ (Δ , σ)

  embˢ : forall {Γ Δ} -> Env Γ Δ -> Sub Γ Δ
  embˢ e         = εˢ 
  embˢ (vs << v) = embˢ vs < emb v 

mutual
  coevˢ : forall {Γ Γ' Δ Δ'} -> Env Γ Δ -> Γ ≡ˠ Γ' -> Δ ≡ˠ Δ' -> Env Γ' Δ'
  coevˢ e p congε = e
  coevˢ (vs << v) p (cong, q q') =
    coevˢ vs p q << coev v (cong⁺ q' (cohvˢ vs p q))

  cohvˢ : forall {Γ Γ' Δ Δ'}(vs : Env Γ Δ)(p : Γ ≡ˠ Γ')(q : Δ ≡ˠ Δ') ->
          embˢ vs ≡ˢ embˢ (coevˢ vs p q)
  cohvˢ e congε congε = reflˢ
  cohvˢ e (cong, p p') congε = cong• (cohvˢ e p congε) (congpop p')
  cohvˢ (vs << v) p (cong, q q') = cong< (cohvˢ vs p q) (sym (coh _ _))

data VTy : Con -> Set where
  VU : forall {Γ} -> VTy Γ
  VEl : forall {Γ} -> Val Γ U -> VTy Γ
  VΠ : forall {Γ Δ} σ -> Ty (Δ , σ) -> Env Γ Δ -> VTy Γ

emb⁺ : forall {Γ} -> VTy Γ -> Ty Γ
emb⁺ VU = U
emb⁺ (VEl σ) = El (emb σ)
emb⁺ (VΠ σ τ vs) = Π σ τ [ embˢ vs ]⁺
