module BetaEta.Normal where
open import BetaEta.Syntax
open import BetaEta.SyntacticLemmas
open import BetaEta.Variables
open import BetaEta.Value
open import BetaEta.IdentityEnvironment

mutual
  data Nf : forall Γ -> Ty Γ -> Set where
    λn   : forall {Γ σ τ} -> Nf (Γ , σ) τ -> Nf Γ (Π σ τ)
    neu  : forall {Γ} -> NeN Γ U -> Nf Γ U
    neel : forall {Γ σ} -> NeN Γ (El σ) -> Nf Γ (El σ)
    ncoe : forall {Γ Γ' σ σ'} -> Nf Γ σ -> σ ≡⁺ σ' -> Nf Γ' σ'

  nemb : forall {Γ σ} -> Nf Γ σ -> Tm Γ σ
  nemb (λn n)     = λt (nemb n)
  nemb (neu n)    = nembⁿ n
  nemb (neel n)   = nembⁿ n
  nemb (ncoe n p) = coe (nemb n) p

  data NeN : forall Γ -> Ty Γ -> Set where
    nvar  : forall {Γ σ} -> Var Γ σ -> NeN Γ σ
    napp  : forall {Γ σ τ} -> NeN Γ (Π σ τ) -> (n : Nf Γ σ) ->
            NeN Γ (τ [ id < nemb n [ id ] ]⁺)
    ncoeⁿ : forall {Γ Γ' σ σ'} -> NeN Γ σ -> σ ≡⁺ σ' -> NeN Γ' σ'

  nembⁿ : forall {Γ σ} -> NeN Γ σ -> Tm Γ σ
  nembⁿ (nvar x)    = embˣ x
  nembⁿ (napp n n') = nembⁿ n $ nemb n'
  nembⁿ (ncoeⁿ n p) = coe (nembⁿ n) p

mutual
  vemb : forall {Γ σ} -> Nf Γ σ -> Val Γ σ
  vemb (λn n)     = coev (λv (nemb n) vid)
                         (trans⁺ (cong⁺ refl⁺ (symˢ comvid)) rightid⁺)
  vemb (neu n)    = nev (vembⁿ n)
  vemb (neel n)   = nev (vembⁿ n)
  vemb (ncoe n p) = coev (vemb n) p

  vembⁿ : forall {Γ σ} -> NeN Γ σ -> NeV Γ σ
  vembⁿ (nvar x) = var x
  vembⁿ (napp n n') = coen (app (vembⁿ n) (vemb n')) 
                           (cong⁺ refl⁺ 
                                  (cong< reflˢ (cong (comvemb n') reflˢ)))
  vembⁿ (ncoeⁿ n p) = coen (vembⁿ n) p
  
  comvemb : forall {Γ σ}(n : Nf Γ σ) -> emb (vemb n) ≡ nemb n
  comvemb (λn n)     = trans (coh _ _) 
                             (trans (cong refl (symˢ comvid)) rightid) 
  comvemb (neu n)    = comvembⁿ n
  comvemb (neel n)   = comvembⁿ n 
  comvemb (ncoe n p) = ir (comvemb n) 

  comvembⁿ : forall {Γ σ}(n : NeN Γ σ) -> embⁿ (vembⁿ n) ≡ nembⁿ n
  comvembⁿ (nvar x)    = refl 
  comvembⁿ (napp n n') = trans (coh _ _)
                               (cong (congapp (comvembⁿ n)) 
                                     (cong< reflˢ (cong (comvemb n') reflˢ)))
  comvembⁿ (ncoeⁿ n p) = ir (comvembⁿ n) 