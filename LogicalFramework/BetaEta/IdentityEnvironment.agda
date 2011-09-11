module BetaEta.IdentityEnvironment where
open import BetaEta.Syntax
open import BetaEta.Variables
open import BetaEta.Value
open import BetaEta.Weakening

mutual
  vid : forall {Γ} -> Env Γ Γ
  vid {ε}     = e
  vid {Γ , σ} =
    wkˢ σ (vid {Γ}) << coev (nev (var (vZ {σ = σ})))
                            (cong⁺ refl⁺
                                  (transˢ (symˢ leftid)
                                         (transˢ (cong• comvid reflˢ)
                                                (comwkˢ σ vid))))

  abstract
    comvid : forall {Γ} -> id {Γ} ≡ˢ embˢ (vid {Γ})
    comvid {ε}     = reflˢ
    comvid {Γ , σ} =
      transˢ (symˢ poptop)
             (cong< (transˢ (symˢ leftid) 
                                  (transˢ (cong• comvid reflˢ) (comwkˢ σ vid)))
                    (sym (coh _ _)))
