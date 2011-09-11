module BasicSystem.IdentityEnvironment where
open import BasicSystem.Syntax
open import BasicSystem.Variables
open import BasicSystem.Value
open import BasicSystem.Weakening

mutual
  vid : forall {Γ} -> Env Γ Γ
  vid {ε}     = e
  vid {Γ , σ} =
    wkˢ σ (vid {Γ}) << coev (nev (var (vZ {σ = σ})))
                            (cong⁺ refl⁺
                                  (transˢ (symˢ leftid)
                                         (transˢ (cong• comvid reflˢ)
                                                (comwkˢ σ vid))))

  comvid : forall {Γ} -> id {Γ} ≡ˢ embˢ (vid {Γ})
  comvid {ε}     = reflˢ
  comvid {Γ , σ} =
    transˢ (symˢ poptop)
           (cong< (transˢ (symˢ leftid) 
                                (transˢ (cong• comvid reflˢ) (comwkˢ σ vid)))
                  (sym (coh _ _)))
