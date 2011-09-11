{-# OPTIONS --no-termination-check 
  #-}

module BasicSystem.Quote where
open import BasicSystem.Syntax
open import BasicSystem.SyntacticLemmas
open import BasicSystem.Variables
open import BasicSystem.Value
open import BasicSystem.Evaluator
open import BasicSystem.Weakening
open import BasicSystem.IdentityEnvironment
open import BasicSystem.Normal

mutual
  quot : forall {Γ σ} -> Val Γ σ -> Nf Γ σ
  quot (λv {σ = σ} t vs)  = 
    ncoe (λn (quot (ev t 
                        (wkˢ _ vs 
                        << 
                        coev (nev (var vZ)) 
                             (trans⁺ assoc⁺ (cong⁺ refl⁺ (comwkˢ _ vs))))))) 
         (trans⁺ (congΠ refl⁺ 
                        (cong⁺ refl⁺
                                (cong< (symˢ (comwkˢ _ vs)) 
                                       (trans (coh _ _) (sym (coh _ _)))))) 
                 (sym⁺ Π[]))
  quot (nev n)    = nen (quotⁿ n) 
  quot (coev v p) = ncoe (quot v) p 

  quotⁿ : forall {Γ σ} -> NeV Γ σ -> NeN Γ σ
  quotⁿ (var x)    = nvar x 
  quotⁿ (app {σ = σ}{τ = τ} n v) = 
    ncoeⁿ (napp (quotⁿ n) (quot v)) 
          (cong⁺ refl⁺ (cong< reflˢ (cong (comquot v) reflˢ)))
  quotⁿ (coen n p) = ncoeⁿ (quotⁿ n) p 

  comquot : forall {Γ σ}(v : Val Γ σ) -> 
           nemb (quot v) ≡ emb v
  comquot (λv {σ = σ} t vs)  =
    trans 
      (coh _ _) 
      (trans 
        (congλ 
          refl⁺
          (trans 
            (comquot (ev t (wkˢ _ vs << coev (nev (var vZ)) _)))
            (trans (sym (comev t (wkˢ (σ [ embˢ vs ]⁺) vs 
                                  << 
                                  coev (nev (var vZ)) _)))
                   (cong
                     refl 
                     (cong< 
                       (symˢ (comwkˢ _ vs)) 
                       (trans (coh _ _) (sym (coh _ _))))))))
                 (trans (sym λ[]) (coh _ Π[]))) 
  comquot (nev n)    = comquotⁿ n 
  comquot (coev v p) = 
    trans (coh _ _) (trans (comquot v) (sym (coh _ _))) 

  comquotⁿ : forall {Γ σ}(n : NeV Γ σ) -> 
           nembⁿ (quotⁿ n) ≡ embⁿ n
  comquotⁿ (var x)    = refl 
  comquotⁿ (app {σ = σ} n v)  = 
    trans (coh _ _) 
          (cong (congapp (comquotⁿ n)) 
                (cong< reflˢ (cong (comquot v) reflˢ))) 
  comquotⁿ (coen n p) = ir (comquotⁿ n) 