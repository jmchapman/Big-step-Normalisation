module BasicSystem.Weakening where
open import BasicSystem.Syntax
open import BasicSystem.SyntacticLemmas
open import BasicSystem.Variables
open import BasicSystem.Value

mutual
  wk : forall {Γ σ}(τ : Ty Γ) -> Val Γ σ -> Val (Γ , τ) (σ [ pop τ ]⁺)
  wk τ (λv t vs)  = coev (λv t (wkˢ τ vs)) 
                         (sym⁺ (trans⁺ assoc⁺ (cong⁺ refl⁺ (comwkˢ τ vs))))
  wk τ (nev n)    = nev (wkⁿ τ n) 
  wk τ (coev v p) = coev (wk (coe⁺ τ (symˠ (fog⁺ p))) v) 
                         (cong⁺ p (congpop (coh⁺ τ _))) 

  comwk : forall {Γ σ}(τ : Ty Γ)(v : Val Γ σ) -> emb v [ pop τ ] ≡ emb (wk τ v)
  comwk τ (λv t vs)  = trans (trans assoc (cong refl (comwkˢ τ vs)))
                             (sym (coh _ _))
  comwk τ (nev n)    = comwkⁿ τ n 
  comwk τ (coev v p) = trans (trans (cong (coh _ _) 
                                          (congpop (sym⁺ (coh⁺ _ _))))
                                    (comwk _ v))
                             (sym (coh _ _)) 

  wkⁿ : forall {Γ σ}(τ : Ty Γ) -> NeV Γ σ -> NeV (Γ , τ) (σ [ pop τ ]⁺)
  wkⁿ τ (var v)    = var (vS v τ) 
  wkⁿ τ (app n v)  =
    coen (app (coen (wkⁿ τ n) Π[]) (wk τ v))
         (trans⁺
           assoc⁺ 
           (trans⁺
             (cong⁺
               refl⁺
               (transˢ
                 popid
                 (transˢ
                   (cong< 
                     (symˢ leftid)
                     (trans (sym (comwk τ v))                                                              (trans (cong (sym rightid) reflˢ) 
                                   (sym (coh _ _)))))
                   (symˢ •<))))
             (sym⁺ assoc⁺))) 
  wkⁿ τ (coen n p) = coen (wkⁿ (coe⁺ τ (symˠ (fog⁺ p))) n) 
                          (cong⁺ p (congpop (coh⁺ _ _))) 

  comwkⁿ : forall {Γ σ}(τ : Ty Γ)(n : NeV Γ σ) ->
         embⁿ n [ pop τ ] ≡ embⁿ (wkⁿ τ n)
  comwkⁿ τ (var v)    = refl
  comwkⁿ τ (app n v)  = 
    trans 
      (trans 
        (trans 
          (trans
            assoc 
            (cong
              refl
              (transˢ
                (transˢ 
                  •< 
                  (cong< 
                    leftid
                    (trans 
                      (coh _ _)
                      (trans (cong rightid reflˢ) (comwk τ v)))))
                (symˢ popid))))
          (sym assoc))
        (cong 
          (trans 
            (sym app[])
            (congapp 
              (trans 
                (coh _ Π[])
                (trans (comwkⁿ τ n) (sym (coh _ Π[]))))))
          reflˢ))
      (sym (coh _ _)) 
  comwkⁿ τ (coen n p) = trans (cong (coh _ _) (congpop (sym⁺ (coh⁺ _ _))))
                              (trans (comwkⁿ _ n) (sym (coh _ _)))

  wkˢ : forall {Γ Δ}(τ : Ty Γ) -> Env Γ Δ -> Env (Γ , τ) Δ
  wkˢ τ e         = e
  wkˢ τ (vs << v) = wkˢ τ vs << coev (wk τ v)
                                     (trans⁺ assoc⁺
                                             (cong⁺ refl⁺ (comwkˢ τ vs)))

  comwkˢ : forall {Γ Δ}(τ : Ty Γ)(vs : Env Γ Δ) ->
         embˢ vs • pop τ ≡ˢ embˢ (wkˢ τ vs)
  comwkˢ τ e = reflˢ
  comwkˢ τ (vs << v) = transˢ •< (cong< (comwkˢ τ vs) (ir (comwk τ v)))