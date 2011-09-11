module BetaEta.Replace where
open import BetaEta.Syntax
open import BetaEta.SyntacticLemmas
open import BetaEta.Value
open import BetaEta.IdentityEnvironment
open import BetaEta.Evaluator

mutual
  replace : forall {Γ σ} -> Val Γ σ -> Val Γ (emb⁺ (ev⁺ σ vid))
  replace (λv t vs) = λv t (evˢ (embˢ vs) vid) 
  replace (nev n) = nev (replaceⁿ n) 
  replace (coev {σ = σ}{σ' = σ'} v p) =
    coev (replace v)
         (trans⁺ (sym⁺ (comev⁺ σ vid)) 
                 (trans⁺ (cong⁺ p 
                                (transˢ (transˢ (symˢ comvid)
                                                (congid (fog⁺ p)))
                                        comvid))
                         (comev⁺ σ' vid))) 

  replaceⁿ : forall {Γ σ} -> NeV Γ σ -> NeV Γ (emb⁺ (ev⁺ σ vid))
  replaceⁿ (var {σ = σ} x)    = 
    coen (var x)
         (trans⁺ (trans⁺ (sym⁺ rightid⁺) (cong⁺ refl⁺ comvid)) (comev⁺ σ vid))
  replaceⁿ (app {σ = σ}{τ = τ} n v)          = 
    coen
      (app (coen (replaceⁿ n) Π[]) 
           (coev (replace v) (sym⁺ (comev⁺ σ vid))))
      
      (trans⁺ 
        assoc⁺ 
        (trans⁺
          (cong⁺
            refl⁺
            (transˢ
              •< 
              (cong<
                (transˢ assocˢ (transˢ (cong• reflˢ pop<) rightidˢ)) 
                (ir
                  (trans
                    (trans 
                      (cong (coh _ _) reflˢ) 
                      (trans 
                        top<
                        (trans
                          (cong (trans (coh _ _) (comreplace v)) comvid)
                          (comev (emb v) vid))))
                    (sym (coh _ _)))))))
          (comev⁺ τ _)))
        
  replaceⁿ (coen {σ = σ}{σ' = σ'} n p)         =
    coen (replaceⁿ n)
         (trans⁺ (trans⁺ (sym⁺ (comev⁺ σ vid)) 
                         (cong⁺ p
                                (transˢ (transˢ (symˢ comvid)
                                                (congid (fog⁺ p))) 
                                        comvid)))
                 (comev⁺ σ' vid)) 

  abstract
    comreplace : forall {Γ σ}(v : Val Γ σ) ->
                 emb (replace v) ≡ emb v
    comreplace (λv t vs)  = cong refl (transˢ (symˢ (comevˢ (embˢ vs) vid)) 
                                              (transˢ (cong• reflˢ (symˢ comvid))
                                                      rightidˢ)) 
    comreplace (nev n)    = comreplaceⁿ n 
    comreplace (coev v p) = ir (comreplace v) 

    comreplaceⁿ : forall {Γ σ}(n : NeV Γ σ) ->
                  embⁿ (replaceⁿ n) ≡ embⁿ n
    comreplaceⁿ (var x)    = coh _ _ 
    comreplaceⁿ (app n v)  =
      trans (coh _ _) 
            (cong (congapp (trans (coh _ _) (comreplaceⁿ n)))
                  (cong< reflˢ (cong (trans (coh _ _) (comreplace v)) reflˢ))) 
    comreplaceⁿ (coen n p) = ir (comreplaceⁿ n) 