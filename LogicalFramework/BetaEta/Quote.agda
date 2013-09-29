
{-# OPTIONS --no-termination-check #-}

module BetaEta.Quote where
open import BetaEta.Syntax
open import BetaEta.SyntacticLemmas
open import BetaEta.Variables
open import BetaEta.Value
open import BetaEta.Evaluator
open import BetaEta.Weakening
open import BetaEta.IdentityEnvironment
open import BetaEta.Replace
open import BetaEta.Normal

mutual
  quot : forall {Γ} σ -> Val Γ (emb⁺ σ) -> Nf Γ (emb⁺ σ)
  quot (VΠ σ τ vs) f          = 
    ncoe (λn (quot _ (replace (vapp (wk (σ [ embˢ vs ]⁺) (coev f Π[])) refl⁺ (nev (var vZ)))))) (trans⁺ (congΠ refl⁺ (trans⁺ (sym⁺ (comev⁺ τ ((evˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid) << coev
     (coev
      (coev
       (coev
        (coev
         (coev
          (coev (nev (var vZ))
           (cong⁺ refl⁺
            (transˢ (symˢ leftid)
             (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
          (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
         (trans⁺ assoc⁺
          (cong⁺ refl⁺
           (comevˢ (pop (σ [ embˢ vs ]⁺))
            (wkˢ (σ [ embˢ vs ]⁺) vid <<
             coev (nev (var vZ))
             (cong⁺ refl⁺
              (transˢ (symˢ leftid)
               (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
        (cong⁺ (sym⁺ refl⁺)
         (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
          (symˠ reflˠ))))
       (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
      (cong⁺ assoc⁺
       (symˢ
        (cohvˢ
         (wkˢ (σ [ embˢ vs ]⁺) vid <<
          coev
          (coev
           (coev (nev (var vZ))
            (cong⁺ refl⁺
             (transˢ (symˢ leftid)
              (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
           (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
          (trans⁺ assoc⁺
           (cong⁺ refl⁺
            (comevˢ (pop (σ [ embˢ vs ]⁺))
             (wkˢ (σ [ embˢ vs ]⁺) vid <<
              coev (nev (var vZ))
              (cong⁺ refl⁺
               (transˢ (symˢ leftid)
                (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
         (cong, reflˠ refl⁺) (cong, (symˠ reflˠ) (sym⁺ refl⁺))))))
     (trans⁺ assoc⁺
      (cong⁺ refl⁺
       (comevˢ (embˢ vs • pop (σ [ embˢ vs ]⁺))
        (wkˢ (σ [ embˢ vs ]⁺) vid <<
         coev
         (coev
          (coev (nev (var vZ))
           (cong⁺ refl⁺
            (transˢ (symˢ leftid)
             (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
          (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
         (trans⁺ assoc⁺
           (cong⁺ refl⁺
           (comevˢ (pop (σ [ embˢ vs ]⁺))
            (wkˢ (σ [ embˢ vs ]⁺) vid <<
             coev (nev (var vZ))
             (cong⁺ refl⁺
              (transˢ (symˢ leftid)
               (transˢ (cong• comvid reflˢ)
                (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))))))))) (cong⁺ refl⁺ (cong< ((transˢ (symˢ (comevˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid)))) ((cong• reflˢ (transˢ (symˢ (comwkˢ (σ [ embˢ vs ]⁺) vid)) (transˢ (cong• (symˢ comvid) reflˢ) leftid))))) ((trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (sym (coh _ _)))))))))))))) (sym⁺ Π[]))
{-
         (trans⁺ (congΠ refl⁺ (trans⁺ (sym⁺ (comev⁺ τ (evˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid) <<
     coev
     (coev
      (coev
       (coev
        (coev
         (coev
          (coev (nev (var vZ))
           (cong⁺ refl⁺
            (transˢ (symˢ leftid)
             (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
          (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
         (trans⁺ assoc⁺ (cong⁺ refl⁺ pop<)))
        (cong⁺ (sym⁺ refl⁺)
         (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
          (symˠ reflˠ))))
       (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
      (cong⁺ assoc⁺
        (symˢ
        (cong<
         (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺) (symˠ reflˠ))
         (sym
          (coh
           (coe
            (coe
             (coe top
              (cong⁺ refl⁺
               (transˢ (symˢ leftid)
                (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
             (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
            (trans⁺ assoc⁺ (cong⁺ refl⁺ pop<)))
           (cong⁺ (sym⁺ refl⁺)
            (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
             (symˠ reflˠ)))))))))
     (trans⁺ assoc⁺
      (cong⁺ refl⁺
       (transˢ (transˢ assocˢ (cong• reflˢ pop<))
        (comevˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid)))))))) (cong⁺ refl⁺ (cong< (transˢ (symˢ (comevˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid))) (cong• reflˢ (transˢ (symˢ (comwkˢ (σ [ embˢ vs ]⁺) vid)) (transˢ (cong• (symˢ comvid) reflˢ) leftid)))) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (sym (coh _ _))))))))))))) (sym⁺ Π[])) 
-}
{-
    ncoe (λn (quot
                 _
                 (replace (vapp (wk (σ [ embˢ vs ]⁺) (coev f Π[])) refl⁺ (nev (var vZ))))))
         (trans⁺ (congΠ refl⁺ (trans⁺ (sym⁺ (comev⁺ τ  (evˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid) <<
    coev
    (coev
     (coev
      (coev
       (coev
        (coev
         (coev (nev (var vZ))
          (cong⁺ refl⁺
           (transˢ (symˢ leftid)
            (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
         (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
        (trans⁺ assoc⁺ (cong⁺ refl⁺ pop<)))
       (cong⁺ (sym⁺ refl⁺)
        (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
         (symˠ reflˠ))))
      (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
     (cong⁺ assoc⁺
      (symˢ
       (cong<
        (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺) (symˠ reflˠ))
        (sym
         (coh
          (coe
           (coe
            (coe top
             (cong⁺ refl⁺
              (transˢ (symˢ leftid)
               (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
            (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
           (trans⁺ assoc⁺ (cong⁺ refl⁺ pop<)))
          (cong⁺ (sym⁺ refl⁺)
           (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
            (symˠ reflˠ)))))))))
    (trans⁺ assoc⁺
     (cong⁺ refl⁺
      (transˢ (transˢ assocˢ (cong• reflˢ pop<))
       (comevˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid)))))))) (cong⁺ refl⁺ (cong< (transˢ (symˢ (comevˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid))) (cong• reflˢ (transˢ (transˢ (symˢ (comwkˢ (σ [ embˢ vs ]⁺) vid)) (cong• (symˢ comvid) reflˢ)) leftid))) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh _ _) (trans (coh top _) (sym (coh top assoc⁺))))))))))))) (sym⁺ Π[]))    
-}
  quot VU          (coev {σ = σ} v p) = 
    ncoe (quot (ev⁺ σ vid) (replace v)) 
         (trans⁺ (trans⁺ (sym⁺ (comev⁺ σ vid)) 
                         (trans⁺ (cong⁺ refl⁺ (symˢ comvid)) rightid⁺))
                 p) 
  quot VU          (nev n)    = neu (quotⁿ n) 
  quot (VEl σ)     (coev {σ = σ'} v p) = 
    ncoe (quot (ev⁺ σ' vid) (replace v))
         (trans⁺ (sym⁺ (comev⁺ σ' vid)) 
                 (trans⁺ (trans⁺ (cong⁺ refl⁺ (symˢ comvid)) rightid⁺)
                         p))  
  quot (VEl σ)     (nev n)    = neel (quotⁿ n) 

  quotⁿ : forall {Γ σ} -> NeV Γ σ -> NeN Γ σ
  quotⁿ (var x)    = nvar x 
  quotⁿ (app {σ = σ}{τ = τ} n v) = 
    ncoeⁿ (napp (quotⁿ n) 
                (ncoe (quot (ev⁺ σ vid) (replace v))
                      (trans⁺ (trans⁺ (sym⁺(comev⁺ σ vid))
                                      (cong⁺ refl⁺ 
                                             (transˢ (symˢ comvid) reflˢ)))
                              rightid⁺))) 
          (cong⁺ refl⁺
                 (cong< reflˢ
                        (cong (trans (coh _ _)
                                     (trans (comquot (ev⁺ σ vid) (replace v))
                                            (comreplace v)))
                              reflˢ)))
  quotⁿ (coen n p) = ncoeⁿ (quotⁿ n) p 

  abstract 
    comquot : forall {Γ}(σ : VTy Γ)(v : Val Γ (emb⁺ σ)) -> 
           nemb (quot σ v) ≡ emb v
    comquot (VΠ σ τ vs) f          = trans 
      (coh
        (λt
         (nemb
          (quot
           (ev⁺ τ
            (evˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid) <<
             coev
             (coev
              (coev
               (coev
                (coev
                 (coev
                  (coev (nev (var vZ))
                   (cong⁺ refl⁺
                    (transˢ (symˢ leftid)
                     (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                  (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                 (trans⁺ assoc⁺
                  (cong⁺ refl⁺
                   (comevˢ (pop (σ [ embˢ vs ]⁺))
                    (wkˢ (σ [ embˢ vs ]⁺) vid <<
                     coev (nev (var vZ))
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                (cong⁺ (sym⁺ refl⁺)
                 (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
                  (symˠ reflˠ))))
               (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
              (cong⁺ assoc⁺
               (symˢ
                (cohvˢ
                 (wkˢ (σ [ embˢ vs ]⁺) vid <<
                  coev
                  (coev
                   (coev (nev (var vZ))
                    (cong⁺ refl⁺
                     (transˢ (symˢ leftid)
                      (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                   (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                  (trans⁺ assoc⁺
                   (cong⁺ refl⁺
                    (comevˢ (pop (σ [ embˢ vs ]⁺))
                     (wkˢ (σ [ embˢ vs ]⁺) vid <<
                      coev (nev (var vZ))
                      (cong⁺ refl⁺
                       (transˢ (symˢ leftid)
                        (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                 (cong, reflˠ refl⁺) (cong, (symˠ reflˠ) (sym⁺ refl⁺))))))
             (trans⁺ assoc⁺
              (cong⁺ refl⁺
               (comevˢ (embˢ vs • pop (σ [ embˢ vs ]⁺))
                (wkˢ (σ [ embˢ vs ]⁺) vid <<
                 coev
                 (coev
                  (coev (nev (var vZ))
                   (cong⁺ refl⁺
                    (transˢ (symˢ leftid)
                     (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                  (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                 (trans⁺ assoc⁺
                  (cong⁺ refl⁺
                   (comevˢ (pop (σ [ embˢ vs ]⁺))
                    (wkˢ (σ [ embˢ vs ]⁺) vid <<
                     coev (nev (var vZ))
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ)
                        (comwkˢ (σ [ embˢ vs ]⁺) vid))))))))))))))
           (replace
            (vapp (wk (coe⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ)) f)
             (trans⁺ (cong⁺ Π[] (congpop (coh⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ))))
              refl⁺)
             (nev (var vZ)))))))
        
        (trans⁺
         (congΠ refl⁺
          (trans⁺
           (sym⁺
            (comev⁺ τ
             (evˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid) <<
              coev
              (coev
               (coev
                (coev
                 (coev
                  (coev
                   (coev (nev (var vZ))
                    (cong⁺ refl⁺
                     (transˢ (symˢ leftid)
                      (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                   (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                  (trans⁺ assoc⁺
                   (cong⁺ refl⁺
                    (comevˢ (pop (σ [ embˢ vs ]⁺))
                     (wkˢ (σ [ embˢ vs ]⁺) vid <<
                      coev (nev (var vZ))
                      (cong⁺ refl⁺
                       (transˢ (symˢ leftid)
                        (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                 (cong⁺ (sym⁺ refl⁺)
                  (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
                   (symˠ reflˠ))))
                (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
               (cong⁺ assoc⁺
                (symˢ
                 (cohvˢ
                  (wkˢ (σ [ embˢ vs ]⁺) vid <<
                   coev
                   (coev
                    (coev (nev (var vZ))
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans⁺ assoc⁺
                    (cong⁺ refl⁺
                     (comevˢ (pop (σ [ embˢ vs ]⁺))
                      (wkˢ (σ [ embˢ vs ]⁺) vid <<
                       coev (nev (var vZ))
                       (cong⁺ refl⁺
                        (transˢ (symˢ leftid)
                         (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                  (cong, reflˠ refl⁺) (cong, (symˠ reflˠ) (sym⁺ refl⁺))))))
              (trans⁺ assoc⁺
               (cong⁺ refl⁺
                (comevˢ (embˢ vs • pop (σ [ embˢ vs ]⁺))
                 (wkˢ (σ [ embˢ vs ]⁺) vid <<
                  coev
                  (coev
                   (coev (nev (var vZ))
                    (cong⁺ refl⁺
                     (transˢ (symˢ leftid)
                      (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                   (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                  (trans⁺ assoc⁺
                   (cong⁺ refl⁺
                    (comevˢ (pop (σ [ embˢ vs ]⁺))
                     (wkˢ (σ [ embˢ vs ]⁺) vid <<
                      coev (nev (var vZ))
                      (cong⁺ refl⁺
                       (transˢ (symˢ leftid)
                        (transˢ (cong• comvid reflˢ)
                         (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))))))))
           (cong⁺ refl⁺
            (cong<
             (transˢ (symˢ (comevˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid)))
              (cong• reflˢ
               (transˢ (symˢ (comwkˢ (σ [ embˢ vs ]⁺) vid))
                (transˢ (cong• (symˢ comvid) reflˢ) leftid))))
             (trans
              (coh
               (coe
                (coe
                 (coe
                  (coe
                   (coe
                    (coe top
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans⁺ assoc⁺
                    (cong⁺ refl⁺
                     (comevˢ (pop (σ [ embˢ vs ]⁺))
                      (wkˢ (σ [ embˢ vs ]⁺) vid <<
                       coev (nev (var vZ))
                       (cong⁺ refl⁺
                        (transˢ (symˢ leftid)
                         (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                  (cong⁺ (sym⁺ refl⁺)
                   (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
                    (symˠ reflˠ))))
                 (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                (cong⁺ assoc⁺
                 (symˢ
                  (cohvˢ
                   (wkˢ (σ [ embˢ vs ]⁺) vid <<
                    coev
                    (coev
                     (coev (nev (var vZ))
                      (cong⁺ refl⁺
                       (transˢ (symˢ leftid)
                        (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                     (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                    (trans⁺ assoc⁺
                     (cong⁺ refl⁺
                      (comevˢ (pop (σ [ embˢ vs ]⁺))
                       (wkˢ (σ [ embˢ vs ]⁺) vid <<
                        coev (nev (var vZ))
                        (cong⁺ refl⁺
                         (transˢ (symˢ leftid)
                          (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                   (cong, reflˠ refl⁺) (cong, (symˠ reflˠ) (sym⁺ refl⁺))))))
               (trans⁺ assoc⁺
                (cong⁺ refl⁺
                 (comevˢ (embˢ vs • pop (σ [ embˢ vs ]⁺))
                  (wkˢ (σ [ embˢ vs ]⁺) vid <<
                   coev
                   (coev
                    (coev (nev (var vZ))
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans⁺ assoc⁺
                    (cong⁺ refl⁺
                     (comevˢ (pop (σ [ embˢ vs ]⁺))
                      (wkˢ (σ [ embˢ vs ]⁺) vid <<
                       coev (nev (var vZ))
                       (cong⁺ refl⁺
                        (transˢ (symˢ leftid)
                         (transˢ (cong• comvid reflˢ)
                          (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))))))
              (trans
               (coh
                (coe
                 (coe
                  (coe
                   (coe
                    (coe top
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans⁺ assoc⁺
                    (cong⁺ refl⁺
                     (comevˢ (pop (σ [ embˢ vs ]⁺))
                      (wkˢ (σ [ embˢ vs ]⁺) vid <<
                       coev (nev (var vZ))
                       (cong⁺ refl⁺
                        (transˢ (symˢ leftid)
                         (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                  (cong⁺ (sym⁺ refl⁺)
                   (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
                    (symˠ reflˠ))))
                 (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                (cong⁺ assoc⁺
                 (symˢ
                  (cohvˢ
                   (wkˢ (σ [ embˢ vs ]⁺) vid <<
                    coev
                    (coev
                     (coev (nev (var vZ))
                      (cong⁺ refl⁺
                       (transˢ (symˢ leftid)
                        (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                     (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                    (trans⁺ assoc⁺
                     (cong⁺ refl⁺
                      (comevˢ (pop (σ [ embˢ vs ]⁺))
                       (wkˢ (σ [ embˢ vs ]⁺) vid <<
                        coev (nev (var vZ))
                        (cong⁺ refl⁺
                         (transˢ (symˢ leftid)
                          (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                   (cong, reflˠ refl⁺) (cong, (symˠ reflˠ) (sym⁺ refl⁺))))))
               (trans
                (coh
                 (coe
                  (coe
                   (coe
                    (coe top
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans⁺ assoc⁺
                    (cong⁺ refl⁺
                     (comevˢ (pop (σ [ embˢ vs ]⁺))
                      (wkˢ (σ [ embˢ vs ]⁺) vid <<
                       coev (nev (var vZ))
                       (cong⁺ refl⁺
                        (transˢ (symˢ leftid)
                         (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                  (cong⁺ (sym⁺ refl⁺)
                   (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
                    (symˠ reflˠ))))
                 (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                (trans
                 (coh
                  (coe
                   (coe
                    (coe top
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans⁺ assoc⁺
                    (cong⁺ refl⁺
                     (comevˢ (pop (σ [ embˢ vs ]⁺))
                      (wkˢ (σ [ embˢ vs ]⁺) vid <<
                       coev (nev (var vZ))
                       (cong⁺ refl⁺
                        (transˢ (symˢ leftid)
                         (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                  (cong⁺ (sym⁺ refl⁺)
                   (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
                    (symˠ reflˠ))))
                 (trans
                  (coh
                   (coe
                    (coe top
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans⁺ assoc⁺
                    (cong⁺ refl⁺
                     (comevˢ (pop (σ [ embˢ vs ]⁺))
                      (wkˢ (σ [ embˢ vs ]⁺) vid <<
                       coev (nev (var vZ))
                       (cong⁺ refl⁺
                        (transˢ (symˢ leftid)
                         (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                  (trans
                   (coh
                    (coe top
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                   (trans
                    (coh top
                     (cong⁺ refl⁺
                      (transˢ (symˢ leftid)
                       (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                    (sym (coh top assoc⁺)))))))))))))
         (sym⁺ Π[])))
      (trans (trans (congλ refl⁺ (trans
                                    (comquot
                                     (ev⁺ τ
                                      (evˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid) <<
                                       coev
                                       (coev
                                        (coev
                                         (coev
                                          (coev
                                           (coev
                                            (coev (nev (var vZ))
                                             (cong⁺ refl⁺
                                              (transˢ (symˢ leftid)
                                               (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                                            (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                                           (trans⁺ assoc⁺
                                            (cong⁺ refl⁺
                                             (comevˢ (pop (σ [ embˢ vs ]⁺))
                                              (wkˢ (σ [ embˢ vs ]⁺) vid <<
                                               coev (nev (var vZ))
                                               (cong⁺ refl⁺
                                                (transˢ (symˢ leftid)
                                                 (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                                          (cong⁺ (sym⁺ refl⁺)
                                           (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
                                            (symˠ reflˠ))))
                                         (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                                        (cong⁺ assoc⁺
                                         (symˢ
                                          (cohvˢ
                                           (wkˢ (σ [ embˢ vs ]⁺) vid <<
                                            coev
                                            (coev
                                             (coev (nev (var vZ))
                                              (cong⁺ refl⁺
                                               (transˢ (symˢ leftid)
                                                (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                                             (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                                            (trans⁺ assoc⁺
                                             (cong⁺ refl⁺
                                              (comevˢ (pop (σ [ embˢ vs ]⁺))
                                               (wkˢ (σ [ embˢ vs ]⁺) vid <<
                                                coev (nev (var vZ))
                                                (cong⁺ refl⁺
                                                 (transˢ (symˢ leftid)
                                                  (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
                                           (cong, reflˠ refl⁺) (cong, (symˠ reflˠ) (sym⁺ refl⁺))))))
                                       (trans⁺ assoc⁺
                                        (cong⁺ refl⁺
                                         (comevˢ (embˢ vs • pop (σ [ embˢ vs ]⁺))
                                          (wkˢ (σ [ embˢ vs ]⁺) vid <<
                                           coev
                                           (coev
                                            (coev (nev (var vZ))
                                             (cong⁺ refl⁺
                                              (transˢ (symˢ leftid)
                                               (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
                                            (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
                                           (trans⁺ assoc⁺
                                            (cong⁺ refl⁺
                                             (comevˢ (pop (σ [ embˢ vs ]⁺))
                                              (wkˢ (σ [ embˢ vs ]⁺) vid <<
                                               coev (nev (var vZ))
                                               (cong⁺ refl⁺
                                                (transˢ (symˢ leftid)
                                                 (transˢ (cong• comvid reflˢ)
                                                  (comwkˢ (σ [ embˢ vs ]⁺) vid))))))))))))))
                                     (replace
                                      (vapp (wk (coe⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ)) f)
                                       (trans⁺ (cong⁺ Π[] (congpop (coh⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ))))
                                        refl⁺)
                                       (nev (var vZ)))))
                                    {!!})) η) (coh (emb f) Π[]))
    
{-
nemb
(quot
 (ev⁺ τ
  (evˢ (embˢ vs) (wkˢ (σ [ embˢ vs ]⁺) vid) <<
   coev
   (coev
    (coev
     (coev
      (coev
       (coev
        (coev (nev (var vZ))
         (cong⁺ refl⁺
          (transˢ (symˢ leftid)
           (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
        (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
       (trans⁺ assoc⁺
        (cong⁺ refl⁺
         (comevˢ (pop (σ [ embˢ vs ]⁺))
          (wkˢ (σ [ embˢ vs ]⁺) vid <<
           coev (nev (var vZ))
           (cong⁺ refl⁺
            (transˢ (symˢ leftid)
             (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
      (cong⁺ (sym⁺ refl⁺)
       (cohvˢ (wkˢ (σ [ embˢ vs ]⁺) vid) (cong, reflˠ refl⁺)
        (symˠ reflˠ))))
     (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
    (cong⁺ assoc⁺
     (symˢ
      (cohvˢ
       (wkˢ (σ [ embˢ vs ]⁺) vid <<
        coev
        (coev
         (coev (nev (var vZ))
          (cong⁺ refl⁺
           (transˢ (symˢ leftid)
            (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
         (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
        (trans⁺ assoc⁺
         (cong⁺ refl⁺
          (comevˢ (pop (σ [ embˢ vs ]⁺))
           (wkˢ (σ [ embˢ vs ]⁺) vid <<
            coev (nev (var vZ))
            (cong⁺ refl⁺
             (transˢ (symˢ leftid)
              (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))))))
       (cong, reflˠ refl⁺) (cong, (symˠ reflˠ) (sym⁺ refl⁺))))))
   (trans⁺ assoc⁺
    (cong⁺ refl⁺
     (comevˢ (embˢ vs • pop (σ [ embˢ vs ]⁺))
      (wkˢ (σ [ embˢ vs ]⁺) vid <<
       coev
       (coev
        (coev (nev (var vZ))
         (cong⁺ refl⁺
          (transˢ (symˢ leftid)
           (transˢ (cong• comvid reflˢ) (comwkˢ (σ [ embˢ vs ]⁺) vid)))))
        (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) (sym⁺ assoc⁺)))
       (trans⁺ assoc⁺
        (cong⁺ refl⁺
         (comevˢ (pop (σ [ embˢ vs ]⁺))
          (wkˢ (σ [ embˢ vs ]⁺) vid <<
           coev (nev (var vZ))
           (cong⁺ refl⁺
            (transˢ (symˢ leftid)
             (transˢ (cong• comvid reflˢ)
              (comwkˢ (σ [ embˢ vs ]⁺) vid))))))))))))))
 (replace
  (vapp (wk (coe⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ)) f)
   (trans⁺ (cong⁺ Π[] (congpop (coh⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ))))
    refl⁺)
   (nev (var vZ)))))

-}



{- 
    trans (coh _ _) 
          (trans (trans (congλ refl⁺
                               (trans (comquot (ev⁺ τ ((evˢ (embˢ vs) (evˢ (pop (σ [ embˢ vs ]⁺)) (evˢ (pop (σ [ embˢ vs ]⁺) < emb (nev (var vZ))) vid))) << {!coev (nev (var vZ)) ?!})) {!!}) (trans (comreplace (vapp (wk (coe⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ)) f)
                                                                              (trans⁺ (cong⁺ Π[] (congpop (coh⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ))))
                                                                                      refl⁺)
                                                                              (nev (var vZ)))) 
                                                            (trans (sym (comvapp  (wk (coe⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ)) f)
                                                                                            (trans⁺ (cong⁺ Π[] (congpop (coh⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ))))
                                                                                                    refl⁺)
                                                                                             (nev (var vZ)))) 
                                                                    (trans (coh _ _) (trans (trans (cong (congapp (trans (trans (coh _ _) (trans (coh _ _) (trans (sym (comwk (coe⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ)) f)) (cong (sym (coh (emb f) Π[])) (congpop (coh⁺ (σ [ embˢ vs ]⁺) (symˠ reflˠ))))))) (sym (coh (emb (coev f Π[]) [ pop (σ [ embˢ vs ]⁺) ]) Π[])))) reflˢ) (trans (cong app[] reflˢ) (trans assoc (cong refl (transˢ popid poptop))))) rightid))))))
                        η)
                 (coh _ Π[])) -}
    comquot VU          (coev {σ = σ} v p) = 
      ir (trans (comquot (ev⁺ σ vid) (replace v) ) (comreplace v)) 
    comquot VU          (nev n)    = comquotⁿ n 
    comquot (VEl σ)     (coev {σ = σ'} v p) = 
      ir (trans (comquot (ev⁺ σ' vid) (replace v)) (comreplace v) ) 
    comquot (VEl σ)     (nev n)    = comquotⁿ n 

    comquotⁿ : forall {Γ σ}(n : NeV Γ σ) -> 
             nembⁿ (quotⁿ n) ≡ embⁿ n
    comquotⁿ (var x)    = refl 
    comquotⁿ (app {σ = σ} n v)  = 
      trans (coh _ _) 
            (cong (congapp (comquotⁿ n)) 
                  (cong< reflˢ 
                         (cong (trans (coh _ _) 
                                      (trans (comquot (ev⁺ σ vid) (replace v))
                                             (comreplace v)))
                               reflˢ))) 
    comquotⁿ (coen n p) = ir (comquotⁿ n) 
