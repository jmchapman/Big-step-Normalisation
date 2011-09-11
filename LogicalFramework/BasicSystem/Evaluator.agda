{-# OPTIONS --no-termination-check #-}

module BasicSystem.Evaluator where
open import BasicSystem.Syntax
open import BasicSystem.SyntacticLemmas
open import BasicSystem.Variables
open import BasicSystem.Value

mutual
  ev : forall {Γ Δ σ} -> Tm Δ σ -> (vs : Env Γ Δ) -> Val Γ (σ [ embˢ vs ]⁺)
  ev (coe t p)     vs        = coev (ev t (coevˢ vs reflˠ (symˠ(fog⁺ p)))) 
                                    (cong⁺ p (symˢ (cohvˢ vs _ _))) 
  ev (t [ ts ])    vs        = coev (ev t (evˢ ts vs)) 
                                    (trans⁺ (cong⁺ refl⁺ (symˢ (comevˢ ts vs)))
                                            (sym⁺ assoc⁺)) 
  ev top           (vs << v) = coev v (trans⁺ (cong⁺ refl⁺ (symˢ pop<)) 
                                              (sym⁺ assoc⁺)) 
  ev (λt t)        vs        = λv t vs 
  ev (app f)       (vs << v) = vapp (ev f vs) refl⁺ v  

  evˢ : forall {Γ Δ Σ} -> Sub Δ Σ -> Env Γ Δ -> Env Γ Σ
  evˢ (coeˢ ts p q) vs       = coevˢ (evˢ ts (coevˢ vs reflˠ (symˠ p))) reflˠ q
  evˢ (ts • us)     vs       = evˢ ts (evˢ us vs)
  evˢ id            vs       = vs
  evˢ (pop σ)      (vs << v) = vs 
  evˢ (ts < t)     vs        =
    evˢ ts vs << coev (ev t vs) (trans⁺ assoc⁺ (cong⁺ refl⁺ (comevˢ ts vs)))

  vapp : forall {Γ Γ' Δ σ τ ρ}{ts : Sub Γ Δ} -> Val Γ' ρ ->
         ρ ≡⁺ (Π σ τ [ ts ]⁺) ->
         (v : Val Γ (σ [ ts ]⁺)) -> Val Γ (τ [ ts < emb v ]⁺)
  vapp (λv t vs)    p a = 
    coev (ev t (vs << coev a (sym⁺ (dom (trans⁺ (sym⁺ Π[]) (trans⁺ p Π[])))))) 
         (inst (cod (trans⁺ (sym⁺ Π[]) (trans⁺ p Π[]))) (coh _ _))
  vapp (nev n)      p a = 
     nev (coen (app (coen (coen n p) Π[]) a) 
               (trans⁺ assoc⁺ (cong⁺ refl⁺ popid))) 
  vapp (coev v p)   q a = vapp v (trans⁺ p q) a  

  comev : forall {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ) ->
        t [ embˢ vs ] ≡ emb (ev t vs)
  comev (coe t p)     vs        = trans (trans (cong (coh _ _) (cohvˢ vs _ _)) 
                                               (comev t (coevˢ vs _ _))) 
                                        (sym (coh _ _)) 
  comev (t [ ts ])    vs        = trans (trans (trans assoc 
                                                    (cong refl (comevˢ ts vs)))
                                               (comev t (evˢ ts vs))) 
                                      (sym (coh _ _)) 
  comev top           (vs << v) = trans top< (sym (coh _ _))
  comev (λt t)        vs        = refl 
  comev (app f)       (vs << v) = 
    trans (trans (trans (trans (trans (cong refl (symˢ popid)) (sym assoc))
                               (cong (sym app[]) reflˢ))
                        (cong (congapp (trans (trans (trans (coh _ Π[]) 
                                                            (comev f vs))
                                                     (sym (coh _ refl⁺)))
                                       (sym (coh _ _))))
                              reflˢ))
                 (sym (coh _ _)))
          (comvapp (ev f vs) refl⁺ v)

  comevˢ : forall {Γ Δ Σ}(ts : Sub Δ Σ)(vs : Env Γ Δ) ->
         ts • embˢ vs ≡ˢ embˢ (evˢ ts vs)
  comevˢ (coeˢ ts p q) vs        = transˢ (transˢ (cong• (cohˢ ts _ _)
                                                       (cohvˢ vs _ _))
                                                (comevˢ ts _)) 
                                        (cohvˢ (evˢ ts _) _ _)  
  comevˢ (ts • us)     vs        = transˢ (transˢ assocˢ
                                                (cong• reflˢ (comevˢ us vs))) 
                                        (comevˢ ts (evˢ us vs)) 
  comevˢ id            vs        = leftid 
  comevˢ (pop σ)       (vs << v) = pop< 
  comevˢ (ts < t)      vs        = transˢ •< 
                                        (cong< (comevˢ ts vs)
                                               (ir (comev t vs))) 

  comvapp : forall {Γ Γ' Δ σ τ ρ}{ts : Sub Γ Δ}
         (f : Val Γ' ρ)(p : ρ ≡⁺ Π σ τ [ ts ]⁺) ->
         (v : Val Γ (σ [ ts ]⁺)) ->
         coe (emb f) p $ˢ emb v ≡ emb (vapp f p v)
  comvapp (λv t vs)  p a = 
    ir 
      (trans 
        (trans 
          (cong 
            (trans 
              (congapp 
                (trans 
                  (coh _ _) 
                  (trans (coh _ _) (trans (sym (coh _ Π[])) 
                (trans λ[] refl)))))
              (trans β (sym (coh _ (cod (trans⁺ (sym⁺ Π[]) (trans⁺ p Π[])))))))
            reflˢ)
          (trans 
            (cong 
              (coh _ _) 
              (cong< 
                (congid (symˠ (fog⁺ p)))
                (cong 
                  (sym 
                    (coh _ (dom (trans⁺ (sym⁺ Π[]) (trans⁺ (sym⁺ p) Π[]))))) 
                  (congid (symˠ(fog⁺ p))))))
            (trans assoc (cong refl (transˢ popid (cong< reflˢ (ir refl)))))))
        (comev t (vs << coev a _))) 
  comvapp (nev n)    p a = ir refl
  comvapp (coev v p) q a = trans (ir (cong (congapp (ir (ir (coh _ _)))) 
                                           reflˢ))
                                 (comvapp v (trans⁺ p q) a)

ev⁺ : forall {Γ Δ} -> Ty Δ -> Env Γ Δ -> VTy Γ
ev⁺ (coe⁺ σ p)  vs = ev⁺ σ (coevˢ vs reflˠ (symˠ p))
ev⁺ (σ [ ts ]⁺) vs = ev⁺ σ (evˢ ts vs)
ev⁺ U          vs = VU
ev⁺ (El σ)     vs = VEl (coev (ev σ vs) U[])
ev⁺ (Π σ τ)    vs = VΠ σ τ vs

comev⁺ : forall {Γ Δ}(σ : Ty Δ)(vs : Env Γ Δ) ->
         σ [ embˢ vs ]⁺ ≡⁺ emb⁺ (ev⁺ σ vs)
comev⁺ (coe⁺ σ p)  vs =
  trans⁺ (cong⁺ (coh⁺ _ _) (cohvˢ vs _ _))
        (comev⁺ σ (coevˢ vs reflˠ (symˠ p)))
comev⁺ (σ [ ts ]⁺) vs =
  trans⁺ assoc⁺ (trans⁺ (cong⁺ refl⁺ (comevˢ ts vs)) (comev⁺ σ (evˢ ts vs)))
comev⁺ U          vs = U[]
comev⁺ (El σ)     vs =
  trans⁺ El[]
         (congEl reflˠ (trans (coh _ _) 
                              (trans (comev σ vs) (sym (coh _ _)))))
comev⁺ (Π σ τ)    vs = refl⁺
