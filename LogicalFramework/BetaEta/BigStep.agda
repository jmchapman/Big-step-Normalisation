module BetaEta.BigStep where
open import BetaEta.Syntax
open import BetaEta.SyntacticLemmas
open import BetaEta.Variables
open import BetaEta.Value

mutual
  data ev_&_⇓_ : forall {Γ Δ σ} -> Tm Δ σ -> (vs : Env Γ Δ) -> 
                 Val Γ (σ [ embˢ vs ]⁺) -> Set where
    evcoe : forall {Γ Δ  Δ'}{σ : Ty Δ}{σ'}{t : Tm Δ' σ'}{p : σ' ≡⁺ σ}
            {vs : Env Γ Δ}{v : Val Γ _} -> 
            ev t & coevˢ vs reflˠ (symˠ (fog⁺ p)) ⇓ v ->
            ev coe t p & vs ⇓ coev v (cong⁺ p (symˢ (cohvˢ vs reflˠ _)))
    ev[] : forall {B Γ Δ σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{vs : Env B Γ}
           {vs' : Env B Δ}(p : evˢ ts & vs ⇓ vs') -> 
           {v : Val B _} -> ev t & vs' ⇓ v -> 
           ev t [ ts ] & vs ⇓ coev v (trans⁺ (cong⁺ refl⁺
                                                    (symˢ (comevˢ ts vs p)))
                                             (sym⁺ assoc⁺))
    evtop : forall {Γ Δ σ}{vs : Env Γ Δ}{v : Val Γ (σ [ embˢ vs ]⁺)} ->
            ev top & vs << v ⇓ coev v (trans⁺ (cong⁺ refl⁺ (symˢ pop<))
                                              (sym⁺ assoc⁺))
    evλ : forall {Γ Δ σ τ}{t : Tm (Δ , σ) τ}{vs : Env Γ Δ} ->
          ev λt t & vs ⇓ λv t vs
    evapp : forall {Γ Δ σ τ}{t : Tm Δ (Π σ τ)}{vs : Env Γ Δ}
            {v : Val Γ _}{v' : Val Γ _} -> ev t & vs ⇓ v' -> 
            {v'' : Val Γ _} -> (vapp v' & refl⁺ & v ⇓ v'') -> 
            ev app t & vs << v ⇓ v'' 

  data evˢ_&_⇓ : forall {Γ Δ Σ} -> Sub Δ Σ -> Env Γ Δ -> Env Γ Σ -> Set where
    evˢcoeˢ : forall {Γ Δ Δ' Σ Σ'}{ts : Sub Δ' Σ'}{p : Δ' ≡ˠ Δ}{q : Σ' ≡ˠ Σ}
              {vs : Env Γ Δ}{vs' : Env Γ Σ'} -> 
              evˢ ts & coevˢ vs reflˠ (symˠ p) ⇓ vs' ->
              evˢ coeˢ ts p q & vs ⇓ (coevˢ vs' reflˠ q)
    evˢ• : forall {B Γ Δ Σ}{ts : Sub Δ Σ}{us : Sub Γ Δ}{vs : Env B Γ}
           {vs' : Env B Δ} -> evˢ us & vs ⇓ vs' ->
           {vs'' : Env B Σ} -> evˢ ts & vs' ⇓ vs'' ->
           evˢ ts • us & vs ⇓ vs''
    evˢid : forall {Γ Δ}{vs : Env Γ Δ} -> evˢ id & vs ⇓ vs           
    evˢpop : forall {Γ Δ}{σ : Ty Δ}{vs : Env Γ Δ}
             {v : Val Γ (σ [ embˢ vs ]⁺)} -> 
             evˢ (pop σ) & (vs << v) ⇓ vs
    evˢ< : forall {B Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)}{vs : Env B Γ}
           {vs' : Env B Δ}(p : evˢ ts & vs ⇓ vs') ->
           {v : Val B _} -> ev t & vs ⇓ v ->
           evˢ ts < t & vs ⇓ (vs' << coev v 
                                          (trans⁺ assoc⁺
                                                  (cong⁺ refl⁺
                                                         (comevˢ _ _ p))))

  data vapp_&_&_⇓_ : forall {Γ Γ' Δ σ τ ρ}{ts : Sub Γ Δ}(v : Val Γ' ρ) ->
                     ρ ≡⁺ Π σ τ [ ts ]⁺ -> (v' : Val Γ (σ [ ts ]⁺)) ->
                     (v'' : Val Γ (τ [ ts < emb v' ]⁺)) -> Set where
    vappλv : forall {Γ Γ' Δ Δ' σ τ σ' τ'}{ts : Sub Γ' Δ'}{t : Tm (Δ , σ) τ}
             {vs : Env Γ Δ}{p : Π σ τ [ embˢ vs ]⁺ ≡⁺ Π σ' τ' [ ts ]⁺}
             {a : Val Γ' (σ' [ ts ]⁺)} -> 
             {v : Val Γ _} -> 
             (ev t & vs << coev a (dom (trans⁺ (sym⁺ Π[])
                                               (trans⁺ (sym⁺ p) Π[])))
                   ⇓ v) -> 
             vapp λv t vs & p & a ⇓ coev v (inst (cod (trans⁺ (sym⁺ Π[]) 
                                                              (trans⁺ p Π[]))) 
                                                 (coh _ _)) 
    vappnev : forall {Γ Γ' Δ σ τ ρ}{ts : Sub Γ Δ}{n : NeV Γ' ρ}
              {p : ρ ≡⁺ Π σ τ [ ts ]⁺}{a : Val Γ (σ [ ts ]⁺)} ->
              vapp nev n & p & a ⇓ nev (coen (app (coen (coen n p) Π[]) a)
                                             (trans⁺ assoc⁺
                                                     (cong⁺ refl⁺ popid)))
    vappcoev : forall {Γ Γ' Γ'' Δ σ τ}{ρ : Ty Γ'}{ρ'}{ts : Sub Γ Δ}
               {v : Val Γ'' ρ'}{p : ρ' ≡⁺ ρ}{q : ρ ≡⁺ Π σ τ [ ts ]⁺}
               {a : Val Γ (σ [ ts ]⁺)} -> 
               {v' : Val Γ _} -> vapp v & trans⁺ p q & a ⇓ v' ->
               vapp coev v p & q & a ⇓ v'

  comev : forall {Γ Δ σ} t (vs : Env Γ Δ){v : Val Γ (σ [ embˢ vs ]⁺)} -> 
          ev t & vs ⇓ v -> t [ embˢ vs ] ≡ emb v
  comev (coe t p) vs (evcoe p') = 
          trans (cong (coh _ _) (cohvˢ vs reflˠ _))
                (trans (comev t _ p') (sym (coh _ _)))
  comev (t [ ts ]) vs (ev[] p q) =
    trans assoc 
          (trans (trans (cong refl (comevˢ ts vs p)) (comev t _ q)) 
                 (sym (coh _ _))) 
  comev top (vs << v) evtop = trans top< (sym (coh _ _)) 
  comev (λt t) _ evλ = refl 
  comev (app f) (vs << v) (evapp p q) = 
    trans (trans ((trans (trans (trans (cong refl (symˢ popid)) (sym assoc))
                               (cong (sym app[]) reflˢ))
                        (cong (congapp (trans (trans (trans (coh _ Π[])
                                                            (comev f vs p))
                                                     (sym (coh _ _)))
                                       (sym (coh _ _))))
                              reflˢ)) )
                 (sym (coh _ _)))
          (comvapp _ _ _ q)

  comevˢ : forall {Γ Δ Σ}(ts : Sub Δ Σ)(vs : Env Γ Δ){vs' : Env Γ Σ} ->
           evˢ ts & vs ⇓ vs' -> ts • embˢ vs ≡ˢ embˢ vs'
  comevˢ .(coeˢ _ p q) vs (evˢcoeˢ {ts = ts}{p = p}{q = q}{vs' = vs'} p') = 
    transˢ (transˢ (cong• (cohˢ _ p q) (cohvˢ vs reflˠ (symˠ p))) 
                   (comevˢ ts (coevˢ vs reflˠ (symˠ p)) p'))
           (cohvˢ vs' reflˠ q) 
  comevˢ .(_ • _) _ (evˢ• p q) = 
    transˢ (transˢ assocˢ (cong• reflˢ (comevˢ _ _ p))) (comevˢ _ _ q)
  comevˢ .id ._ evˢid = leftid 
  comevˢ .(pop _) .(_ << _) evˢpop = pop<
  comevˢ .(_ < _) _ (evˢ< p q) = 
    transˢ •< (cong< (comevˢ _ _ p) (ir (comev _ _ q)))

  comvapp : forall {Γ Γ' Δ σ τ ρ}{ts : Sub Γ Δ}
         (f : Val Γ' ρ)(p : ρ ≡⁺ Π σ τ [ ts ]⁺) ->
         (v : Val Γ (σ [ ts ]⁺)){v' : Val Γ _} ->
         vapp f & p & v ⇓ v' ->
         coe (emb f) p $ˢ emb v ≡ emb v'
  comvapp .(λv t vs) p a (vappλv {t = t}{vs = vs} y) =  ir 
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
        (comev _ _ y))

  comvapp .(nev n) p a (vappnev {n = n}) = ir refl
  comvapp .(coev v p') p a (vappcoev {v = v} {p = p'} y) = trans (ir (cong (congapp (ir (ir (coh _ _))))
                    reflˢ)) 
          (comvapp _ _ _ y)

data ev⁺_&_⇓_ : forall {Γ Δ} -> Ty Δ -> Env Γ Δ -> VTy Γ -> Set where
  ev⁺coe⁺ : forall {Γ Δ Δ'}{σ : Ty Δ'}{p : Δ' ≡ˠ Δ}{vs : Env Γ Δ}
            {σ' : VTy Γ} -> ev⁺ σ & coevˢ vs reflˠ (symˠ p) ⇓ σ' ->
            ev⁺ coe⁺ σ p & vs ⇓ σ'
  ev⁺[] : forall {B Γ Δ}{σ : Ty Δ}{ts : Sub Γ Δ}{vs : Env B Γ}
          {vs' : Env B Δ} -> evˢ ts & vs ⇓ vs' ->
          {σ' : VTy B} -> ev⁺ σ & vs' ⇓ σ' -> ev⁺ σ [ ts ]⁺ & vs ⇓ σ'
  ev⁺U : forall {Γ Δ}{vs : Env Γ Δ} -> ev⁺ U & vs ⇓ VU
  ev⁺El : forall {Γ Δ}{σ : Tm Δ U}{vs : Env Γ Δ}
          {σ' : Val Γ (U [ embˢ vs ]⁺)} -> ev σ & vs ⇓ σ' -> 
          ev⁺ El σ & vs ⇓ VEl (coev σ' U[])
          
  ev⁺Π : forall {Γ Δ σ τ}{vs : Env Γ Δ} -> ev⁺ Π σ τ & vs ⇓ VΠ σ τ vs

comev⁺ : forall {Γ Δ}{σ : Ty Δ}{vs : Env Γ Δ}{σ' : VTy Γ} -> ev⁺ σ & vs ⇓ σ' ->
         σ [ embˢ vs ]⁺ ≡⁺ emb⁺ σ'
comev⁺ {vs = vs}(ev⁺coe⁺ {p = p'} p) = 
  trans⁺ (cong⁺ (coh⁺ _ p') (cohvˢ vs reflˠ (symˠ p'))) (comev⁺ p) 
comev⁺ (ev⁺[] p q) = 
  trans⁺ assoc⁺ (trans⁺ (cong⁺ refl⁺ (comevˢ _ _ p)) (comev⁺ q))
comev⁺ ev⁺U = U[]
comev⁺ (ev⁺El p) = trans⁺ El[] (congEl reflˠ (ir (comev _ _ p))) 
comev⁺ ev⁺Π = refl⁺
