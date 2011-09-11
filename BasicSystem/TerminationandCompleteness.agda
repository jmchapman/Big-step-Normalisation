module BasicSystem.TerminationandCompleteness where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPEBigStep
open import BasicSystem.OPELemmas
open import BasicSystem.Embeddings
open import BasicSystem.Conversion
open import BasicSystem.BigStepSemantics
open import BasicSystem.StrongComputability
open import BasicSystem.IdentityEnvironment

mutual
  fundthrm : forall {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ) -> SCE vs ->
             Σ (Val Γ σ) 
               \v -> eval t & vs ⇓ v ∧ SCV v ∧ (t [ embˢ vs ] ≃ emb v)
  fundthrm top        (vs << v) (s<< svs sv) = sig v (tr rvar sv  top<) 
  fundthrm (t [ ts ]) vs svs = 
     sig (σ₁ sw) 
         (tr (rsubs (t1 (σ₂ sws)) (t1 (σ₂ sw))) 
             (t2 (σ₂ sw)) 
             (trans (trans [][] (cong[] refl (t3 (σ₂ sws)))) (t3 (σ₂ sw)))) 
     where
     sws = fundthrmˢ ts vs svs
     sw  = fundthrm t (σ₁ sws) (t2 (σ₂ sws))
  fundthrm (λt t)      vs svs = 
    sig (λv t vs) 
        (tr rlam 
            (\{_} f a sa -> 
              let st = fundthrm t (emap f vs << a) (s<< (scemap f vs svs) sa) 
              in  sig (σ₁ st) 
                      (tr (r$lam (t1 (σ₂ st)))
                          (t2 (σ₂ st)) 
                          (trans 
                            (trans 
                              (cong$ λ[] refl)
                              (trans 
                                β 
                                (trans 
                                  [][] 
                                  (cong[] 
                                    refl 
                                    (transˢ 
                                      comp< 
                                        (cong< 
                                          (transˢ 
                                            assoc 
                                            (transˢ 
                                              (cong○ reflˢ popcomp) 
                                              rightidˢ)) 
                                          top<)))))) 
                                  (t3 (σ₂ st)))))
            refl)  
  fundthrm (t $ u)    vs svs = 
    sig (σ₁ stu) 
        (tr (rapp (t1 (σ₂ st)) 
                  (t1 (σ₂ su)) 
                  (helper' (sym⁼ (oidvmap (σ₁ st))) (t1 (σ₂ stu)))) 
            (t2 (σ₂ stu)) 
            (trans (trans $[] ((cong$ (t3 (σ₂ st)) (t3 (σ₂ su))))) (helper'' (sym⁼ (oidvmap (σ₁ st))) {(σ₁ (fundthrm u vs svs))}{σ₁ (t2 (σ₂ (fundthrm t vs svs)) oid (σ₁ (fundthrm u vs svs)) (t2 (σ₂ (fundthrm u vs svs))))} (t3 (σ₂ stu)))))
    where
    st  = fundthrm t vs svs
    su  = fundthrm u vs svs
    stu = t2 (σ₂ st) oid (σ₁ su) (t2 (σ₂ su))

  fundthrmˢ : forall {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ) -> SCE vs ->
              Σ (Env B Δ) 
                \ws -> 
                  evalˢ ts & vs ⇓ ws ∧ SCE ws ∧ (ts ○ (embˢ vs) ≃ˢ embˢ ws)
  fundthrmˢ (pop σ)   (vs << v) (s<< svs sv) = sig vs (tr rˢpop svs popcomp) 
  fundthrmˢ (ts < t)  vs        svs          = 
    sig (σ₁ sts << σ₁ st) 
        (tr (rˢcons (t1 (σ₂ sts)) (t1 (σ₂ st))) 
            (s<< (t2 (σ₂ sts)) (t2 (σ₂ st))) 
            (transˢ comp< (cong< (t3 (σ₂ sts)) (t3 (σ₂ st))))) 
    where
    sts = fundthrmˢ ts vs svs
    st  = fundthrm  t  vs svs
  fundthrmˢ id        vs        svs          = sig vs (tr rˢid svs leftidˢ) 
  fundthrmˢ (ts ○ us) vs        svs          = 
    sig (σ₁ sts) 
        (tr (rˢcomp (t1 (σ₂ sus)) (t1 (σ₂ sts))) 
            (t2 (σ₂ sts)) 
            (transˢ (transˢ assoc (cong○ reflˢ (t3 (σ₂ sus)))) (t3 (σ₂ sts)))) 
    where
    sus = fundthrmˢ us vs svs
    sts = fundthrmˢ ts (σ₁ sus) (t2 (σ₂ sus))

mutual
  quotlema : forall {Γ} σ {v : Val Γ σ} -> 
              SCV v -> Σ (Nf Γ σ) (\m ->  quot v ⇓ m × (emb v ≃ nemb m ))
  quotlema ι {nev n} (sig m (pr p q)) = sig (ne m) (pr (qbase p) q)
  quotlema {Γ} (σ ⇒ τ) {v} sv =
    sig (λn (σ₁ qvvZ)) 
        (pr (qarr (t1 (σ₂ svvZ)) (π₁ (σ₂ qvvZ))) 
            (trans 
              η 
              (congλ 
                (trans 
                  (cong$ 
                    (trans
                      (trans (cong[] (trans (sym []id) (cong[] refl lemoid)) 
                                     reflˢ ) 
                             [][]) 
                      (sym (ovemb (skip σ oid) v))) 
                    refl) 
                  (trans (t3 (σ₂ svvZ)) (π₂ (σ₂ qvvZ)))))))
    where
    svZ = quotlemb σ {varV (vZ {Γ})} qⁿvar refl
    svvZ = sv (skip σ oid) (nev (varV vZ)) svZ
    qvvZ = quotlema τ (t2 (σ₂ svvZ))

  quotlemb : forall {Γ} σ {n : NeV Γ σ}{m : NeN Γ σ} -> 
              quotⁿ n ⇓ m -> embⁿ n ≃ nembⁿ m -> SCV (nev n)
  quotlemb ι       {n} p q = sig _ (pr p q) 
  quotlemb (σ ⇒ τ) {n}{m} p q = \f a sa -> 
    let qla = quotlema σ sa
    in  sig (nev (appV (nevmap f n) a)) 
            (tr r$ne 
                (quotlemb τ 
                           (qⁿapp (quotⁿ⇓map f p) (π₁ (σ₂ qla))) 
                           (cong$ (trans (onevemb f n) 
                                         (trans (cong[] q reflˢ) 
                                                (sym (onenemb f m)))) 
                                  (π₂ (σ₂ qla)))) 
                (cong$ (trans (onevemb f n) (sym (onevemb f n))) refl))


scvar : forall {Γ σ}(x : Var Γ σ) -> SCV (nev (varV x))
scvar x = quotlemb _ qⁿvar refl 

scid : forall Γ -> SCE (vid {Γ})
scid ε       = sε 
scid (Γ < σ) = s<< (scemap (weak σ) _ (scid Γ)) (scvar vZ) 

normthrm : forall {Γ σ}(t : Tm Γ σ) -> Σ (Nf Γ σ) \n -> nf t ⇓ n × (t ≃ nemb n)
normthrm t = sig (σ₁ qt) (pr (norm⇓ (t1 (σ₂ ft)) (π₁ (σ₂ qt))) 
                         (trans (trans (trans (sym []id) (cong[] refl embvid))
                                       (t3 (σ₂ ft))) 
                                (π₂ (σ₂ qt))))  
  where
  ft = fundthrm t vid (scid _)
  qt = quotlema _ (t2 (σ₂ ft))