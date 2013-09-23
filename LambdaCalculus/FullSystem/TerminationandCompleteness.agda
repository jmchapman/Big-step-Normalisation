module FullSystem.TerminationandCompleteness where
open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.OPE
open import FullSystem.OPEBigStep
open import FullSystem.OPELemmas
open import FullSystem.Embeddings
open import FullSystem.Conversion
open import FullSystem.BigStepSemantics
open import FullSystem.StrongComputability
open import FullSystem.IdentityEnvironment

mutual
  quotelema : forall {Γ} σ {v : Val Γ σ} -> 
              SCV v -> Σ (Nf Γ σ) (\m ->  quot v ⇓ m ∧ (emb v ≃ nemb m ))
  quotelema ι {nev n} (sig m (pr p q)) = sig (neι m) (pr (qbase p) q)
  quotelema {Γ} (σ ⇒ τ) {v} sv =
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
    svZ = quotelemb σ {varV (vZ {Γ})} qⁿvar refl
    svvZ = sv (skip σ oid) (nev (varV vZ)) svZ
    qvvZ = quotelema τ (t2 (σ₂ svvZ))
  quotelema N {nev n}  (sig m (pr p q)) = sig (neN m) (pr (qNn p) q) 
  quotelema N {zerov}  sv = sig zeron (pr qNz refl) 
  quotelema N {sucv v} sv = let  qv = quotelema N {v} sv in sig (sucn (σ₁ qv)) (pr (qNs (π₁ (σ₂ qv))) (congsuc (π₂ (σ₂ qv))))   
  quotelema One     {v} sv = sig voidn (pr qone ηvoid) 
  quotelema (σ × τ) {v} (pr (sig w (tr p p' p'')) (sig w' (tr q q' q''))) = 
    sig < σ₁ qw , σ₁ qw' >n 
        (pr (qprod p (π₁ (σ₂ qw)) q (π₁ (σ₂ qw'))) 
            (trans η<,> (cong<,> (trans p'' (π₂ (σ₂ qw))) (trans q'' (π₂ (σ₂ qw'))))))
    where
    qw  = quotelema σ p'
    qw' = quotelema τ q'

  quotelemb : forall {Γ} σ {n : NeV Γ σ}{m : NeN Γ σ} -> 
              quotⁿ n ⇓ m -> embⁿ n ≃ nembⁿ m -> SCV (nev n)
  quotelemb ι       {n} p q = sig _ (pr p q) 
  quotelemb (σ ⇒ τ) {n}{m} p q = \f a sa -> 
    let qla = quotelema σ sa
    in  sig (nev (appV (nevmap f n) a)) 
            (tr r$ne 
                (quotelemb τ 
                           (qⁿapp (quotⁿ⇓map f p) (π₁ (σ₂ qla))) 
                           (cong$ (trans (onevemb f n) 
                                         (trans (cong[] q reflˢ) 
                                                (sym (onenemb f m)))) 
                                  (π₂ (σ₂ qla)))) 
                (cong$ (trans (onevemb f n) (sym (onevemb f n))) refl))
  quotelemb N {v} p q = sig _ (pr p q) 
  quotelemb One     {n} p q = void 
  quotelemb (σ × τ) {n} p q = 
    pr (sig (nev (fstV n)) (tr rfstnev qfst  refl))
       (sig (nev (sndV n)) (tr rsndnev qsnd  refl)) 
    where
    qfst = quotelemb σ (qⁿfst p) (congfst q)
    qsnd = quotelemb τ (qⁿsnd p) (congsnd q)

SCR : forall {Γ σ}(z : Val Γ σ)(s : Val Γ (N ⇒ σ ⇒ σ))(v : Val Γ N) ->
      SCV z -> SCV s -> SCV v ->
      Σ (Val Γ σ) 
        \w -> (prim z & s & v ⇓ w) ∧ 
              SCV w ∧ 
               (prim (emb z) (emb s) (emb v) ≃ (emb w ))  
SCR {σ = σ} z s (nev n)  sz ss (sig m (pr p q)) =
  sig (nev (primV z s n)) 
      (tr rprn 
          (quotelemb σ (qⁿprim (π₁ (σ₂ qlaz)) (π₁ (σ₂ qlas)) p) 
                       (congprim (π₂ (σ₂ qlaz)) 
                                 (π₂ (σ₂ qlas)) 
                                 q))
          refl)
  where
  qlaz = quotelema σ sz
  qlas = quotelema (N ⇒ σ ⇒ σ) ss

SCR z s zerov    sz ss sv = sig z (tr rprz sz primz) 
SCR z s (sucv v) sz ss sv = 
  sig (σ₁ Sfv) 
      (tr (rprs (helper' (sym⁼ (oidvmap s)) (t1 (σ₂ Sf))) 
                (t1 (σ₂ Sv)) 
                (helper' (sym⁼ (oidvmap (σ₁ (ss oid v sv)))) (t1 (σ₂ Sfv)))) 
          (t2 (σ₂ Sfv)) 
          (trans (trans prims 
                        (cong$ (trans (trans (cong$ (trans (trans (sym []id) 
                                                                  (cong[] refl lemoid))
                                                           (sym (ovemb oid s))) 
                                                    refl) 
                                             (trans (trans (t3 (σ₂ Sf)) (sym []id)) 
                                                    (cong[] refl lemoid))) 
                                      (sym (ovemb oid (σ₁ (ss oid v sv)))))
                               (t3 (σ₂ Sv)))) 
                 (t3 (σ₂ Sfv)))) 
  where 
  Sv  = SCR z s v sz ss sv
  Sf  = ss oid v sv
  Sfv = t2 (σ₂ Sf) oid (σ₁ Sv) (t2 (σ₂ Sv)) 

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
            (trans (trans $[] (cong$ (t3 (σ₂ st)) (t3 (σ₂ su)))) 
                   (helper'' (sym⁼ (oidvmap (σ₁ st))) {σ₁ (fundthrm u vs svs)}{σ₁ (t2 (σ₂ (fundthrm t vs svs)) oid (σ₁ (fundthrm u vs svs)) (t2 (σ₂ (fundthrm u vs svs))))} (t3 (σ₂ stu)))))
    where
    st  = fundthrm t vs svs
    su  = fundthrm u vs svs
    stu = t2 (σ₂ st) oid (σ₁ su) (t2 (σ₂ su))
  fundthrm zero         vs svs = 
    sig zerov 
        (tr rzero void zero[]) 
  fundthrm (suc t)      vs svs = 
    sig (sucv (σ₁ ft)) 
        (tr (rsuc (t1 (σ₂ ft))) 
            (t2 (σ₂ ft)) 
            (trans suc[] (congsuc (t3 (σ₂ ft)))))
    where
    ft = fundthrm t vs svs
  fundthrm (prim z s t) vs svs = 
    sig (σ₁ fv) 
        (tr (rprim (t1 (σ₂ fz)) (t1 (σ₂ fs)) (t1 (σ₂ ft)) (t1 (σ₂ fv))) 
            (t2 (σ₂ fv)) 
            (trans prim[] 
                   (trans (congprim (t3 (σ₂ fz)) (t3 (σ₂ fs)) (t3 (σ₂ ft))) 
                          (t3 (σ₂ fv)))))
     where
     fz = fundthrm z vs svs
     fs = fundthrm s vs svs
     ft = fundthrm t vs svs
     fv = SCR (σ₁ fz) (σ₁ fs) (σ₁ ft) (t2 (σ₂ fz)) (t2 (σ₂ fs)) (t2 (σ₂ ft))
  fundthrm void      vs svs = sig voidv (tr rvoid void void[]) 
  fundthrm < t , u > vs svs = 
    sig < σ₁ ft , σ₁ fu >v  
        (tr (r<,> (t1 (σ₂ ft)) (t1 (σ₂ fu))) 
            (pr (sig (σ₁ ft) (tr rfst<,> (t2 (σ₂ ft)) βfst)) (sig (σ₁ fu) (tr rsnd<,> (t2 (σ₂ fu)) βsnd)))
            (trans <,>[] (cong<,> (t3 (σ₂ ft)) (t3 (σ₂ fu)))))
    where 
    ft = fundthrm t vs svs
    fu = fundthrm u vs svs
  fundthrm (fst t)   vs svs = 
    sig (σ₁ ftfst) 
        (tr (rfst (t1 (σ₂ ft)) (t1 (σ₂ ftfst)))
            (t2 (σ₂ ftfst)) 
            (trans fst[] (trans (congfst (t3 (σ₂ ft))) (t3 (σ₂ ftfst))))) 
    where
    ft    = fundthrm t vs svs
    ftfst = π₁ (t2 (σ₂ ft))
  fundthrm (snd t)   vs svs = 
    sig (σ₁ ftsnd ) 
        (tr (rsnd (t1 (σ₂ ft)) (t1 (σ₂ ftsnd)))
            (t2 (σ₂ ftsnd)) 
            (trans snd[] (trans (congsnd (t3 (σ₂ ft))) (t3 (σ₂ ftsnd))))) 
    where
    ft = fundthrm t vs svs
    ftsnd = π₂ (t2 (σ₂ ft))

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

scvar : forall {Γ σ}(x : Var Γ σ) -> SCV (nev (varV x))
scvar {σ = σ} x = quotelemb σ qⁿvar refl 

scid : forall Γ -> SCE (vid {Γ})
scid ε       = sε 
scid (Γ < σ) = s<< (scemap (weak σ) _ (scid Γ)) (scvar (vZ {σ = σ})) 

normthrm : forall {Γ σ}(t : Tm Γ σ) -> Σ (Nf Γ σ) \n -> nf t ⇓ n ∧ (t ≃ nemb n)
normthrm t = sig (σ₁ qt) (pr (norm⇓ (t1 (σ₂ ft)) (π₁ (σ₂ qt))) 
                         (trans (trans (trans (sym []id) (cong[] refl embvid))
                                       (t3 (σ₂ ft))) 
                                (π₂ (σ₂ qt))))  
  where
  ft = fundthrm t vid (scid _)
  qt = quotelema _ (t2 (σ₂ ft))
