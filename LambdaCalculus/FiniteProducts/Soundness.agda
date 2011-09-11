module FiniteProducts.Soundness where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.OPERecursive
open import FiniteProducts.RecursiveNormaliser
open import FiniteProducts.Conversion
open import FiniteProducts.StrongConvertibility
open import FiniteProducts.IdentityEnvironment
mutual
  idext : forall {Γ Δ σ}(t : Tm Δ σ){vs vs' : Env Γ Δ} -> vs ∼ˢ vs' ->
          eval t vs ∼ eval t vs'
  idext top              (∼<< p q) = q 
  idext (t [ ts ])       p         = idext t (idextˢ ts p)
  idext (λt t)            p         = \f p' -> idext t (∼<< (∼ˢmap f p) p')   
  idext (t $ u){vs}{vs'} p         = 
    helper (sym⁼ (oidvmap (eval t vs))) 
           (sym⁼ (oidvmap (eval t vs'))) 
           (idext t p oid (idext u p)) 
  idext void             p         = void 
  idext < t , u >        p         = pr (idext t p) (idext u p) 
  idext (fst t)          p         = π₁ (idext t p) 
  idext (snd t)          p         = π₂ (idext t p) 

  idextˢ : forall {B Γ Δ}(ts : Sub Γ Δ){vs vs' : Env B Γ} -> vs ∼ˢ vs' ->
           evalˢ ts vs ∼ˢ evalˢ ts vs' 
  idextˢ (pop σ)   (∼<< p q) = p 
  idextˢ (ts < t)  p         = ∼<< (idextˢ ts p) (idext t p) 
  idextˢ id        p         = p 
  idextˢ (ts ○ us) p         = idextˢ ts (idextˢ us p)

mutual
  sfundthrm : forall {Γ Δ σ}{t t' : Tm Δ σ} -> t ≃ t' ->
              {vs vs' : Env Γ Δ} -> vs ∼ˢ vs' -> eval t vs ∼ eval t' vs'
  sfundthrm {t = t} refl  q = idext t q
  sfundthrm (sym p)       q = sym∼ (sfundthrm p (sym∼ˢ q)) 
  sfundthrm (trans p p')  q = 
    trans∼ (sfundthrm p (trans∼ˢ q (sym∼ˢ q))) 
           (sfundthrm p' q)  
  sfundthrm (cong[] p p') q = sfundthrm p (sfundthrmˢ p' q) 
  sfundthrm (congλ p)     q = \f p' -> sfundthrm p (∼<< (∼ˢmap f q) p')  
  sfundthrm (cong$ {t = t}{t' = t'} p p')  q = 
    helper (sym⁼ (oidvmap (eval t  _)))
           (sym⁼ (oidvmap (eval t' _)))
           (sfundthrm p q oid (sfundthrm p' q)) 
  sfundthrm {t' = t'} top<          q = idext t' q 
  sfundthrm {t = t [ ts ] [ us ]} [][]          q = idext t (idextˢ ts (idextˢ us q))  
  sfundthrm {t' = t} []id          q = idext t q 
  sfundthrm (λ[] {t = t}{ts = ts}){vs}{vs'} q = \f p -> 
    helper' {t = t}
            (evˢmaplem f ts vs') 
            (idext t (∼<< (∼ˢmap f (idextˢ ts q)) p)) 
  sfundthrm ($[]{t = t}{u = u}{ts = ts}) q =
    helper (sym⁼ (oidvmap (eval t (evalˢ ts _))))
           (sym⁼ (oidvmap (eval t (evalˢ ts _))))
           (idext t (idextˢ ts q) oid (idext u (idextˢ ts q))) 
  sfundthrm (βλ {t = t}{u = u}) q = idext t (∼<< q (idext u q)) 
  sfundthrm (ηλ {t = t}){vs = vs}{vs' = vs'} q = \f {a} {a'} p -> 
    helper {f = vmap f (eval t vs)} 
           refl⁼
           (evmaplem f t vs')
           (idext t q f p) 
  sfundthrm (cong<,> p q) r = pr (sfundthrm p r) (sfundthrm q r) 
  sfundthrm (congfst p)   q = π₁ (sfundthrm p q) 
  sfundthrm (congsnd p)   q = π₂ (sfundthrm p q) 
  sfundthrm void[]        p = void 
  sfundthrm (<,>[] {t = t}{u}{ts}) p = pr (idext t (idextˢ ts p))
                                          (idext u (idextˢ ts p))
  sfundthrm (fst[] {t = t}{ts}) p = π₁ (idext t (idextˢ ts p)) 
  sfundthrm (snd[] {t = t}{ts}) p = π₂ (idext t (idextˢ ts p))
  sfundthrm {t' = t} βfst          p = idext t p 
  sfundthrm {t' = u} βsnd          p = idext u p 
  sfundthrm (η<,> {t = t}) p = idext t p 
  sfundthrm ηvoid         p = void 

  sfundthrmˢ : forall {B Γ Δ}{ts ts' : Sub Γ Δ} -> ts ≃ˢ ts' ->
               {vs vs' : Env B Γ} -> vs ∼ˢ vs' -> evalˢ ts vs ∼ˢ evalˢ ts' vs'
  sfundthrmˢ {ts = ts} reflˢ         q = idextˢ ts q 
  sfundthrmˢ (symˢ p)      q = sym∼ˢ (sfundthrmˢ p (sym∼ˢ q)) 
  sfundthrmˢ (transˢ p p') q = 
    trans∼ˢ (sfundthrmˢ p (trans∼ˢ q (sym∼ˢ q)))
             (sfundthrmˢ p' q)  
  sfundthrmˢ (cong< p p')  q = ∼<< (sfundthrmˢ p q) (sfundthrm p' q) 
  sfundthrmˢ (cong○ p p')  q = sfundthrmˢ p (sfundthrmˢ p' q ) 
  sfundthrmˢ idcomp        (∼<< q q') = ∼<< q q' 
  sfundthrmˢ {ts' = ts} popcomp       q = idextˢ ts q 
  sfundthrmˢ {ts' = ts} leftidˢ       q = idextˢ ts q 
  sfundthrmˢ {ts' = ts} rightidˢ      q = idextˢ ts q 
  sfundthrmˢ {ts = (ts ○ ts') ○ ts''} assoc         q = idextˢ ts (idextˢ ts' (idextˢ ts'' q)) 
  sfundthrmˢ {ts = (ts < t) ○ ts'} comp<         q = 
   ∼<< (idextˢ ts (idextˢ ts' q)) (idext t (idextˢ ts' q)) 

mutual
  squotlema : forall {Γ σ}{v v' : Val Γ σ} -> 
               v ∼ v' -> quot v == quot v'
  squotlema {σ = ι}    {nev n}{nev n'} p = resp ne p 
  squotlema {Γ}{σ ⇒ τ}                 p = 
    resp λn (squotlema {σ = τ} (p (weak σ) q)) 
    where
    q = squotlemb (refl⁼ {a = quotⁿ (varV (vZ {Γ}{σ}))})
  squotlema {σ = One}                  p = refl⁼ 
  squotlema {σ = σ × τ} (pr p q) = resp2 <_,_>n (squotlema p) (squotlema q) 

  squotlemb : forall {Γ σ}{n n' : NeV Γ σ} -> 
               quotⁿ n == quotⁿ n' -> nev n ∼ nev n'
  squotlemb {σ = ι}     p = p 
  squotlemb {σ = σ ⇒ τ}{n}{n'} p = \f q -> 
    let q' = squotlema {σ = σ} q     
    in  squotlemb {σ = τ} 
                   (resp2 appN 
                          (trans⁼ (qⁿmaplem f n) 
                                  (trans⁼ (resp (nenmap f) p) 
                                          (sym⁼ (qⁿmaplem f n')))) 
                          q')   
  squotlemb {σ = One}   p = void 
  squotlemb {σ = σ × τ} p = pr (squotlemb (resp fstN p)) (squotlemb (resp sndN p)) 

sndvar : forall {Γ σ}(x : Var Γ σ) -> nev (varV x) ∼ nev (varV x)
sndvar x = squotlemb (refl⁼ {a = quotⁿ (varV x)}) 

sndid : forall Γ -> (vid {Γ}) ∼ˢ (vid {Γ})
sndid ε       = ∼ε 
sndid (Γ < σ) = ∼<< (∼ˢmap (skip σ oid) (sndid Γ)) (sndvar vZ) 

soundthrm : forall {Γ σ}{t t' : Tm Γ σ} -> t ≃ t' -> nf t == nf t'
soundthrm {Γ}{σ} p = squotlema {σ = σ} (sfundthrm p (sndid Γ)) 