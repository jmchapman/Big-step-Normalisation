module BasicSystem.OPELemmas where

open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.Utils
open import BasicSystem.Embeddings
open import BasicSystem.Conversion

rightid : forall {Γ Δ} (f : OPE Γ Δ) -> comp f oid == f
rightid done     = refl⁼ 
rightid (keep σ f) = resp (keep σ) (rightid f) 
rightid (skip σ f) = resp (skip σ) (rightid f)

leftid : forall {Γ Δ} (f : OPE Γ Δ) -> comp oid f == f
leftid done       = refl⁼ 
leftid (keep σ f) = resp (keep σ)  (leftid f) 
leftid (skip σ f) = resp (skip σ) (leftid f)

-- Variables
oidxmap : forall {Γ σ}(x : Var Γ σ) -> xmap oid x == x
oidxmap vZ       = refl⁼ 
oidxmap (vS σ x) = resp (vS σ) (oidxmap x) 

compxmap : forall {B Γ Δ σ}(f : OPE B Γ)(g : OPE Γ Δ)(x : Var Δ σ) -> 
           xmap f (xmap g x) == xmap (comp f g) x
compxmap done     done     ()
compxmap (skip σ f) g           x         = resp (vS σ) (compxmap f g x)  
compxmap (keep σ f) (keep .σ g) vZ        = refl⁼ 
compxmap (keep σ f) (keep .σ g) (vS .σ x) = resp (vS σ) (compxmap f g x) 
compxmap (keep σ f) (skip .σ g) x         = resp (vS σ) (compxmap f g x) 

-- Values
mutual
  oidvmap : forall {Γ σ}(v : Val Γ σ) -> vmap oid v == v
  oidvmap (λv t vs) = resp (λv t) (oidemap vs) 
  oidvmap (nev n)   = resp nev (oidnevmap n) 

  oidnevmap : forall {Γ σ}(n : NeV Γ σ) -> nevmap oid n == n
  oidnevmap (varV x)   = resp varV (oidxmap x) 
  oidnevmap (appV n v) = resp2 appV (oidnevmap n) (oidvmap v) 
  
  oidemap : forall {Γ Δ}(vs : Env Γ Δ) -> emap oid vs == vs
  oidemap ε        = refl⁼ 
  oidemap (vs << v) = resp2 _<<_ (oidemap vs) (oidvmap v) 

mutual
  compvmap : forall {B Γ Δ σ}(f : OPE B Γ)(g : OPE Γ Δ)(v : Val Δ σ) -> 
             vmap f (vmap g v) == vmap (comp f g) v
  compvmap f g (λv t vs) = resp (λv t) (compemap f g vs) 
  compvmap f g (nev n)   = resp nev (compnevmap f g n) 

  compnevmap : forall {B Γ Δ σ}(f : OPE B Γ)(g : OPE Γ Δ)(n : NeV Δ σ) -> 
               nevmap f (nevmap g n) == nevmap (comp f g) n
  compnevmap f g (varV x)   = resp varV (compxmap f g x) 
  compnevmap f g (appV n v) = resp2 appV (compnevmap f g n) (compvmap f g v) 

  compemap : forall {A B Γ Δ}(f : OPE A B)(g : OPE B Γ)(vs : Env Γ Δ) -> 
             emap f (emap g vs) == emap (comp f g) vs
  compemap f g ε         = refl⁼ 
  compemap f g (vs << v) = resp2 _<<_ (compemap f g vs) (compvmap f g v) 

quotlemma : forall {Γ Δ σ} τ (f : OPE Γ Δ)(v : Val Δ σ) ->
             vmap (keep τ f) (vmap (skip τ oid) v) == vwk τ (vmap f v)
quotlemma τ f v = 
  trans⁼ (trans⁼ (compvmap (keep τ f) (skip τ oid) v)
                 (resp (\f -> vmap (skip τ f) v)
                       (trans⁼ (rightid f) 
                               (sym⁼ (leftid f)))))
         (sym⁼ (compvmap (skip τ oid) f v))

-- Embedding and conversion
-- Variables
oxemb : forall {Γ Δ σ}(f : OPE Γ Δ)(x : Var Δ σ) ->
        embˣ (xmap f x) ≃ embˣ x [ oemb f ]
oxemb (keep σ f) vZ       = sym top< 
oxemb (skip σ f) vZ       = trans (cong[] (oxemb f vZ) reflˢ) [][] 
oxemb (keep .τ f) (vS τ x) = 
  trans (cong[] (oxemb f x) reflˢ)
        (trans (trans [][] (cong[] refl (symˢ popcomp))) (sym [][])) 
oxemb (skip σ  f) (vS τ x) = trans (cong[] (oxemb f (vS τ x)) reflˢ) [][] 
oxemb done ()

-- Values
mutual
  ovemb : forall {Γ Δ σ}(f : OPE Γ Δ)(v : Val Δ σ) ->
            emb (vmap f v) ≃ emb v [ oemb f ]
  ovemb f (λv t vs) = trans (cong[] refl (oeemb f vs)) (sym [][]) 
  ovemb f (nev n)   = onevemb f n 

  onevemb : forall {Γ Δ σ}(f : OPE Γ Δ)(n : NeV Δ σ) ->
            embⁿ (nevmap f n) ≃ embⁿ n [ oemb f ]
  onevemb f (varV x)   = oxemb f x 
  onevemb f (appV n v) = trans (cong$ (onevemb f n) (ovemb f v)) (sym $[]) 

  oeemb : forall {B Γ Δ}(f : OPE B Γ)(vs : Env Γ Δ) ->
           embˢ (emap f vs) ≃ˢ embˢ vs ○ oemb f
  oeemb f (vs << v) = transˢ (cong< (oeemb f vs) (ovemb f v)) (symˢ comp<) 
  oeemb {Γ = Γ < σ} (keep .σ f) ε = 
    transˢ (transˢ (transˢ (cong○ (oeemb f ε) reflˢ) assoc) 
                   (cong○ reflˢ (symˢ popcomp))) 
           (symˢ assoc) 
  oeemb {Γ = Γ < σ} (skip τ  f) ε = transˢ (cong○ (oeemb f ε) reflˢ) assoc 
  oeemb {Γ = ε} done       ε = symˢ leftidˢ 
  oeemb {Γ = ε} (skip σ f) ε = transˢ (cong○ (oeemb f ε) reflˢ) assoc 

lemoid : forall {Γ} -> id {Γ} ≃ˢ oemb oid
lemoid {ε}     = reflˢ 
lemoid {Γ < σ} = transˢ idcomp (cong< (cong○ (lemoid {Γ}) reflˢ) refl) 

-- Normal Forms
mutual
  onfemb : forall {Γ Δ σ}(f : OPE Γ Δ)(n : Nf Δ σ) ->
           nemb (nfmap f n) ≃ nemb n [ oemb f ]
  onfemb f (λn n) = trans (congλ (onfemb (keep _ f) n)) (sym λ[]) 
  onfemb f (ne n) = onenemb f n 

  onenemb : forall {Γ Δ σ}(f : OPE Γ Δ)(n : NeN Δ σ) ->
            nembⁿ (nenmap f n) ≃ nembⁿ n [ oemb f ]
  onenemb f (varN x)    = oxemb f x 
  onenemb f (appN n n') = trans (cong$ (onenemb f n) (onfemb f n')) (sym $[]) 