module FullSystem.OPE where

open import FullSystem.Syntax

data OPE : Con -> Con -> Set where
  done : OPE ε ε
  keep : forall {Γ Δ} σ -> OPE Γ Δ -> OPE (Γ < σ) (Δ < σ)
  skip : forall {Γ Δ} σ -> OPE Γ Δ -> OPE (Γ < σ) Δ

oid : forall {Γ} -> OPE Γ Γ
oid {ε}     = done
oid {Γ < σ} = keep σ oid

comp : forall {B Γ Δ} -> OPE B Γ -> OPE Γ Δ -> OPE B Δ
comp done     done          = done
comp (skip σ f) g           = skip σ (comp f g) 
comp (keep σ f) (keep .σ g) = keep σ (comp f g) 
comp (keep σ f) (skip .σ g) = skip σ (comp f g)

weak : forall {Γ} τ -> OPE (Γ < τ) Γ
weak τ = skip τ oid

-- Variables
xmap : forall {Γ Δ σ} -> OPE Γ Δ -> Var Δ σ -> Var Γ σ
xmap done     ()
xmap (keep σ f) vZ        = vZ
xmap (keep σ f) (vS .σ x) = vS σ (xmap f x)
xmap (skip σ f) x         = vS σ (xmap f x)

-- Values
mutual
  vmap : forall {Γ Δ σ} -> OPE Γ Δ -> Val Δ σ -> Val Γ σ
  vmap f (λv t vs) = λv t (emap f vs) 
  vmap f (nev n)   = nev (nevmap f n) 
  vmap f zerov     = zerov 
  vmap f (sucv v)  = sucv (vmap f v) 
  vmap f voidv      = voidv
  vmap f < v , w >v = < vmap f v , vmap f w >v 

  nevmap : forall {Γ Δ σ} -> OPE Γ Δ -> NeV Δ σ -> NeV Γ σ
  nevmap f (varV x)      = varV (xmap f x)  
  nevmap f (appV n v)    = appV (nevmap f n) (vmap f v) 
  nevmap f (primV z s n) = primV (vmap f z) (vmap f s) (nevmap f n) 
  nevmap f (fstV n)   = fstV (nevmap f n) 
  nevmap f (sndV n)   = sndV (nevmap f n) 


  emap : forall {B Γ Δ} -> OPE B Γ -> Env Γ Δ -> Env B Δ
  emap f ε         = ε 
  emap f (vs << v) = emap f vs << vmap f v 

-- weakening for values
vwk : forall {Γ σ} τ -> Val Γ σ -> Val (Γ < τ) σ
vwk τ v = vmap (weak τ) v

ewk : forall {Γ Δ} τ -> Env Γ Δ -> Env (Γ < τ) Δ
ewk τ ε         = ε 
ewk τ (vs << v) = ewk τ vs << vwk τ v

-- Normal forms
mutual
  nfmap : forall {Γ Δ σ} -> OPE Γ Δ -> Nf Δ σ -> Nf Γ σ
  nfmap f (λn n)   = λn (nfmap (keep _ f) n) 
  nfmap f (neι n)  = neι (nenmap f n) 
  nfmap f (neN n)  = neN (nenmap f n)
  nfmap f zeron    = zeron 
  nfmap f (sucn n) = sucn (nfmap f n) 
  nfmap f voidn      = voidn 
  nfmap f < m , n >n = < nfmap f m , nfmap f n >n 

  nenmap : forall {Γ Δ σ} -> OPE Γ Δ -> NeN Δ σ -> NeN Γ σ
  nenmap f (varN x)    = varN (xmap f x) 
  nenmap f (appN n n') = appN (nenmap f n) (nfmap f n')
  nenmap f (primN z s n) = primN (nfmap f z) (nfmap f s) (nenmap f n) 
  nenmap f (fstN n)    = fstN (nenmap f n) 
  nenmap f (sndN n)    = sndN (nenmap f n) 

-- Embedding
oemb : forall {Γ Δ} -> OPE Γ Δ -> Sub Γ Δ
oemb done       = id 
oemb (keep σ f) = (oemb f ○ pop σ) < top  
oemb (skip σ f) = oemb f ○ pop σ
