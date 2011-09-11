module NaturalNumbers.OPEBigStep where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.OPE
open import NaturalNumbers.OPELemmas
open import NaturalNumbers.BigStepSemantics

mutual
  eval⇓map : forall {B Γ Δ σ}(f : OPE B Γ)
             {t : Tm Δ σ}{vs : Env Γ Δ}{v : Val Γ σ} ->
             eval t & vs ⇓ v -> eval t & emap f vs ⇓ vmap f v
  eval⇓map f rvar            = rvar 
  eval⇓map f (rsubs p p')    = rsubs (evalˢ⇓map f p) (eval⇓map f p') 
  eval⇓map f rlam            = rlam 
  eval⇓map f (rapp p p' p'') = 
    rapp (eval⇓map f p) (eval⇓map f p') ($$⇓map f p'') 
  eval⇓map f rzero           = rzero
  eval⇓map f (rsuc p)        = rsuc (eval⇓map f p)
  eval⇓map f (rprim p p' p'' p''') = 
    rprim (eval⇓map f p) (eval⇓map f p') (eval⇓map f p'') (prim⇓map f p''')

  prim⇓map : forall {B Γ σ}(f : OPE B Γ)
             {z : Val Γ σ}{s : Val Γ (N ⇒ σ ⇒ σ)}{v : Val Γ N}{w : Val Γ σ} ->
             prim z & s & v ⇓ w -> 
             prim vmap f z & vmap f s & vmap f v ⇓ vmap f w
  prim⇓map f rprn            = rprn 
  prim⇓map f rprz            = rprz 
  prim⇓map f (rprs p p' p'') = 
    rprs ($$⇓map f p) (prim⇓map f p') ($$⇓map f p'') 

  $$⇓map : forall {Γ Δ σ τ}(f : OPE Γ Δ)
           {v : Val Δ (σ ⇒ τ)}{a : Val Δ σ}{v' : Val Δ τ} ->
           v $$ a ⇓ v' -> vmap f v $$ vmap f a ⇓ vmap f v'
  $$⇓map f (r$lam p) = r$lam (eval⇓map f p) 
  $$⇓map f r$ne      = r$ne 

  evalˢ⇓map : forall {A B Γ Δ}(f : OPE A B)
              {ts : Sub Γ Δ}{vs : Env B Γ}{ws : Env B Δ} ->
              evalˢ ts & vs ⇓ ws -> evalˢ ts & emap f vs ⇓ emap f ws
  evalˢ⇓map f rˢpop         = rˢpop 
  evalˢ⇓map f (rˢcons p p') = rˢcons (evalˢ⇓map f p) (eval⇓map f p') 
  evalˢ⇓map f rˢid          = rˢid 
  evalˢ⇓map f (rˢcomp p p') = rˢcomp (evalˢ⇓map f p) (evalˢ⇓map f p')

mutual
  quot⇓map : forall {Γ Δ σ}(f : OPE Γ Δ) ->
              {v : Val Δ σ}{n : Nf Δ σ} ->
              quot v ⇓ n -> quot vmap f v ⇓ nfmap f n
  quot⇓map f (qbase p)   = qbase (quotⁿ⇓map f p) 
  quot⇓map {σ = σ ⇒ τ} f (qarr {f = v} p p') with $$⇓map (keep _ f) p
  ... | p'' with vmap (keep σ f) (vmap (skip σ oid) v) | quotlemma σ f v
  ... | ._ | refl⁼ = qarr p'' (quot⇓map (keep _ f) p') 
  quot⇓map {σ = N} f qNz     = qNz
  quot⇓map {σ = N} f (qNs p) = qNs (quot⇓map f p)
  quot⇓map {σ = N} f (qNn p) = qNn (quotⁿ⇓map f p)

  quotⁿ⇓map : forall {Γ Δ σ}(f : OPE Γ Δ) ->
              {n : NeV Δ σ}{n' : NeN Δ σ} ->
              quotⁿ n ⇓ n' -> quotⁿ nevmap f n ⇓ nenmap f n'
  quotⁿ⇓map f qⁿvar        = qⁿvar 
  quotⁿ⇓map f (qⁿapp p p') = qⁿapp (quotⁿ⇓map f p) (quot⇓map f p') 
  quotⁿ⇓map f (qⁿprim p p' p'') =
    qⁿprim (quot⇓map f p) (quot⇓map f p') (quotⁿ⇓map f p'')