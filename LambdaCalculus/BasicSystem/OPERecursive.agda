{-# OPTIONS --no-termination-check 
  #-}
module BasicSystem.OPERecursive where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.RecursiveNormaliser

-- Unsurprisingly this isn't structurally recursive

mutual
  evmaplem : forall {B Γ Δ σ}(f : OPE B Γ)(t : Tm Δ σ)(vs : Env Γ Δ) -> 
             eval t (emap f vs) == vmap f (eval t vs)
  evmaplem f top        (vs << v) = refl⁼ 
  evmaplem f (t [ ts ]) vs        = 
    trans⁼ (resp (eval t) (evˢmaplem f ts vs)) (evmaplem f t (evalˢ ts vs)) 
  evmaplem f (λt t)     vs        = refl⁼ 
  evmaplem f (t $ u)    vs        = 
    trans⁼ (resp2 (\v a -> v $$ a) (evmaplem f t vs) (evmaplem f u vs))
           ($$maplem f (eval t vs) (eval u vs))
           

  $$maplem : forall {Γ Δ σ τ}(f : OPE Γ Δ)(v : Val Δ (σ ⇒ τ))(a : Val Δ σ) ->
             vmap f v $$ vmap f a == vmap f (v $$ a)
  $$maplem f (λv t vs) a = evmaplem f t (vs << a) 
  $$maplem f (nev n)   a = refl⁼ 

  evˢmaplem : forall {A B Γ Δ}(f : OPE A B)(ts : Sub Γ Δ)(vs : Env B Γ) ->
              evalˢ ts (emap f vs) == emap f (evalˢ ts vs)
  evˢmaplem f (pop σ)   (vs << v) = refl⁼ 
  evˢmaplem f (ts < t)  vs        = 
    resp2 _<<_ (evˢmaplem f ts vs) (evmaplem f t vs) 
  evˢmaplem f id        vs        = refl⁼ 
  evˢmaplem f (ts ○ us) vs        = 
    trans⁼ (resp (evalˢ ts) (evˢmaplem f us vs)) 
           (evˢmaplem f ts (evalˢ us vs))  

mutual
  qmaplem : forall {Γ Δ σ}(f : OPE Γ Δ)(v : Val Δ σ) -> 
             quot (vmap f v) == nfmap f (quot v)
  qmaplem {σ = ι}     f (nev n) = resp ne (qⁿmaplem f n) 
  qmaplem {σ = σ ⇒ τ} f v       = 
    resp λn 
         (trans⁼ (resp (\v -> quot (v $$ nev (varV vZ))) 
                       (compvmap (skip σ oid) f v)) 
                 (trans⁼ (trans⁼ (resp (\f -> quot (vmap (skip σ f) v $$ nev (varV vZ))) 
                                       (trans⁼ (leftid f) (sym⁼ (rightid f))))
                                 (resp quot (trans⁼ (resp (\v -> v $$ nev (varV vZ))
                                                           (sym⁼ (compvmap (keep σ f) (skip σ oid) v)))  
                                                     ($$maplem (keep σ f) 
                                                               (vmap (skip σ oid) v) 
                                                               (nev (varV vZ)) ))))
                         (qmaplem (keep σ f) 
                                  (vmap (skip σ oid) v $$ nev (varV vZ))))) 

  qⁿmaplem : forall {Γ Δ σ}(f : OPE Γ Δ)(n : NeV Δ σ) -> 
             quotⁿ (nevmap f n) == nenmap f (quotⁿ n)
  qⁿmaplem f (varV x)   = refl⁼ 
  qⁿmaplem f (appV n v) = resp2 appN (qⁿmaplem f n) (qmaplem f v) 
