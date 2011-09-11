{-# OPTIONS --no-termination-check 
  #-}
module NaturalNumbers.OPERecursive where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.OPE
open import NaturalNumbers.OPELemmas
open import NaturalNumbers.RecursiveNormaliser

-- Unsurprisingly this isn't structurally recursive

mutual
  evmaplem : forall {B Γ Δ σ}(f : OPE B Γ)(t : Tm Δ σ)(vs : Env Γ Δ) -> 
             eval t (emap f vs) == vmap f (eval t vs)
  evmaplem f top          (vs << v) = refl⁼ 
  evmaplem f (t [ ts ])   vs        = 
    trans⁼ (resp (eval t) (evˢmaplem f ts vs)) (evmaplem f t (evalˢ ts vs)) 
  evmaplem f (λt t)        vs        = refl⁼ 
  evmaplem f (t $ u)      vs        = 
    trans⁼ (resp2 (\v a -> v $$ a) (evmaplem f t vs) (evmaplem f u vs))
           ($$maplem f (eval t vs) (eval u vs))
  evmaplem f zero         vs        = refl⁼ 
  evmaplem f (suc t)      vs        = resp sucv (evmaplem f t vs) 
  evmaplem f (prim z s t) vs        = 
    trans⁼ (resp3 vprim (evmaplem f z vs) (evmaplem f s vs) (evmaplem f t vs)) 
           (primmaplem f (eval z vs) (eval s vs) (eval t vs))       

  primmaplem : forall {B Γ σ}(f : OPE B Γ)(z : Val Γ σ) s v -> 
               vprim (vmap f z) (vmap f s) (vmap f v) == vmap f (vprim z s v)
  primmaplem f z s (nev n)  = refl⁼ 
  primmaplem f z s zerov    = refl⁼ 
  primmaplem f z s (sucv v) = 
    trans⁼ (resp2 _$$_ ($$maplem f s v) (primmaplem f z s v)) 
           ($$maplem f (s $$ v) (vprim z s v)) 

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
  qmaplem {σ = ι}     f (nev n) = resp neι (qⁿmaplem f n) 
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
  qmaplem {Γ} {Δ} {N} f (nev n) = resp neN (qⁿmaplem f n) 
  qmaplem {Γ} {Δ} {N} f zerov    = refl⁼ 
  qmaplem {Γ} {Δ} {N} f (sucv v) = resp sucn (qmaplem f v)  

  qⁿmaplem : forall {Γ Δ σ}(f : OPE Γ Δ)(n : NeV Δ σ) -> 
             quotⁿ (nevmap f n) == nenmap f (quotⁿ n)
  qⁿmaplem f (varV x)      = refl⁼ 
  qⁿmaplem f (appV n v)    = resp2 appN (qⁿmaplem f n) (qmaplem f v) 
  qⁿmaplem f (primV z s n) = 
    resp3 primN (qmaplem f z) (qmaplem f s) (qⁿmaplem f n) 