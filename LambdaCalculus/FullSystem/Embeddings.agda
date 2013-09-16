module FullSystem.Embeddings where

open import FullSystem.Syntax

embˣ : forall {Γ σ} -> Var Γ σ -> Tm Γ σ
embˣ vZ       = top 
embˣ (vS τ x) = embˣ x [ pop τ ]

mutual
  emb  : forall {Γ σ} -> Val Γ σ -> Tm Γ σ
  emb (λv t vs) = λt t [ embˢ vs ] 
  emb (nev n)   = embⁿ n 
  emb zerov     = zero 
  emb (sucv v)  = suc (emb v) 
  emb voidv      = void
  emb < m , n >v = < emb m , emb n >

  embⁿ : forall {Γ σ} -> NeV Γ σ -> Tm Γ σ
  embⁿ (varV x)      = embˣ x 
  embⁿ (appV n v)    = embⁿ n $ emb v
  embⁿ (primV z s n) = prim (emb z) (emb s) (embⁿ n) 
  embⁿ (fstV n)   = fst (embⁿ n)
  embⁿ (sndV n)   = snd (embⁿ n)


  embˢ : forall {Γ Σ} -> Env Γ Σ -> Sub Γ Σ
  embˢ (vs << v) = embˢ vs < emb v
  embˢ {ε}     ε = id 
  embˢ {Γ < σ} ε = embˢ {Γ} ε ○ pop σ 

mutual
  nemb  : forall {Γ σ} -> Nf Γ σ -> Tm Γ σ
  nemb (λn n)   = λt (nemb n) 
  nemb (neι n)  = nembⁿ n
  nemb (neN n)  = nembⁿ n
  nemb zeron    = zero 
  nemb (sucn n) = suc (nemb n)  
  nemb voidn      = void
  nemb < m , n >n = < nemb m , nemb n >

  nembⁿ : forall {Γ σ} -> NeN Γ σ -> Tm Γ σ
  nembⁿ (varN x)      = embˣ x
  nembⁿ (appN n n')   = nembⁿ n $ nemb n'
  nembⁿ (primN z f n) = prim (nemb z) (nemb f) (nembⁿ n) 
  nembⁿ (fstN n)    = fst (nembⁿ n)
  nembⁿ (sndN n)    = snd (nembⁿ n) 
