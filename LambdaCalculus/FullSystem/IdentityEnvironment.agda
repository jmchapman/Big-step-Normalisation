module FullSystem.IdentityEnvironment where
open import FullSystem.Syntax
open import FullSystem.Conversion
open import FullSystem.OPE
open import FullSystem.OPELemmas
open import FullSystem.Embeddings

vid : forall {Γ} -> Env Γ Γ
vid {ε}     = ε
vid {Γ < σ} = emap (skip σ oid) vid << nev (varV vZ)

embvid : forall {Γ} -> id {Γ} ≃ˢ embˢ vid
embvid {ε}     = reflˢ 
embvid {Γ < σ} = 
  transˢ idcomp 
         (cong< (transˢ (transˢ (cong○ (transˢ (symˢ rightidˢ) 
                                               (cong○ embvid lemoid)) 
                                       reflˢ)
                                assoc) 
                        (symˢ (oeemb (skip σ oid) vid)) )
                refl) 
