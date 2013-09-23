module FullSystem.StrongComputability where
open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.OPE
open import FullSystem.OPEBigStep
open import FullSystem.OPELemmas
open import FullSystem.Embeddings
open import FullSystem.Conversion
open import FullSystem.BigStepSemantics

SCV : forall {Γ σ} -> Val Γ σ -> Set
SCV {Γ} {ι}     (nev n)  = Σ (NeN Γ ι) \m -> quotⁿ n ⇓ m ∧ (embⁿ n ≃ nembⁿ m)
SCV {Γ} {σ ⇒ τ} v        = forall {B}(f : OPE B Γ)(a : Val B σ) -> SCV a -> 
  Σ (Val B τ) 
    \w -> (vmap f v $$ a ⇓ w) ∧ SCV w ∧ (emb (vmap f v) $ emb a ≃ emb w)    
SCV {Γ} {N}     zerov    = True
SCV {Γ} {N}     (sucv v) = SCV v 
SCV {Γ} {N}     (nev n)  = Σ (NeN Γ N) \m -> quotⁿ n ⇓ m ∧ (embⁿ n ≃ nembⁿ m) 
SCV {Γ} {One}   _       = True
SCV {Γ} {σ × τ} p       =
  (Σ (Val Γ σ) \v -> vfst p ⇓ v ∧ SCV v ∧ (fst (emb p) ≃ emb v)) ∧ 
  (Σ (Val Γ τ) \v -> vsnd p ⇓ v ∧ SCV v ∧ (snd (emb p) ≃ emb v))

data SCE {Γ : Con} : forall {Δ} -> Env Γ Δ -> Set where
  sε : SCE ε
  s<< : forall {Δ σ}{vs : Env Γ Δ}{v : Val Γ σ} ->
        SCE vs -> SCV v -> SCE (vs << v)

helper : forall {Θ}{σ}{τ}{f f' : Val Θ (σ ⇒ τ)} -> f == f' -> 
    {a : Val Θ σ} ->
    Σ (Val Θ τ) (\v -> (f' $$ a ⇓ v) ∧ SCV v ∧ (emb f' $ emb a ≃ emb v)) ->
    Σ (Val Θ τ) \v -> (f $$ a ⇓ v) ∧ SCV v ∧ (emb f $ emb a ≃ emb v)
helper refl⁼ p = p 

helper' : forall {Θ}{σ}{τ}{f f' : Val Θ (σ ⇒ τ)} -> f == f' -> 
    {a : Val Θ σ}{v : Val Θ τ}-> f' $$ a ⇓ v -> f $$ a ⇓ v
helper' refl⁼ p = p 

helper'' : forall {Θ}{σ}{τ}{f f' : Val Θ (σ ⇒ τ)} -> f == f' -> 
    {a : Val Θ σ}{v : Val Θ τ} -> 
    emb f' $ emb a ≃ emb v -> emb f $ emb a ≃ emb v
helper'' refl⁼ p = p 

scvmap : forall {Γ Δ σ}(f : OPE Γ Δ)(v : Val Δ σ) -> SCV v -> SCV (vmap f v)
scvmap {σ = ι} f (nev m)  (sig n (pr p q)) = 
  sig (nenmap f n) 
      (pr (quotⁿ⇓map f p) 
          (trans (onevemb f m) (trans (cong[] q reflˢ) (sym (onenemb f n)))))
scvmap {σ = σ ⇒ τ} f v     sv              = \f' a sa -> 
  helper (compvmap f' f v) (sv (comp f' f) a sa) 
scvmap {σ = N} f zerov    void             = void 
scvmap {σ = N} f (sucv v) sv               = scvmap f v sv 
scvmap {σ = N} f (nev n)  (sig m (pr p q)) = 
  sig (nenmap f m) 
      (pr (quotⁿ⇓map f p) 
          (trans (onevemb f n) (trans (cong[] q reflˢ) (sym (onenemb f m))))) 
scvmap {σ = One}   f v       void                       = void 
scvmap {σ = σ × τ} f v       (pr (sig w (tr p p' p'')) (sig w' (tr q q' q''))) = 
  pr (sig (vmap f w)  
          (tr (vfst⇓map f p) 
              (scvmap f w p')  
              (trans (trans (congfst (ovemb f v)) (sym fst[])) 
                     (trans (cong[] p'' reflˢ) (sym (ovemb f w))))))
     (sig (vmap f w') 
          (tr (vsnd⇓map f q) 
              (scvmap f w' q') 
              (trans (trans (congsnd (ovemb f v)) (sym snd[])) 
                     (trans (cong[] q'' reflˢ) (sym (ovemb f w'))))))

scemap : forall {B Γ Δ}(f : OPE B Γ)(vs : Env Γ Δ) -> 
         SCE vs -> SCE (emap f vs)
scemap f ε         sε         = sε 
scemap f (vs << v) (s<< p p') = s<< (scemap f vs p) (scvmap f v p') 
