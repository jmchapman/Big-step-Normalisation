module BasicSystem.StrongConvertibility where
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.OPERecursive
open import BasicSystem.RecursiveNormaliser
open import BasicSystem.Utils

_∼_ : forall {Γ σ} -> Val Γ σ -> Val Γ σ -> Set 
_∼_ {Γ}{ι}     (nev n) (nev n') = quotⁿ n == quotⁿ n'   
_∼_ {Γ}{σ ⇒ τ} v       v'       = forall {B}(f : OPE B Γ){a a' : Val B σ} -> 
    a ∼ a' -> (vmap f v $$ a) ∼ (vmap f v' $$ a')

data _∼ˢ_ {Γ : Con} : forall {Δ} -> Env Γ Δ -> Env Γ Δ -> Set where
  ∼ε  : ε ∼ˢ ε
  ∼<< : forall {Δ σ}{vs vs' : Env Γ Δ}{v v' : Val Γ σ} -> 
        vs ∼ˢ vs' -> v ∼ v' -> (vs << v) ∼ˢ (vs' << v')

helper : forall {Θ}{σ}{τ}{f f' f'' f''' : Val Θ (σ ⇒ τ)} -> 
         f == f' -> f'' == f''' -> {a a' : Val Θ σ} -> 
         (f' $$ a) ∼ (f''' $$ a') -> (f $$ a) ∼ (f'' $$ a')
helper refl⁼ refl⁼ p = p 

helper' : forall {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{vs vs' vs'' : Env Γ Δ} -> 
          vs'' == vs' -> {a a' : Val Γ σ} ->          
          eval t (vs << a) ∼ eval t (vs' << a') -> 
          eval t (vs << a) ∼ eval t (vs'' << a')
helper' refl⁼ p = p 

∼map : forall {Γ Δ σ}(f : OPE Γ Δ){v v' : Val Δ σ} -> v ∼ v' ->
       vmap f v ∼ vmap f v'
∼map {σ = ι}     f {nev n}{nev n'}  p = 
  trans⁼ (qⁿmaplem f n) (trans⁼ (resp (nenmap f) p) (sym⁼ (qⁿmaplem f n')) ) 
∼map {σ = σ ⇒ τ} f {v}    {v'}      p = \f' p' -> 
   helper (compvmap f' f v) (compvmap f' f v') (p (comp f' f) p')  

∼ˢmap : forall {B Γ Δ}(f : OPE B Γ){vs vs' : Env Γ Δ} -> vs ∼ˢ vs' -> 
        emap f vs ∼ˢ emap f vs'
∼ˢmap f ∼ε         = ∼ε 
∼ˢmap f (∼<< p p') = ∼<< (∼ˢmap f p) (∼map f p') 

mutual
  sym∼ : forall {Γ σ}{v v' : Val Γ σ} -> v ∼ v' -> v' ∼ v
  sym∼ {σ = ι}     {nev n}{nev n'} p = sym⁼ p 
  sym∼ {σ = σ ⇒ τ}                 p = \f p' -> sym∼ (p f (sym∼ p'))   


  sym∼ˢ : forall {Γ Δ}{vs vs' : Env Γ Δ} -> vs ∼ˢ vs' -> vs' ∼ˢ vs
  sym∼ˢ ∼ε        = ∼ε 
  sym∼ˢ (∼<< p q) = ∼<< (sym∼ˢ p) (sym∼ q)

mutual
  trans∼ : forall {Γ σ}{v v' v'' : Val Γ σ} -> v ∼ v' -> v' ∼ v'' -> v ∼ v''
  trans∼ {σ = ι}     {nev n}{nev n'}{nev n''} p p' = trans⁼ p p' 
  trans∼ {σ = σ ⇒ τ}                          p p' = \f p'' -> 
    trans∼ (p f (trans∼ p'' (sym∼ p''))) (p' f p'')  

  -- using that if a is related to a' then a is related to a

  trans∼ˢ : forall {Γ Δ}{vs vs' vs'' : Env Γ Δ} -> 
            vs ∼ˢ vs' -> vs' ∼ˢ vs'' -> vs ∼ˢ vs''
  trans∼ˢ ∼ε         ∼ε         = ∼ε 
  trans∼ˢ (∼<< p p') (∼<< q q') = ∼<< (trans∼ˢ p q) (trans∼ p' q')
