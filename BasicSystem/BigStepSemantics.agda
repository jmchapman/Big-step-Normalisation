module BasicSystem.BigStepSemantics where
open import BasicSystem.Syntax
open import BasicSystem.OPE

mutual
  data eval_&_⇓_ : forall {Γ Δ σ} -> Tm Δ σ -> Env Γ Δ -> Val Γ σ -> Set where
    rlam  : forall {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{vs : Env Γ Δ} ->
            eval λt t & vs ⇓ λv t vs
    rvar  : forall {Γ Δ σ}{vs : Env Γ Δ}{v : Val Γ σ} -> 
            eval top & (vs << v) ⇓ v
    rsubs : forall {B Γ Δ σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{vs : Env B Γ}{ws v} ->
            evalˢ ts & vs ⇓ ws -> eval t & ws ⇓ v -> eval t [ ts ] & vs ⇓ v
    rapp  : forall {Γ Δ σ τ}{t : Tm Δ (σ ⇒ τ)}{u : Tm Δ σ}{vs : Env Γ Δ}
            {f : Val Γ (σ ⇒ τ)}{a : Val Γ σ}{v : Val Γ τ} ->
            eval t & vs ⇓ f -> eval u & vs ⇓ a -> f $$ a ⇓ v ->
            eval t $ u & vs ⇓ v

  data _$$_⇓_ : forall {Γ σ τ} -> 
                Val Γ (σ ⇒ τ) -> Val Γ σ -> Val Γ τ -> Set where
    r$lam : forall {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{vs : Env Γ Δ}{a : Val Γ σ}{v} ->
            eval t & vs << a ⇓ v -> λv t vs $$ a ⇓ v
    r$ne  : forall {Γ σ τ}{n : NeV Γ (σ ⇒ τ)}{v : Val Γ σ} ->
            nev n $$ v ⇓ nev (appV n v)

  data evalˢ_&_⇓_ : forall {Γ Δ Σ} -> 
                    Sub Δ Σ -> Env Γ Δ -> Env Γ Σ -> Set where
    rˢpop  : forall {Γ Δ σ}{vs : Env Γ Δ}{v : Val Γ σ} -> 
             evalˢ pop σ & vs << v ⇓ vs
    rˢcons : forall {Γ Δ Σ σ}{ts : Sub Δ Σ}{t : Tm Δ σ}{vs : Env Γ Δ}{ws v} ->
             evalˢ ts & vs ⇓ ws -> eval t & vs ⇓ v -> 
             evalˢ ts < t & vs ⇓ (ws << v)
    rˢid   : forall {Γ Δ}{vs : Env Γ Δ} -> evalˢ id & vs ⇓ vs
    rˢcomp : forall {A B Γ Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Env A B}{ws}
                    {xs} -> evalˢ us & vs ⇓ ws ->
                    evalˢ ts & ws ⇓ xs -> evalˢ ts ○ us & vs ⇓ xs

mutual
  data quot_⇓_ : forall {Γ σ} -> Val Γ σ -> Nf Γ σ -> Set where
    qarr : forall {Γ σ τ}{f : Val Γ (σ ⇒ τ)}{v : Val (Γ < σ) τ}{n} ->
           vwk σ f $$ nev (varV vZ) ⇓ v ->  quot v ⇓ n -> quot f ⇓ λn n
    qbase : forall {Γ}{m : NeV Γ ι}{n} -> quotⁿ m ⇓ n -> quot nev m ⇓ ne n

  data quotⁿ_⇓_ : forall {Γ σ} -> NeV Γ σ -> NeN Γ σ -> Set where
    qⁿvar : forall {Γ σ}{x : Var Γ σ} -> quotⁿ varV x ⇓ varN x
    qⁿapp : forall {Γ σ τ}{m : NeV Γ (σ ⇒ τ)}{v}{n}{n'} ->
            quotⁿ m ⇓ n -> quot v ⇓ n' -> quotⁿ appV m v ⇓ appN n n'

open import BasicSystem.IdentityEnvironment

data nf_⇓_ {Γ : Con}{σ : Ty} : Tm Γ σ -> Nf Γ σ -> Set where
  norm⇓ : forall {t v n} -> eval t & vid ⇓ v -> quot v ⇓ n -> nf t ⇓ n