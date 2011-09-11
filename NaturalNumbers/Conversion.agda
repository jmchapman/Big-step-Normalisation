module NaturalNumbers.Conversion where
open import NaturalNumbers.Syntax

infix 10 _≃_
infix 10 _≃ˢ_

mutual
  data _≃_ : forall {Γ σ} -> Tm Γ σ -> Tm Γ σ -> Set where
    -- equivalence closure
    refl  : forall {Γ σ}{t : Tm Γ σ} -> t ≃ t
    sym   : forall {Γ σ}{t t' : Tm Γ σ} -> t ≃ t' -> t' ≃ t
    trans : forall {Γ σ}{t t' t'' : Tm Γ σ} -> t ≃ t' -> t' ≃ t'' -> t ≃ t''

    -- congruence closure
    cong[]   : forall {Γ Δ σ}{t t' : Tm Δ σ}{ts ts' : Sub Γ Δ} -> t ≃ t' ->
               ts ≃ˢ ts' -> t [ ts ] ≃ t' [ ts' ]

    congλ    : forall {Γ σ τ}{t t' : Tm (Γ < σ) τ} -> t ≃ t' -> λt t ≃ λt t'
    cong$    : forall {Γ σ τ}{t t' : Tm Γ (σ ⇒ τ)}{u u' : Tm Γ σ} -> t ≃ t' ->
                u ≃ u' -> t $ u ≃ t' $ u'

    congsuc  : forall {Γ}{t t' : Tm Γ N} -> t ≃ t' -> suc t ≃ suc t'
    congprim : forall {Γ σ}{z z' : Tm Γ σ}{s s'}{n n'} -> 
               z ≃ z' -> s ≃ s' -> n ≃ n' -> prim z s n ≃ prim z' s' n'
               

    -- computation rules
    top< : forall {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} -> top [ ts < t ] ≃ t 
    [][] : forall {B Γ Δ σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{us : Sub B Γ} ->
           t [ ts ] [ us ] ≃ t [ ts ○ us ]
    []id : forall {Γ σ}{t : Tm Γ σ} -> t [ id ] ≃ t

    λ[]  : forall {Γ Δ σ τ}{t : Tm (Δ < σ) τ}{ts : Sub Γ Δ} -> 
           λt t [ ts ] ≃ λt (t [ (ts ○ pop σ) < top ])
    $[]  : forall {Γ Δ σ τ}{t : Tm Δ (σ ⇒ τ)}{u : Tm Δ σ}{ts : Sub Γ Δ} ->
           (t $ u) [ ts ] ≃ t [ ts ] $ (u [ ts ])
    β    : forall {Γ σ τ}{t : Tm (Γ < σ) τ}{u : Tm Γ σ} ->
           λt t $ u ≃ t [ id < u ]
    η    : forall {Γ σ τ}{t : Tm Γ (σ ⇒ τ)} -> t ≃  λt (t [ pop σ ] $ top)

    zero[] : forall {Γ Δ}{ts : Sub Γ Δ} -> zero [ ts ] ≃ zero
    suc[]  : forall {Γ Δ t}{ts : Sub Γ Δ} -> suc t [ ts ] ≃ suc (t [ ts ])
    prim[] : forall {Γ Δ σ}{z : Tm Δ σ}{s n}{ts : Sub Γ Δ} -> 
             prim z s n [ ts ] ≃ prim (z [ ts ]) (s [ ts ]) (n [ ts ])
    primz : forall {Γ σ}{z : Tm Γ σ}{s} -> prim z s zero ≃ z
    prims : forall {Γ σ}{z : Tm Γ σ}{s n} -> 
            prim z s (suc n) ≃ ((s $ n) $ prim z s n)

  data _≃ˢ_ : forall {Γ Δ} -> Sub Γ Δ -> Sub Γ Δ -> Set where
    -- equivalence closure
    reflˢ  : forall {Γ Δ}{ts : Sub Γ Δ} -> ts ≃ˢ ts
    symˢ   : forall {Γ Δ}{ts ts' : Sub Γ Δ} -> ts ≃ˢ ts' -> ts' ≃ˢ ts
    transˢ : forall {Γ Δ}{ts ts' ts'' : Sub Γ Δ} -> ts ≃ˢ ts' -> 
             ts' ≃ˢ ts'' -> ts ≃ˢ ts''
  
    -- congruence closure
    cong<  : forall {Γ Δ σ}{ts ts' : Sub Γ Δ}{t t' : Tm Γ σ} -> ts ≃ˢ ts' ->
             t ≃ t' -> ts < t ≃ˢ ts' < t'
    cong○  : forall {B Γ Δ}{ts ts' : Sub Γ Δ}{us us' : Sub B Γ} -> ts ≃ˢ ts' ->
             us ≃ˢ us' -> ts ○ us ≃ˢ ts' ○ us'

    -- computation rules
    idcomp  : forall {Γ σ} -> id ≃ˢ (id {Γ} ○ pop σ) < top
    popcomp : forall {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ} -> 
              pop σ ○ (ts < t) ≃ˢ ts
    leftidˢ : forall {Γ Δ}{ts : Sub Γ Δ} -> id ○ ts ≃ˢ ts
    rightidˢ : forall {Γ Δ}{ts : Sub Γ Δ} -> ts ○ id ≃ˢ ts
    assoc   : forall {A B Γ Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} ->
              (ts ○ us) ○ vs ≃ˢ ts ○ (us ○ vs)
    comp<   : forall {B Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ σ}{us : Sub B Γ} ->
              (ts < t) ○ us ≃ˢ (ts ○ us) < t [ us ]
