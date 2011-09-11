{-# 
  OPTIONS --no-termination-check #-}

module FiniteCoproducts.Recursive where
open import FiniteCoproducts.Syntax

-- Recursive normaliser
_$$_ : forall {σ τ} -> Nf (σ ⇒ τ) -> Nf σ -> Nf τ
Kⁿ      $$ x       = Kⁿ¹ x
Kⁿ¹ x   $$ y       = x
Sⁿ      $$ x       = Sⁿ¹ x
Sⁿ¹ x   $$ y       = Sⁿ² x y
Sⁿ² x y $$ z       = (x $$ z) $$ (y $$ z)
NEⁿ     $$ ()
inlⁿ    $$ x       = inlⁿ¹ x
inrⁿ    $$ x       = inrⁿ¹ x
Cⁿ      $$ l       = Cⁿ¹ l
Cⁿ¹ l   $$ r       = Cⁿ² l r
Cⁿ² l r $$ inlⁿ¹ x  = l $$ x
Cⁿ² l r $$ inrⁿ¹ x  = r $$ x

nf : {σ : Ty} -> Tm σ -> Nf σ
nf K       = Kⁿ
nf S       = Sⁿ
nf (t $ u) = nf t $$ nf u
nf NE      = NEⁿ
nf inl     = inlⁿ
nf inr     = inrⁿ
nf C       = Cⁿ