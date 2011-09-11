{-# OPTIONS --no-termination-check 
  #-}

module NaturalNumbers.Recursive where
open import NaturalNumbers.Syntax

-- Recursive normaliser
_$$_ : forall {σ τ} -> Nf (σ ⇒ τ) -> Nf σ -> Nf τ
Kⁿ      $$ x       = Kⁿ¹ x
Kⁿ¹ x   $$ y       = x
Sⁿ      $$ x       = Sⁿ¹ x
Sⁿ¹ x   $$ y       = Sⁿ² x y
Sⁿ² x y $$ z       = (x $$ z) $$ (y $$ z)
sucⁿ    $$ n       = sucⁿ¹ n
Rⁿ      $$ z       = Rⁿ¹ z
Rⁿ¹ z   $$ f       = Rⁿ² z f
Rⁿ² z f $$ zeroⁿ   = z
Rⁿ² z f $$ sucⁿ¹ n  = (f $$ n) $$ (Rⁿ² z f $$ n)

nf : {σ : Ty} -> Tm σ -> Nf σ
nf K = Kⁿ
nf S = Sⁿ
nf (t $ u) = nf t $$ nf u
nf zero = zeroⁿ
nf suc  = sucⁿ
nf R    = Rⁿ