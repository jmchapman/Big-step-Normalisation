{-# OPTIONS --no-termination-check 
  #-}

module FiniteProducts.Recursive where
open import FiniteProducts.Syntax

-- Recursive normaliser
_$$_ : forall {σ τ} -> Nf (σ ⇒ τ) -> Nf σ -> Nf τ
Kⁿ      $$ x        = Kⁿ¹ x
Kⁿ¹ x   $$ y        = x
Sⁿ      $$ x        = Sⁿ¹ x
Sⁿ¹ x   $$ y        = Sⁿ² x y
Sⁿ² x y $$ z        = (x $$ z) $$ (y $$ z)
prⁿ     $$ x        = prⁿ¹ x
prⁿ¹ x  $$ y        = prⁿ² x y 
fstⁿ    $$ prⁿ² x y = x
sndⁿ    $$ prⁿ² x y = y 

nf : {σ : Ty} -> Tm σ -> Nf σ
nf K = Kⁿ
nf S = Sⁿ
nf (t $ u) = nf t $$ nf u
nf void = voidⁿ
nf pr = prⁿ
nf fst = fstⁿ
nf snd = sndⁿ