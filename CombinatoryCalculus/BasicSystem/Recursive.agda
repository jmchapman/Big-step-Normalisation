{-# OPTIONS  --no-termination-check #-}

module BasicSystem.Recursive where
open import BasicSystem.Syntax

-- Recursive normaliser
_$$_ : forall {σ τ} -> Nf (σ ⇒ τ) -> Nf σ -> Nf τ
Kⁿ      $$ x       = Kⁿ¹ x
Kⁿ¹ x   $$ y       = x
Sⁿ      $$ x       = Sⁿ¹ x
Sⁿ¹ x   $$ y       = Sⁿ² x y
Sⁿ² x y $$ z       = (x $$ z) $$ (y $$ z)

nf : {σ : Ty} -> Tm σ -> Nf σ
nf K = Kⁿ
nf S = Sⁿ
nf (t $ u) = nf t $$ nf u