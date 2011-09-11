{-# OPTIONS --no-termination-check 
  #-}

module FullSystem.Recursive where
open import FullSystem.Syntax

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
NEⁿ     $$ ()
inlⁿ    $$ x       = inlⁿ¹ x
inrⁿ    $$ x       = inrⁿ¹ x
Cⁿ      $$ l       = Cⁿ¹ l
Cⁿ¹ l   $$ r       = Cⁿ² l r
Cⁿ² l r $$ inlⁿ¹ x  = l $$ x
Cⁿ² l r $$ inrⁿ¹ x  = r $$ x
sucⁿ    $$ n       = sucⁿ¹ n
Rⁿ      $$ z       = Rⁿ¹ z
Rⁿ¹ z   $$ f       = Rⁿ² z f
Rⁿ² z f $$ zeroⁿ   = z
Rⁿ² z f $$ sucⁿ¹ n  = (f $$ n) $$ (Rⁿ² z f $$ n)

nf : {σ : Ty} -> Tm σ -> Nf σ
nf K = Kⁿ
nf S = Sⁿ
nf (t $ u) = nf t $$ nf u
nf void = voidⁿ
nf pr = prⁿ
nf fst = fstⁿ
nf snd = sndⁿ
nf NE      = NEⁿ
nf inl     = inlⁿ
nf inr     = inrⁿ
nf C       = Cⁿ
nf zero = zeroⁿ
nf suc  = sucⁿ
nf R    = Rⁿ