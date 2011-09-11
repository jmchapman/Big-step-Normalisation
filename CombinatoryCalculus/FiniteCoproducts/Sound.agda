module FiniteCoproducts.Sound where

open import FiniteCoproducts.Utils
open import FiniteCoproducts.Syntax
open import FiniteCoproducts.Recursive

sound : forall {σ}{t u : Tm σ} -> t ≡ u -> nf t == nf u
sound refl        = refl⁼ 
sound (sym p)     = sym⁼ (sound p) 
sound (trans p q) = trans⁼ (sound p) (sound q) 
sound K≡          = refl⁼ 
sound S≡          = refl⁼ 
sound ($≡ p q)    = resp2 (sound p) (sound q) _$$_
sound Cl = refl⁼ 
sound Cr = refl⁼ 
