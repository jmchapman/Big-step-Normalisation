module BasicSystem.Sound where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Recursive

sound : forall {σ}{t u : Tm σ} -> t ≡ u -> nf t == nf u
sound refl        = refl⁼ 
sound (sym p)     = sym⁼ (sound p) 
sound (trans p q) = trans⁼ (sound p) (sound q) 
sound K≡          = refl⁼ 
sound S≡          = refl⁼ 
sound ($≡ p q)    = resp2 (sound p) (sound q) _$$_