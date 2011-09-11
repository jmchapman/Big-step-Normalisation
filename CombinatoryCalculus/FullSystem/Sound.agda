module FullSystem.Sound where

open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.Recursive

sound : forall {σ}{t u : Tm σ} -> t ≡ u -> nf t == nf u
sound refl        = refl⁼ 
sound (sym p)     = sym⁼ (sound p) 
sound (trans p q) = trans⁼ (sound p) (sound q) 
sound K≡          = refl⁼ 
sound S≡          = refl⁼ 
sound ($≡ p q)    = resp2 (sound p) (sound q) _$$_
sound fst≡        = refl⁼
sound snd≡        = refl⁼ 
sound Cl          = refl⁼ 
sound Cr          = refl⁼ 
sound Rzero≡      = refl⁼ 
sound Rsuc≡       = refl⁼ 