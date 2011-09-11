module FiniteProducts.StrongComp where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.BigStep

-- Strong Computability
SCN : forall {σ} -> Nf σ -> Set
SCN {ι}       n = True
SCN {One}     n = True
SCN {σ ⇒ τ} f = forall a -> SCN a -> 
  Σ (Nf τ) \n ->  (f $ⁿ a ⇓ n) ∧ SCN n ∧ (⌜ f ⌝ $ ⌜ a ⌝ ≡ ⌜ n ⌝)
SCN {σ × τ} p = 
  (Σ (Nf σ) \n -> (fstⁿ $ⁿ p ⇓ n) ∧ SCN n ∧ (fst $ ⌜ p ⌝ ≡ ⌜ n ⌝))
  ∧
  (Σ (Nf τ) \n -> (sndⁿ $ⁿ p ⇓ n) ∧ SCN n ∧ (snd $ ⌜ p ⌝ ≡ ⌜ n ⌝))



-- there is a shorter proof of prop1 but the termination checker doesn't 
-- like it
prop1 : forall {σ} -> (n : Nf σ) -> SCN n
prop1 Kⁿ        = \x sx -> sig (Kⁿ¹ x) 
                               (tr rKⁿ (\y sy -> sig x (tr rKⁿ¹ sx K≡)) refl)
prop1 (Kⁿ¹ x)   = \y sy -> sig x (tr rKⁿ¹ (prop1 x) K≡) 
prop1 Sⁿ        = \x sx -> sig (Sⁿ¹ x) 
                               (tr rSⁿ 
                                   (\y sy -> sig (Sⁿ² x y)
                                                 (tr rSⁿ¹  
                                                     (\z sz -> 
  let pxz = sx z sz
      pyz = sy z sz
      pxzyz = π₁ (σ₁ pxz) (σ₀ pyz) (π₁ (σ₁ pyz)) 
  in  sig (σ₀ pxzyz) 
          (tr (rSⁿ² (π₀ (σ₁ pxz)) (π₀ (σ₁ pyz)) (π₀ (σ₁ pxzyz)))
              (π₁ (σ₁ pxzyz)) 
              (trans S≡ 
                     (trans ($≡ (π₂ (σ₁ pxz)) (π₂ (σ₁ pyz)))
                            (π₂ (σ₁ pxzyz)))))) refl)) 
  refl)
prop1 (Sⁿ¹ x)   = \y sy -> sig (Sⁿ² x y) (tr rSⁿ¹ (\z sz -> 
  let sx = prop1 x
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = π₁ (σ₁ pxz) (σ₀ pyz) (π₁ (σ₁ pyz)) 
  in  sig (σ₀ pxzyz) 
          (tr (rSⁿ² (π₀ (σ₁ pxz)) (π₀ (σ₁ pyz)) (π₀ (σ₁ pxzyz)))
              (π₁ (σ₁ pxzyz)) 
              (trans S≡ 
                     (trans ($≡ (π₂ (σ₁ pxz)) (π₂ (σ₁ pyz)))
                            (π₂ (σ₁ pxzyz)))))) 
  refl)  
prop1 (Sⁿ² x y) = \z sz ->
  let sx = prop1 x
      sy = prop1 y
      pxz = sx z sz
      pyz = sy z sz
      pxzyz = π₁ (σ₁ pxz) (σ₀ pyz) (π₁ (σ₁ pyz)) 
  in  sig (σ₀ pxzyz) 
          (tr (rSⁿ² (π₀ (σ₁ pxz)) (π₀ (σ₁ pyz)) (π₀ (σ₁ pxzyz)))         
              (π₁ (σ₁ pxzyz)) 
              (trans S≡ 
                     (trans ($≡ (π₂ (σ₁ pxz)) (π₂ (σ₁ pyz)))
                            (π₂ (σ₁ pxzyz)))))        
prop1 voidⁿ      = record {} 
prop1 prⁿ        = \x sx -> 
  sig (prⁿ¹ x)
      (tr rprⁿ 
          (\y sy -> sig (prⁿ² x y) 
                        (tr rprⁿ¹ 
                            (pr (sig x (tr rfstⁿ sx fst≡)) 
                                (sig y (tr rsndⁿ sy snd≡))) 
                            refl)) 
          refl)  
prop1 (prⁿ¹ x)   = \y sy -> 
  sig (prⁿ² x y) 
      (tr rprⁿ¹ 
          (pr (sig x (tr rfstⁿ (prop1 x) fst≡)) 
              (sig y (tr rsndⁿ sy snd≡))) 
          refl) 
prop1 (prⁿ² x y) =
  pr (sig x (tr rfstⁿ (prop1 x) fst≡)) 
     (sig y (tr rsndⁿ (prop1 y) snd≡))
prop1 fstⁿ      = \_ -> pfst
prop1 sndⁿ      = \_ -> psnd

SC : forall {σ} -> Tm σ -> Set
SC {σ} t = Σ (Nf σ) \n -> (t ⇓ n) ∧ SCN n ∧ (t ≡ ⌜ n ⌝)

prop2 : forall {σ} -> (t : Tm σ) -> SC t
prop2 K       = sig Kⁿ (tr rK (prop1 Kⁿ) refl) 
prop2 S       = sig Sⁿ (tr rS (prop1 Sⁿ) refl) 
prop2 (t $ u) with prop2 t          | prop2 u
prop2 (t $ u) | sig f (tr rf sf cf) | sig a (tr ra sa ca) with sf a sa
prop2 (t $ u) | sig f (tr rf sf cf) | sig a (tr ra sa ca) | sig v (tr rv sv cv)
  = sig v (tr (r$ rf ra rv) sv (trans ($≡ cf ca) cv))
prop2 void    = sig voidⁿ (tr rvoid (record {}) refl) 
prop2 pr      = 
  sig prⁿ 
      (tr rpr 
          (\x sx -> sig (prⁿ¹ x) 
                        (tr rprⁿ
                            (\y sy -> sig (prⁿ² x y) 
                                          (tr rprⁿ¹  
                                              (pr (sig x (tr rfstⁿ sx fst≡)) 
                                                  (sig y (tr rsndⁿ sy snd≡)))
                                              refl)) 
                            refl))
          refl ) 
prop2 fst     = sig fstⁿ (tr rfst (\_ -> pfst) refl) 
prop2 snd     = sig sndⁿ (tr rsnd (\_ -> psnd) refl) 
