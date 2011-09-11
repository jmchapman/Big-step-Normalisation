module BasicSystem.StrongComp where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.BigStep

-- Strong Computability
SCN : forall {σ} -> Nf σ -> Set
SCN {ι}     n = True
SCN {σ ⇒ τ} f = forall a -> SCN a -> 
  Σ (Nf τ) \n ->  (f $ⁿ a ⇓ n) ∧ SCN n ∧ (⌜ f ⌝ $ ⌜ a ⌝ ≡ ⌜ n ⌝)

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

SC : forall {σ} -> Tm σ -> Set
SC {σ} t = Σ (Nf σ) \n -> (t ⇓ n) ∧ SCN n ∧ (t ≡ ⌜ n ⌝)

prop2 : forall {σ} -> (t : Tm σ) -> SC t
prop2 K       = sig Kⁿ (tr rK (prop1 Kⁿ) refl) 
prop2 S       = sig Sⁿ (tr rS (prop1 Sⁿ) refl) 
prop2 (t $ u) with prop2 t          | prop2 u
prop2 (t $ u) | sig f (tr rf sf cf) | sig a (tr ra sa ca) with sf a sa
prop2 (t $ u) | sig f (tr rf sf cf) | sig a (tr ra sa ca) | sig v (tr rv sv cv)
  = sig v (tr (r$ rf ra rv) sv (trans ($≡ cf ca) cv))
