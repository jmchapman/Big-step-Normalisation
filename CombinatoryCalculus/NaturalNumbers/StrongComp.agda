module NaturalNumbers.StrongComp where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.BigStep

-- Strong Computability
SCN : forall {σ} -> Nf σ -> Set
SCN {ι}     n = True
SCN {N}     n = True
SCN {σ ⇒ τ} f = forall a -> SCN a -> 
  Σ (Nf τ) \n ->  (f $ⁿ a ⇓ n) ∧ SCN n ∧ (⌜ f ⌝ $ ⌜ a ⌝ ≡ ⌜ n ⌝)

SCR : forall {σ}(z : Nf σ)(f : Nf (N ⇒ σ ⇒ σ))(n : Nf N) ->
      SCN z -> SCN f -> 
      Σ (Nf σ) 
        \n' -> (Rⁿ² z f $ⁿ n ⇓ n') ∧ 
               SCN n' ∧ 
               (R $ ⌜ z ⌝ $ ⌜ f ⌝ $ ⌜ n ⌝ ≡ ⌜ n' ⌝)  
SCR z f zeroⁿ sz sf = sig z (tr rRⁿ²z sz Rzero≡) 
SCR z f (sucⁿ¹ n) sz sf  = 
  sig (σ₀ fnrn)
      (tr (rRⁿ²f (π₀ (σ₁ fn)) (π₀ (σ₁ rn)) (π₀ (σ₁ fnrn))) 
          (π₁ (σ₁ fnrn))
          (trans Rsuc≡ (trans ($≡ (π₂ (σ₁ fn)) (π₂ (σ₁ rn))) (π₂ (σ₁ fnrn)))))
  where
  fn = sf n (record {})
  rn = SCR z f n sz sf
  fnrn = π₁ (σ₁ fn) (σ₀ rn) (π₁ (σ₁ rn)) 

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
prop1 zeroⁿ = record {} 
prop1 sucⁿ = \n _ -> sig (sucⁿ¹ n) (tr rsucⁿ (record {}) refl ) 
prop1 (sucⁿ¹ n) = record {} 
prop1 Rⁿ = \z sz -> 
  sig (Rⁿ¹ z) 
      (tr rRⁿ 
          (\f sf -> sig (Rⁿ² z f)
                          (tr rRⁿ¹
                              (\n _ -> SCR z f n sz sf)
                              refl))
          refl)  
prop1 (Rⁿ¹ z) = \f sf -> 
  sig (Rⁿ² z f) 
      (tr rRⁿ¹ 
          (\n _ -> SCR z f n (prop1 z) sf) 
          refl )  
prop1 (Rⁿ² z f) = \n _ -> SCR z f n (prop1 z) (prop1 f) 

SC : forall {σ} -> Tm σ -> Set
SC {σ} t = Σ (Nf σ) \n -> (t ⇓ n) ∧ SCN n ∧ (t ≡ ⌜ n ⌝)

prop2 : forall {σ} -> (t : Tm σ) -> SC t
prop2 K       = sig Kⁿ (tr rK (prop1 Kⁿ) refl) 
prop2 S       = sig Sⁿ (tr rS (prop1 Sⁿ) refl) 
prop2 (t $ u) with prop2 t          | prop2 u
prop2 (t $ u) | sig f (tr rf sf cf) | sig a (tr ra sa ca) with sf a sa
prop2 (t $ u) | sig f (tr rf sf cf) | sig a (tr ra sa ca) | sig v (tr rv sv cv)
  = sig v (tr (r$ rf ra rv) sv (trans ($≡ cf ca) cv))
prop2 zero    = sig zeroⁿ (tr rzero (record {}) refl)
prop2 suc     = 
  sig sucⁿ 
      (tr rsuc 
          (\n sn -> sig (sucⁿ¹ n) 
                        (tr rsucⁿ (record {}) refl)) 
          refl)
prop2 R       = 
  sig Rⁿ 
      (tr rR  
          (\z sz -> sig (Rⁿ¹ z) 
                        (tr rRⁿ  
                            (\f sf -> sig (Rⁿ² z f) 
                                          (tr rRⁿ¹  
                                              (\n _ -> SCR z f n sz sf)
                                              refl))
                            refl))
          refl)