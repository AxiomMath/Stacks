module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Polynomial rings and extension of the coefficient algebra

Extending the coefficient algebra of a polynomial ring commutes with forming the polynomial
ring: for `R`-algebras `A` and `S` the polynomial ring over `A ⊗[R] S` is `A ⊗[R] S[X]`.

## Main definitions

* `Algebra.TensorProduct.polynomialRight`: the comparison isomorphism
  `(A ⊗[R] S)[X] ≃ₐ[R] A ⊗[R] S[X]`.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra.TensorProduct

variable (R A S : Type u) [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

/-- The polynomial ring over `A ⊗[R] S` is the extension of the polynomial ring over `S` along
`R → A`: both are the free `A ⊗[R] S`-module on the powers of the variable. -/
noncomputable def polynomialRight :
    Polynomial (A ⊗[R] S) ≃ₐ[R] A ⊗[R] Polynomial S :=
  AlgEquiv.ofAlgHom
    (Polynomial.eval₂AlgHom (map (AlgHom.id R A) Polynomial.CAlgHom)
      (includeRight Polynomial.X) fun _ ↦ Commute.all _ _)
    (lift (Polynomial.CAlgHom.comp (includeLeft : A →ₐ[R] A ⊗[R] S))
      (Polynomial.mapAlgHom (includeRight : S →ₐ[R] A ⊗[R] S)) fun _ _ ↦ Commute.all _ _)
    (by
      refine Algebra.TensorProduct.ext (AlgHom.ext fun a ↦ ?_) (Polynomial.algHom_ext' ?_ ?_)
      · simp
      · refine AlgHom.ext fun s ↦ ?_
        simp
      · simp)
    (by
      refine Polynomial.algHom_ext' (AlgHom.ext fun z ↦ ?_) ?_
      · induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add]; rw [hx, hy]
        | tmul a s => simp [← Polynomial.C_mul, tmul_mul_tmul]
      · simp [← Algebra.TensorProduct.one_def])

/-- The comparison isomorphism sends a constant polynomial to the corresponding constant. -/
@[simp]
theorem polynomialRight_C (x : A ⊗[R] S) :
    polynomialRight R A S (Polynomial.C x) = map (AlgHom.id R A) Polynomial.CAlgHom x := by
  simp [polynomialRight]

/-- The comparison isomorphism sends the variable to the variable in the right factor. -/
@[simp]
theorem polynomialRight_X :
    polynomialRight R A S Polynomial.X = includeRight Polynomial.X := by
  simp [polynomialRight]

/-- The comparison isomorphism identifies the polynomials whose coefficients lie in the right
factor with the polynomials over the right factor. -/
@[simp]
theorem polynomialRight_map_includeRight (p : Polynomial S) :
    polynomialRight R A S (p.map (includeRight : S →ₐ[R] A ⊗[R] S).toRingHom) =
      includeRight p := by
  have h : (polynomialRight R A S).toAlgHom.comp
        (Polynomial.mapAlgHom (includeRight : S →ₐ[R] A ⊗[R] S)) =
      (includeRight : Polynomial S →ₐ[R] A ⊗[R] Polynomial S) := by
    refine Polynomial.algHom_ext' (AlgHom.ext fun s ↦ ?_) ?_ <;> simp
  exact congrArg (fun k : Polynomial S →ₐ[R] A ⊗[R] Polynomial S ↦ k p) h

/-- Extending the coefficients on the right factor commutes with viewing a tensor product of
the left factor with a constant as a constant polynomial. -/
theorem map_id_mapAlgHom_comp_map_id_CAlgHom {E : Type u} [CommRing E] [Algebra R E]
    (φ : S →ₐ[R] E) (g : A ⊗[R] S) :
    map (AlgHom.id R A) (Polynomial.mapAlgHom φ) (map (AlgHom.id R A) Polynomial.CAlgHom g) =
      map (AlgHom.id R A) Polynomial.CAlgHom (map (AlgHom.id R A) φ g) := by
  induction g using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, ← map_add]
  | tmul a s => simp

end Algebra.TensorProduct

end
