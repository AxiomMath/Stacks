module

public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul contracting homotopy with coefficients

`StacksFrontier.LinearAlgebra.ExteriorPower.Koszul` builds the contraction
`exteriorPower.contraction φ n` against a linear functional, the left wedge multiplication
`exteriorPower.wedgeLeft e n`, and the Koszul identity

`ι_φ ∘ (e ∧ ·) + (e ∧ ·) ∘ ι_φ = φ e • id`

on the exterior powers of `M` themselves.  A Koszul complex is frequently used with
coefficients in a second module `N`, as `(⋀[R]^n M) ⊗[R] N`, and then the two operators are
`LinearMap.rTensor N` of the above.  This module records that the identity survives, which is
the only thing a coefficient Koszul complex needs beyond the bare one.

Nothing here is specific to the exterior algebra: `LinearMap.rTensor N` is an additive,
`R`-linear, composition-preserving functor, so the identity transports term by term.  It is
stated for the Koszul operators because that is the shape consumers ask for, and because
without it each consumer re-derives the transport inline.

## Main results

* `exteriorPower.rTensor_contraction_comp_rTensor_wedgeLeft_add` — the Koszul identity on
  `(⋀[R]^(n + 1) M) ⊗[R] N`, as an identity of linear maps.
* `exteriorPower.rTensor_contraction_rTensor_wedgeLeft_add_rTensor_wedgeLeft_rTensor_contraction`
  — the same evaluated at a point, with `φ e = 1`, which is the contracting homotopy.
-/

@[expose] public noncomputable section

namespace exteriorPower

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

open scoped TensorProduct

/-- An endomorphism equal to `c • id` with `c = 1` fixes every point. -/
private theorem apply_eq_of_eq_smul_id {P : Type*} [AddCommGroup P] [Module R P]
    {f : P →ₗ[R] P} {c : R} (hc : c = 1) (h : f = c • LinearMap.id) (x : P) : f x = x := by
  simp [h, hc]

/-- **The Koszul identity with coefficients.**  Tensoring on the right by `N` carries the
anticommutator of the contraction against `φ` and the wedge by `e` to multiplication by the
scalar `φ e` on `(⋀[R]^(n + 1) M) ⊗[R] N`. -/
@[ega "III 1.1.7" "(f), partial"]
theorem rTensor_contraction_comp_rTensor_wedgeLeft_add (φ : M →ₗ[R] R) (e : M) (n : ℕ) :
    LinearMap.rTensor N (contraction φ (n + 1)) ∘ₗ
          LinearMap.rTensor N (wedgeLeft e (n + 1)) +
        LinearMap.rTensor N (wedgeLeft e n) ∘ₗ LinearMap.rTensor N (contraction φ n) =
      φ e • LinearMap.id (R := R) (M := (⋀[R]^(n + 1) M) ⊗[R] N) := by
  rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_add,
    contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction, LinearMap.rTensor_smul,
    LinearMap.rTensor_id]

/-- **The Koszul contracting homotopy with coefficients**, evaluated at a point.  When `φ e = 1`
the two composites add up to the identity of `(⋀[R]^(n + 1) M) ⊗[R] N`. -/
theorem rTensor_contraction_rTensor_wedgeLeft_add_rTensor_wedgeLeft_rTensor_contraction
    (φ : M →ₗ[R] R) (e : M) (he : φ e = 1) (n : ℕ) (x : (⋀[R]^(n + 1) M) ⊗[R] N) :
    LinearMap.rTensor N (contraction φ (n + 1))
          (LinearMap.rTensor N (wedgeLeft e (n + 1)) x) +
        LinearMap.rTensor N (wedgeLeft e n) (LinearMap.rTensor N (contraction φ n) x) = x := by
  exact apply_eq_of_eq_smul_id he (rTensor_contraction_comp_rTensor_wedgeLeft_add φ e n) x

/-- **Wedging a wedge of vectors by a sum on the left** expands as the sum of the wedges.
`exteriorPower.wedgeLeft` is linear in the exterior power but not bundled as a function of the
vector `e`; on a wedge of vectors this is the multilinearity of `exteriorPower.ιMulti` in its
first slot. -/
theorem wedgeLeft_sum_ιMulti {iota : Type*} (n : ℕ) (s : Finset iota) (e : iota → M)
    (v : Fin n → M) :
    wedgeLeft (∑ u ∈ s, e u) n (ιMulti R n v) =
      ∑ u ∈ s, wedgeLeft (e u) n (ιMulti R n v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, wedgeLeft_ιMulti]
      exact (ιMulti R (n + 1)).map_coord_zero (i := 0) (Fin.cons_zero _ _)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, wedgeLeft_ιMulti, wedgeLeft_ιMulti,
        wedgeLeft_ιMulti]
      exact (ιMulti R (n + 1)).toMultilinearMap.cons_add v (e a) (∑ u ∈ s, e u)

/-- The degree-zero case of the Koszul identity with coefficients: on `(⋀[R]^0 M) ⊗[R] N` the
contraction after wedging with `e` is multiplication by `φ e`. -/
@[ega "III 1.1.7" "partial"]
theorem rTensor_contraction_rTensor_wedgeLeft_zero (φ : M →ₗ[R] R) (e : M) (he : φ e = 1)
    (x : (⋀[R]^0 M) ⊗[R] N) :
    LinearMap.rTensor N (contraction φ 0) (LinearMap.rTensor N (wedgeLeft e 0) x) = x := by
  exact apply_eq_of_eq_smul_id (f := LinearMap.rTensor N (contraction φ 0) ∘ₗ
    LinearMap.rTensor N (wedgeLeft e 0)) he (by
      rw [← LinearMap.rTensor_comp, contraction_comp_wedgeLeft_zero, LinearMap.rTensor_smul,
        LinearMap.rTensor_id]) x

end exteriorPower

end
