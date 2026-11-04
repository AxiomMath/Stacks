module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Blocks
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison

/-!
# A four-dimensional example of a periodic determinant

Over a field `k`, let `φ` and `ψ` be the endomorphisms of `k^{⊕ 4}` whose matrices are zero
except for the entries `u₁` in position `(2,1)` and `u₂` in position `(4,3)`, respectively `v₂`
in position `(2,3)` and `v₁` in position `(4,1)`, with `u₁, u₂, v₁, v₂` nonzero. The resulting
exact two-periodic complex has periodic determinant `-u₁u₂/(v₁v₂)`.

## Main definitions

* `AlgebraicGeometry.crossPairFirstMatrix` and `AlgebraicGeometry.crossPairSecondMatrix` are
  the two matrices, and `AlgebraicGeometry.crossPairFirst` and
  `AlgebraicGeometry.crossPairSecond` the endomorphisms of `k^{⊕ 4}` they define.

## Main results

* `AlgebraicGeometry.periodicDeterminant_crossPair` computes the periodic determinant of the
  two endomorphisms.

## Implementation notes

Reordering the basis as `e₁, e₃, e₂, e₄` turns the two endomorphisms into block endomorphisms
whose upper-right blocks have determinants `u₁u₂` and `-v₁v₂`; the second sign is the source of
the sign in the answer. As for the block endomorphisms, the exactness and finite-length
witnesses are constructed rather than assumed, and the formula is stated in the residue field.

## References

* [Stacks Project, Tag 02PT](https://stacks.math.columbia.edu/tag/02PT)
-/

@[expose] public section

noncomputable section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v w

/-- Exactness transfers backwards along an isomorphism of periodic complexes. -/
private theorem exact_of_exact_linearEquiv
    {R : Type u} {M : Type v} {M' : Type w} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (e : M ≃ₗ[R] M') (φ ψ : M →ₗ[R] M) (φ' ψ' : M' →ₗ[R] M')
    (hφ : ∀ z, e (φ z) = φ' (e z)) (hψ : ∀ z, e (ψ z) = ψ' (e z))
    (h : Function.Exact φ' ψ') : Function.Exact φ ψ := by
  intro y
  constructor
  · intro hy
    have h0 : ψ' (e y) = 0 := by rw [← hψ y, hy, map_zero]
    obtain ⟨x, hx⟩ := (h (e y)).mp h0
    refine ⟨e.symm x, ?_⟩
    apply e.injective
    rw [hφ (e.symm x), e.apply_symm_apply, hx]
  · rintro ⟨x, rfl⟩
    apply e.injective
    rw [hψ (φ x), hφ x, map_zero]
    exact h.apply_apply_eq_zero (e x)

/-- A finite-dimensional vector space over a field has finite length. -/
private theorem isFiniteLength_pi (k : Type u) [Field k] (n : ℕ) :
    IsFiniteLength k (Fin n → k) := by
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_finrank]
  simp

/-- The `4 × 4` matrix over `k` with entries `u₁` in position `(2,1)` and `u₂` in position
`(4,3)` and all other entries zero. -/
def crossPairFirstMatrix {k : Type u} [Field k] (u₁ u₂ : k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, 0, 0;
     u₁, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, u₂, 0]

/-- The `4 × 4` matrix over `k` with entries `v₂` in position `(2,3)` and `v₁` in position
`(4,1)` and all other entries zero. -/
def crossPairSecondMatrix {k : Type u} [Field k] (v₁ v₂ : k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, 0, 0;
     0, 0, v₂, 0;
     0, 0, 0, 0;
     v₁, 0, 0, 0]

/-- The endomorphism of `k^{⊕ 4}` sending the first basis vector to `u₁` times the second and
the third to `u₂` times the fourth, and the second and fourth to zero. -/
def crossPairFirst {k : Type u} [Field k] (u₁ u₂ : k) : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  (crossPairFirstMatrix u₁ u₂).mulVecLin

/-- The endomorphism of `k^{⊕ 4}` sending the third basis vector to `v₂` times the second and
the first to `v₁` times the fourth, and the second and fourth to zero. -/
def crossPairSecond {k : Type u} [Field k] (v₁ v₂ : k) : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  (crossPairSecondMatrix v₁ v₂).mulVecLin

/-- The diagonal block appearing after reordering the basis for the first endomorphism. -/
private def crossPairFirstBlock {k : Type u} [Field k] (u₁ u₂ : k) : Matrix (Fin 2) (Fin 2) k :=
  !![u₁, 0; 0, u₂]

/-- The antidiagonal block appearing after reordering the basis for the second
endomorphism. -/
private def crossPairSecondBlock {k : Type u} [Field k] (v₁ v₂ : k) :
    Matrix (Fin 2) (Fin 2) k :=
  !![0, v₂; v₁, 0]

private theorem det_crossPairFirstBlock {k : Type u} [Field k] (u₁ u₂ : k) :
    (crossPairFirstBlock u₁ u₂).det = u₁ * u₂ := by
  rw [crossPairFirstBlock, Matrix.det_fin_two_of]
  ring

private theorem det_crossPairSecondBlock {k : Type u} [Field k] (v₁ v₂ : k) :
    (crossPairSecondBlock v₁ v₂).det = -(v₁ * v₂) := by
  rw [crossPairSecondBlock, Matrix.det_fin_two_of]
  ring

/-- Reordering the standard basis of `k^{⊕ 4}` as `e₁, e₃, e₂, e₄` and splitting it in two. -/
private def crossPairReorder (k : Type u) [Field k] :
    (Fin 4 → k) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)) where
  toFun z := (![z 1, z 3], ![z 0, z 2])
  map_add' x y := by apply Prod.ext <;> (funext i; fin_cases i <;> simp)
  map_smul' c x := by apply Prod.ext <;> (funext i; fin_cases i <;> simp)
  invFun p := ![p.2 0, p.1 0, p.2 1, p.1 1]
  left_inv z := by funext i; fin_cases i <;> simp
  right_inv p := by apply Prod.ext <;> (funext i; fin_cases i <;> simp)

private theorem crossPairReorder_first {k : Type u} [Field k] (u₁ u₂ : k) (z : Fin 4 → k) :
    crossPairReorder k (crossPairFirst u₁ u₂ z) =
      upperBlockEndomorphism (crossPairFirstBlock u₁ u₂) (crossPairReorder k z) := by
  apply Prod.ext <;>
    (funext i; fin_cases i <;>
      simp [crossPairReorder, crossPairFirst, crossPairFirstMatrix, crossPairFirstBlock,
        upperBlockEndomorphism, dotProduct, Fin.sum_univ_four,
        Matrix.vecHead, Matrix.vecTail, mul_comm])

private theorem crossPairReorder_second {k : Type u} [Field k] (v₁ v₂ : k) (z : Fin 4 → k) :
    crossPairReorder k (crossPairSecond v₁ v₂ z) =
      upperBlockEndomorphism (crossPairSecondBlock v₁ v₂) (crossPairReorder k z) := by
  apply Prod.ext <;>
    (funext i; fin_cases i <;>
      simp [crossPairReorder, crossPairSecond, crossPairSecondMatrix, crossPairSecondBlock,
        upperBlockEndomorphism, dotProduct, Fin.sum_univ_four,
        Matrix.vecHead, Matrix.vecTail, mul_comm])

/-- **Stacks Project, Tag 02PT.** For nonzero `u₁, u₂, v₁, v₂` in a field `k`, the two
endomorphisms of `k^{⊕ 4}` with single nonzero matrix entries `u₁, u₂` and `v₂, v₁` form an
exact two-periodic complex whose periodic determinant is `-u₁u₂/(v₁v₂)`. -/
@[stacks 02PT]
theorem periodicDeterminant_crossPair {k : Type u} [Field k] (u₁ u₂ v₁ v₂ : kˣ) :
    ∃ (hφψ : Function.Exact (crossPairFirst (u₁ : k) u₂) (crossPairSecond (v₁ : k) v₂))
      (hψφ : Function.Exact (crossPairSecond (v₁ : k) v₂) (crossPairFirst (u₁ : k) u₂))
      (hM : IsFiniteLength k (Fin 4 → k)),
      (periodicDeterminant (crossPairFirst (u₁ : k) u₂) (crossPairSecond (v₁ : k) v₂)
        hφψ hψφ hM : IsLocalRing.ResidueField k) =
        -(IsLocalRing.residue k ((u₁ : k) * u₂) / IsLocalRing.residue k ((v₁ : k) * v₂)) := by
  classical
  let U := crossPairFirstBlock (u₁ : k) u₂
  let V := crossPairSecondBlock (v₁ : k) v₂
  have hU : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det, det_crossPairFirstBlock]
    exact u₁.isUnit.mul u₂.isUnit
  have hV : IsUnit V := by
    rw [Matrix.isUnit_iff_isUnit_det, det_crossPairSecondBlock]
    exact (v₁.isUnit.mul v₂.isUnit).neg
  obtain ⟨hUV, hVU, hM', hformula⟩ :=
    periodicDeterminant_upperBlockEndomorphism (k := k) 2 U V hU hV
  let e := crossPairReorder k
  have hcommU : ∀ z, e (crossPairFirst (u₁ : k) u₂ z) = upperBlockEndomorphism U (e z) :=
    crossPairReorder_first (u₁ : k) u₂
  have hcommV : ∀ z, e (crossPairSecond (v₁ : k) v₂ z) = upperBlockEndomorphism V (e z) :=
    crossPairReorder_second (v₁ : k) v₂
  have hφψ : Function.Exact (crossPairFirst (u₁ : k) u₂) (crossPairSecond (v₁ : k) v₂) :=
    exact_of_exact_linearEquiv e _ _ _ _ hcommU hcommV hUV
  have hψφ : Function.Exact (crossPairSecond (v₁ : k) v₂) (crossPairFirst (u₁ : k) u₂) :=
    exact_of_exact_linearEquiv e _ _ _ _ hcommV hcommU hVU
  refine ⟨hφψ, hψφ, isFiniteLength_pi k 4, ?_⟩
  have htransport :
      periodicDeterminant (crossPairFirst (u₁ : k) u₂) (crossPairSecond (v₁ : k) v₂)
          hφψ hψφ (isFiniteLength_pi k 4) =
        periodicDeterminant (upperBlockEndomorphism U) (upperBlockEndomorphism V)
          hUV hVU hM' :=
    periodicDeterminant_eq_of_linearEquiv _ _ hφψ hψφ _ _ hUV hVU e
      (LinearMap.ext hcommU) (LinearMap.ext hcommV) _ hM'
  rw [htransport, hformula, det_crossPairFirstBlock, det_crossPairSecondBlock]
  simp [div_neg]

end AlgebraicGeometry
