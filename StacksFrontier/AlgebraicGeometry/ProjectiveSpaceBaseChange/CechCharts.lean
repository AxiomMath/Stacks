module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic

/-!
# The standard charts of projective space under base change

The `n + 1` standard charts of `ℙⁿ_R` are pulled back from the integral model, and the
base-change morphism `ℙⁿ_B ⟶ ℙⁿ_A` of a ring map `A ⟶ B` is the identity on that model. So the
charts of `ℙⁿ_B` are exactly the preimages of the charts of `ℙⁿ_A`, and the same holds for every
finite intersection of charts. Over an intersection of charts — an affine open, by
`Stacks.ProjectiveCohomology.isAffineOpen_iInf_chart` — the canonical base-change map on the
sections of the structure sheaf is then an isomorphism whenever `A ⟶ B` is flat.

## Main results

* `Stacks.ProjectiveCohomology.preimage_chart` and
  `Stacks.ProjectiveCohomology.preimage_iInf_chart`: the charts and their finite intersections
  are stable under base change.
* `Stacks.ProjectiveCohomology.isIso_pushoutSection_iInf_chart`: over an intersection of
  standard charts, `Γ(ℙⁿ_A, U) ⊗_A B ≅ Γ(ℙⁿ_B, U_B)` for a flat `A ⟶ B`.
* `Stacks.ProjectiveCohomology.compactSpace_projectiveSpaceOverRing` and
  `Stacks.ProjectiveCohomology.quasiSeparatedSpace_projectiveSpaceOverRing`: projective space
  over a ring is quasi-compact and quasi-separated.

## Implementation notes

The two charts are *equal* opens, not merely isomorphic: `Stacks.ProjectiveCohomology.chart` is
defined as a preimage along `AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse`, and
`AlgebraicGeometry.projectiveSpaceOverMap_snd` says the base-change morphism composed with that
projection *is* the projection on the smaller base.

These are the geometric half of the degreewise input to the Čech comparison of [Stacks, Tag 02KH]
part (2) for projective space, which `Stacks.ProjectiveCohomology.cechBaseChangeIsoChart`
assembles.

## References

* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.ProjectiveCohomology

variable (n : ℕ) {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-! ### The charts are stable under base change -/

/-- **The standard charts of projective space are stable under base change.** The `i`-th chart of
`ℙⁿ_B` is the preimage of the `i`-th chart of `ℙⁿ_A` along the base-change morphism. -/
public theorem preimage_chart (i : Fin (n + 1)) :
    projectiveSpaceOverRingMap n φ ⁻¹ᵁ chart n A i = chart n B i := by
  change (projectiveSpaceOverMap n (Spec.map φ) ≫
      projectiveSpaceOver.toIntegralAtUniverse n (Spec A)) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) = _
  rw [projectiveSpaceOverMap_snd]
  rfl

/-- **Finite intersections of standard charts are stable under base change.** -/
public theorem preimage_iInf_chart {r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    projectiveSpaceOverRingMap n φ ⁻¹ᵁ (⨅ k, chart n A (s k)) = ⨅ k, chart n B (s k) := by
  rw [preimage_iInf, iInf_congr fun k => preimage_chart n φ (s k)]

/-- The universe-lifted form of `Stacks.ProjectiveCohomology.preimage_chart`, for the index type
that [Stacks, Tag 01XD] requires. -/
public theorem preimage_chartAtUniverse (i : ULift.{u} (Fin (n + 1))) :
    projectiveSpaceOverRingMap n φ ⁻¹ᵁ chartAtUniverse n A i = chartAtUniverse n B i :=
  preimage_chart n φ i.down

/-- The universe-lifted form of `Stacks.ProjectiveCohomology.preimage_iInf_chart`. -/
public theorem preimage_iInf_chartAtUniverse {r : ℕ}
    (s : Fin (r + 1) → ULift.{u} (Fin (n + 1))) :
    projectiveSpaceOverRingMap n φ ⁻¹ᵁ (⨅ k, chartAtUniverse n A (s k)) =
      ⨅ k, chartAtUniverse n B (s k) :=
  preimage_iInf_chart n φ fun k => (s k).down

/-! ### Projective space is quasi-compact and quasi-separated -/

/-- Projective space over a ring is quasi-compact. -/
public theorem compactSpace_projectiveSpaceOverRing (R : CommRingCat.{u}) :
    CompactSpace (projectiveSpaceOverRing n R) :=
  QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver n (Spec R) ↘ Spec R)

/-- Projective space over a ring is quasi-separated. -/
public theorem quasiSeparatedSpace_projectiveSpaceOverRing (R : CommRingCat.{u}) :
    QuasiSeparatedSpace (projectiveSpaceOverRing n R) :=
  have := isSeparated_projectiveSpaceOver n (Spec R)
  inferInstance

/-! ### Degree-zero base change over an intersection of charts -/

/-- **Degree-zero flat base change over an intersection of standard charts.** For a flat ring
map `A ⟶ B` and a finite family of standard charts of `ℙⁿ_A`, the canonical map

  `Γ(ℙⁿ_A, ⋂ Uᵢ) ⊗_A B ⟶ Γ(ℙⁿ_B, ⋂ (Uᵢ)_B)`

is an isomorphism, the square being the cartesian square
`AlgebraicGeometry.isPullback_projectiveSpaceOverMap`. -/
public theorem isIso_pushoutSection_iInf_chart [Flat (Spec.map φ)] {r : ℕ}
    (s : Fin (r + 1) → Fin (n + 1)) :
    IsIso (pushoutSection (isPullback_projectiveSpaceOverMap n (Spec.map φ))
      (US := ⊤) (UT := ⊤) (UX := ⨅ k, chart n A (s k))
      (UY := ⨅ k, chart n B (s k)) (by simp) (by simp)
      (by
        rw [Scheme.Hom.preimage_top, inf_top_eq]
        exact (preimage_iInf_chart n φ s).symm)) :=
  isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _
    (isAffineOpen_top _) (isAffineOpen_top _)
    (isAffineOpen_iInf_chart n A s).isCompact
    (isAffineOpen_iInf_chart n A s).isQuasiSeparated

end Stacks.ProjectiveCohomology

end
