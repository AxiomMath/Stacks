module

public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.CoordinateChoice

/-!
# The overlap of a coordinate chart with a cutting chart

[Stacks, Tag 02NP] covers `X` by the charts `α⁻¹(D₊(f_j))` of standard opens of homogeneous
elements of positive degree inside `α.coborderRange`, and separately by the charts
`α⁻¹(D₊(y_i))` of degree-one coordinates, where the morphism to `ℙⁿ_S` is pinned. The two covers
have to be compared, and the comparison is made by cutting with the product: `y_i f_j` is again
homogeneous of positive degree, its standard open is `D₊(y_i) ⊓ D₊(f_j)` and therefore still lies
in `α.coborderRange`, so the overlap chart inherits everything the cutting chart has — it is
affine, `α` restricts to a closed immersion over it, and its sections are fractions.

This file records that inheritance, and — the point of the file — matches it with the *other*
spelling of the same open: `Stacks.ProjChartBasicOpen.basicOpen_appLE_awayToSection_mk` exhibits
the overlap as the nonvanishing locus, inside the coordinate chart `α⁻¹(D₊(y_i))`, of the inverse
image of the degree-zero fraction `y_i f_j / y_i^{1 + d_j}`. It is that spelling the morphism to
projective space produces, and the affineness proved here is stated at it.

## Main results

* `Stacks.OverlapChart.basicOpen_mul_le_left` and
  `Stacks.OverlapChart.basicOpen_mul_le_coborderRange`: the standard open of the product lies
  inside the coordinate's standard open, and inside the coborder of the range.
* `Stacks.OverlapChart.preimage_basicOpen_inf_mul`: **the overlap is the chart of the product**,
  `α⁻¹(D₊(y)) ⊓ α⁻¹(D₊(y f)) = α⁻¹(D₊(y f))`.
* `Stacks.OverlapChart.isAffineOpen_preimage_basicOpen_mul`,
  `Stacks.OverlapChart.isClosedImmersion_restrict_basicOpen_mul` and
  `Stacks.OverlapChart.surjective_awayToChart_mul`: the overlap chart is affine, `α` restricts to
  a closed immersion over it, and every one of its sections is a fraction `b / (y f)^k`.
* `Stacks.OverlapChart.isAffineOpen_basicOpen_appLE_mul`: **the affineness at the spelling the
  coordinate cut produces**, as the nonvanishing locus inside `α⁻¹(D₊(y))` of the inverse image
  of `y f / y^{1 + d}`.

## References

* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u w

namespace Stacks.OverlapChart

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (α : X ⟶ AlgebraicGeometry.Proj 𝒜)

/-! ### The standard open of the product -/

/-- **The standard open of `y f` lies inside that of `y`.** -/
theorem basicOpen_mul_le_left (y f : A) :
    AlgebraicGeometry.Proj.basicOpen 𝒜 (y * f) ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 y :=
  AlgebraicGeometry.Proj.basicOpen_mono 𝒜 y (y * f) ⟨f, rfl⟩

/-- **The standard open of `y f` lies inside that of `f`.** -/
theorem basicOpen_mul_le_right (y f : A) :
    AlgebraicGeometry.Proj.basicOpen 𝒜 (y * f) ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f :=
  AlgebraicGeometry.Proj.basicOpen_mono 𝒜 f (y * f) ⟨y, mul_comm y f⟩

/-- **The overlap of the coordinate chart with the chart of `y f` is the chart of `y f`.** -/
theorem preimage_basicOpen_inf_mul (y f : A) :
    (α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 y) ⊓
        (α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (y * f)) =
      α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (y * f) :=
  inf_eq_right.mpr fun _ hx => basicOpen_mul_le_left 𝒜 y f hx

/-! ### What the overlap chart inherits -/

section Immersion

variable [IsImmersion α] {y f : A} {d : ℕ}

/-- **Cutting with the product stays inside the coborder of the range**, so the overlap chart is
a chart of the same kind as the cutting chart. -/
theorem basicOpen_mul_le_coborderRange (y f : A)
    (hcob : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ α.coborderRange) :
    AlgebraicGeometry.Proj.basicOpen 𝒜 (y * f) ≤ α.coborderRange :=
  (basicOpen_mul_le_right 𝒜 y f).trans hcob

/-- **The overlap chart is affine.** `y f` is homogeneous of degree `1 + d > 0` and its standard
open lies in the coborder of the range, so this is
`Stacks.CoordinateChoice.isAffineOpen_preimage_basicOpen` at `y f`. -/
theorem isAffineOpen_preimage_basicOpen_mul (hy : y ∈ 𝒜 1) (hf : f ∈ 𝒜 d)
    (hcob : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ α.coborderRange) :
    IsAffineOpen (α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (y * f)) :=
  Stacks.CoordinateChoice.isAffineOpen_preimage_basicOpen 𝒜 α
    (SetLike.mul_mem_graded hy hf) (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 d))
    (basicOpen_mul_le_coborderRange 𝒜 α y f hcob)

/-- **The immersion restricts to a closed immersion over the overlap chart.** -/
theorem isClosedImmersion_restrict_basicOpen_mul
    (hcob : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ α.coborderRange) :
    IsClosedImmersion (α ∣_ AlgebraicGeometry.Proj.basicOpen 𝒜 (y * f)) :=
  Stacks.CoordinateChoice.isClosedImmersion_restrict_basicOpen 𝒜 α
    (basicOpen_mul_le_coborderRange 𝒜 α y f hcob)

/-- **Every section of the overlap chart is a fraction `b / (y f)^k`.** -/
theorem surjective_awayToChart_mul (hy : y ∈ 𝒜 1) (hf : f ∈ 𝒜 d)
    (hcob : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ α.coborderRange) :
    Function.Surjective (Stacks.CoordinateChoice.awayToChart 𝒜 α (y * f)) :=
  Stacks.CoordinateChoice.surjective_awayToChart 𝒜 α (SetLike.mul_mem_graded hy hf)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 d))
    (basicOpen_mul_le_coborderRange 𝒜 α y f hcob)

/-- **The overlap is affine at the spelling the coordinate cut of [Stacks, Tag 02NP]
produces it.** Inside the coordinate chart `α⁻¹(D₊(y))` the overlap with `α⁻¹(D₊(y f))` is the
nonvanishing locus of the inverse image along `α` of the degree-zero fraction `y f / y^{1 + d}`
of `A₍y₎`, by `Stacks.ProjChartBasicOpen.basicOpen_appLE_awayToSection_mk`; this says that open
is affine.

It is the form the finishing step needs: `AlgebraicGeometry.Scheme.preimage_basicOpen` matches
that nonvanishing locus with the preimage of a standard open of the chart `D₊(T_i)` of `ℙⁿ_S`,
and `Stacks.FiniteFactorization.isClosedImmersion_morphismRestrict` asks precisely for an affine
open of the target whose preimage is affine. -/
theorem isAffineOpen_basicOpen_appLE_mul (hy : y ∈ 𝒜 1) (hf : f ∈ 𝒜 d)
    (hcob : AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ α.coborderRange)
    (hmul : y * f ∈ 𝒜 ((1 + d) • 1)) :
    IsAffineOpen (X.basicOpen (α.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 y)
      (α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 y) le_rfl
      ((AlgebraicGeometry.Proj.awayToSection 𝒜 y).hom
        (Away.mk 𝒜 hy (1 + d) (y * f) hmul)))) := by
  rw [Stacks.ProjChartBasicOpen.basicOpen_appLE_awayToSection_mk 𝒜 α hy Nat.one_pos (1 + d)
      (y * f) hmul le_rfl, preimage_basicOpen_inf_mul]
  exact isAffineOpen_preimage_basicOpen_mul 𝒜 α hy hf hcob

end Immersion

end Stacks.OverlapChart

end
