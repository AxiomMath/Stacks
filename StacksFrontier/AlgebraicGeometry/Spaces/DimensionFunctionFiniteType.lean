module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.TranscendenceDegreeFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint

/-!
# The dimension function induced on an algebraic space of finite type over the base

Let `B` be a decent, locally Noetherian, universally catenary algebraic space carrying a
dimension function `δ`. For a decent algebraic space `X` locally of finite type over `B`,
Stacks 0EDN asserts that the function sending a point `x` to `δ (f x)` plus the
transcendence degree of `x` over `f x` is again a dimension function.

This module defines that function and proves that the relative transcendence degree entering
it is finite at every point of a morphism locally of finite type. The theorem itself is
`AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue`, in
`StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionFunction`, which imports this module.

## Main definitions

* `AlgebraicGeometry.Space.inducedDimensionValue` is the value prescribed by the base
  dimension function and the relative transcendence degree.

## Main results

* `AlgebraicGeometry.Space.exists_finite_transcendenceDegreeAt` gives finiteness of the
  relative transcendence degree at each point of a morphism locally of finite type.
* `AlgebraicGeometry.Space.inducedDimensionValue_eq` evaluates the induced function against
  any specified relative transcendence degree.

## Implementation notes

The relative transcendence degree of Tag 04NM is a predicate specifying a value in `ℕ∞`
rather than a function, so the induced function chooses a natural-number value when one
exists and falls back on `0` otherwise. The fallback is never taken for a morphism locally
of finite type, by `exists_finite_transcendenceDegreeAt`.

Finiteness is proved by choosing one pointed pair of étale charts at the point, where the
underlying morphism of schemes is locally of finite type and the residue-field transcendence
degree is finite by
`AlgebraicGeometry.MorphismOfGerms.exists_natCast_hasResidueFieldTranscendenceDegree`, and
then transporting the resulting value to every other pointed chart with
`AlgebraicGeometry.Space.chart_property_iff_of_pointedCharts`. When no pointed chart exists
the every-chart condition holds vacuously, so no algebraic-space hypothesis is needed.

The pointwise formula needs the chosen value to agree with any other value satisfying the
predicate. The algebraic-space hypotheses supply a pointed chart by
`AlgebraicGeometry.Space.exists_etaleChartAtPoint`, and on that one chart the germ-level
degree is unique by
`AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique`; without a
chart the every-chart condition is satisfied by every value and the formula is false.

## References

* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **The function of Stacks 0EDN.** The value at `x` of the function induced by a dimension
function `δ` on the target: `δ` at the image of `x`, plus the finite relative transcendence
degree at `x`. The fallback value is irrelevant for a morphism locally of finite type, by
`AlgebraicGeometry.Space.exists_finite_transcendenceDegreeAt`. That it is a dimension function
is `AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue`. -/
noncomputable def inducedDimensionValue (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (δ : points B S hS Y → ℤ) (f : X ⟶ Y) (x : points B S hS X) : ℤ := by
  classical
  exact δ (pointsMap B S hS X f x) +
    (if h : ∃ n : ℕ, HasTranscendenceDegreeAt B S hS f x n
      then ((Classical.choose h : ℕ) : ℤ) else 0)

/-- **Finiteness of the relative degree.** A morphism of algebraic spaces locally of finite type
has a finite relative transcendence degree at every point of its source. -/
theorem exists_finite_transcendenceDegreeAt (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) :
    ∃ n : ℕ, HasTranscendenceDegreeAt B S hS f x n := by
  classical
  by_cases hc : Nonempty (EtaleChartAtPoint B S hS f x)
  · obtain ⟨c⟩ := hc
    have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
      hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
    obtain ⟨n, hn⟩ :=
      MorphismOfGerms.exists_natCast_hasResidueFieldTranscendenceDegree
        ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)
    refine ⟨n, fun d => ?_⟩
    exact (chart_property_iff_of_pointedCharts B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} (n : ℕ∞))
      (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget
        (n : ℕ∞)) f x c d).mp hn
  · exact ⟨0, fun c => absurd (Nonempty.intro c) hc⟩

/-- **The pointwise formula.** The induced value at `x` is `δ` at the image of `x` plus the
relative transcendence degree at `x`, for any value `r` of that degree. -/
theorem inducedDimensionValue_eq (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (δ : points B S hS Y → ℤ) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) (r : ℕ∞)
    (hr : HasTranscendenceDegreeAt B S hS f x r) :
    inducedDimensionValue B S hS δ f x = δ (pointsMap B S hS X f x) + (r.toNat : ℤ) := by
  classical
  have h : ∃ n : ℕ, HasTranscendenceDegreeAt B S hS f x n :=
    exists_finite_transcendenceDegreeAt B S hS f hf x
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hX hY f x
  have hru : ((Classical.choose h : ℕ) : ℕ∞) = r :=
    MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique
      (Classical.choose_spec h c) (hr c)
  unfold inducedDimensionValue
  rw [dite_eq_left h, ← hru, ENat.toNat_natCast]

end AlgebraicGeometry.Space

end
