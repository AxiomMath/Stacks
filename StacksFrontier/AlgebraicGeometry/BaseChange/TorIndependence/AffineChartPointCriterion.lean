module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartPrimeCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.LocalizationDetectsIso

/-!
# Condition (2) of Stacks 0DJ8 at one chart, read at the primes of `𝒪_{X'}(U')`

`AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_isIso_ringBaseChangeCohomologyMap`
reduces condition (2) of Stacks 0DJ8 at a Cartesian affine-open chart to the invertibility, in
every degree, of the ring-level map of Stacks 0DJ7 for the chart's square of coordinate rings.
That map is a map of `𝒪_{X'}(U')`-modules, so the local criterion applies to it: it is invertible
exactly when its extension of scalars to the localization at every prime is invertible.

This is the shape in which the affine reduction of the source proof meets the pointwise condition
(1): the pointwise map of Stacks 0DJ7 at a point `x'` of `U'` is a map of `𝒪_{X',x'}`-modules, and
`𝒪_{X',x'}` is the localization of `𝒪_{X'}(U')` at the prime that `x'` names.

## Main results

* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_prime`: condition (2) at a chart
  is the invertibility, in every degree and at every prime of `𝒪_{X'}(U')`, of the extension of
  scalars of the ring-level map of Stacks 0DJ7 to the localization at that prime.

## Implementation notes

The statement is indexed by primes rather than by points of `Spec 𝒪_{X'}(U')`, even though
condition (1) is indexed by points: the two indices are the same on the nose, and the prime form
is what makes the `Localization.AtPrime` instance available to the statement.

No tag attribute is placed here: this is a restatement of the existing
`isIso_comparison_iff_forall_isIso_ringBaseChangeCohomologyMap`, which carries the tag already,
through the local criterion of [Stacks, Tag 00HN].

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Condition (2) of Stacks 0DJ8 at one chart, read at the primes.** The comparison map
of a Cartesian affine-open chart is an isomorphism exactly when, in every degree and at every
prime `p` of `𝒪_{X'}(U')`, the ring-level map of Stacks 0DJ7 for the chart's square of coordinate
rings becomes invertible after extension of scalars to the localization at `p`.

Two steps: the existing reduction of condition (2) to invertibility of that ring-level map in
every degree, and the local criterion of [Stacks, Tag 00HN] applied to it as a map of
`𝒪_{X'}(U')`-modules. -/
public theorem isIso_comparison_iff_forall_prime (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    (IsIso (ch.comparison K K' φ) ↔
      ∀ (n : ℤ) (p : Ideal ch.A') (_ : p.IsPrime),
        IsIso ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap ch.A' (Localization.AtPrime p))).map
          (RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral
            (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K)
            ((affineDerivedSections ch.incU').obj K')
            (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n))) := by
  rw [ch.isIso_comparison_iff_forall_isIso_ringBaseChangeCohomologyMap K K' φ]
  exact forall_congr' fun _ =>
    Stacks.StalkLocalization.isIso_iff_forall_isIso_extendScalars_atPrime _

end BaseChangeChart

end AlgebraicGeometry

end
