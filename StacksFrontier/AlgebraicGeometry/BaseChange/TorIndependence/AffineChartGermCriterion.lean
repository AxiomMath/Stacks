module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartPointCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartStalkRings

/-!
# Condition (2) of Stacks 0DJ8 at one chart, read at the local rings of `U'`

`AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_prime` reads condition (2) of
Stacks 0DJ8 at a chart as the invertibility, in every degree and at every prime `p` of
`𝒪_{X'}(U')`, of the extension of scalars of the ring-level map of Stacks 0DJ7 to
`Localization.AtPrime p`. The pointwise condition (1) is stated instead over the local ring
`𝒪_{X', x'}`, which `𝒪_{X'}(U') → 𝒪_{Spec 𝒪_{X'}(U'), y}` presents as that localization. This
module restates the criterion over the germ maps, so that no comparison between
`Localization.AtPrime p` and the local ring of the scheme is left for the consumer.

## Main results

* `Stacks.StalkLocalization.isIso_extendScalars_germ_iff_bijective_localizedMap`: extension of
  scalars along the germ map of `Spec A` at `y` is invertible on a map of `A`-modules exactly when
  that map's localization at `y` is bijective.
* `Stacks.StalkLocalization.isIso_iff_forall_isIso_extendScalars_germ`: a map of `A`-modules is
  invertible exactly when all of its base changes along the germ maps of `Spec A` are.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_germ`: condition (2) at a chart,
  read at the local rings of the points of `Spec 𝒪_{X'}(U')`.

## Implementation notes

The germ map exhibits the stalk as the localization at the prime of the point —
`AlgebraicGeometry.isLocalization_atPrime_specGermRingHom` — so `𝒪_{Spec A, y} ⊗_A M` is the
localization of `M`, and the base change of a map along the germ map is its localized map. That is
`AlgebraicGeometry.bijective_localizedModule_map_iff_bijective_lTensor`; the only step left is
that the underlying function of `(ModuleCat.extendScalars _).map F` is `LinearMap.lTensor`, which
holds by `rfl`.

Points are bound as `PrimeSpectrum ↑A` rather than as `↥(Spec A)`, because `y.asIdeal.IsPrime` is
not found by instance search at the second spelling; the two types are definitionally equal, so a
consumer passes a point unchanged either way. This follows
`AlgebraicGeometry.isLocalization_atPrime_specGermRingHom`, which binds the point the same way for
the same reason.

Everything below is a restatement of
`AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_isIso_ringBaseChangeCohomologyMap`
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

namespace Stacks.StalkLocalization

/-- **Extension of scalars along a germ map is invertible exactly when the localized map is
bijective.** The germ map `A → 𝒪_{Spec A, y}` is the localization at the prime of `y`, so base
change along it is localization of modules. -/
public theorem isIso_extendScalars_germ_iff_bijective_localizedMap (A : CommRingCat.{u})
    (y : PrimeSpectrum (A : Type u)) {M N : ModuleCat.{u} (A : Type u)} (F : M ⟶ N) :
    IsIso ((ModuleCat.extendScalars.{u, u, u} (AlgebraicGeometry.specGermRingHom A y)).map F) ↔
      Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl F.hom) := by
  let := (AlgebraicGeometry.specGermRingHom A y).toAlgebra
  rw [AlgebraicGeometry.bijective_localizedModule_map_iff_bijective_lTensor A y F.hom,
    ConcreteCategory.isIso_iff_bijective]
  exact Iff.of_eq (congrArg Function.Bijective (funext fun _ => rfl))

/-- **A map of modules is invertible exactly when all of its base changes along the germ maps
are.** This is [Stacks, Tag 00HN] (6) read through the germ maps of `Spec A`. -/
public theorem isIso_iff_forall_isIso_extendScalars_germ (A : CommRingCat.{u})
    {M N : ModuleCat.{u} (A : Type u)} (F : M ⟶ N) :
    IsIso F ↔ ∀ y : PrimeSpectrum (A : Type u),
      IsIso ((ModuleCat.extendScalars.{u, u, u}
        (AlgebraicGeometry.specGermRingHom A y)).map F) := by
  rw [ConcreteCategory.isIso_iff_bijective, bijective_iff_forall_bijective_localizedMap' F.hom]
  exact forall_congr' fun y =>
    (isIso_extendScalars_germ_iff_bijective_localizedMap A y F).symm

end Stacks.StalkLocalization

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Condition (2) of Stacks 0DJ8 at one chart, read at the local rings of `U'`.** The comparison
map of a Cartesian affine-open chart is an isomorphism exactly when, in every degree and at every
point `y` of `Spec 𝒪_{X'}(U')`, the ring-level map of Stacks 0DJ7 for the chart's square of
coordinate rings becomes invertible after extension of scalars along the germ map at `y`.

This is the form the comparison with condition (1) consumes: the pointwise map of Stacks 0DJ7 at
the point of `X'` that `y` names is stated over the local ring `𝒪_{X', x'}`, and the germ map is
what presents that local ring. -/
public theorem isIso_comparison_iff_forall_germ (ch : BaseChangeChart f g f' g')
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
      ∀ (n : ℤ) (y : PrimeSpectrum (ch.A' : Type u)),
        IsIso ((ModuleCat.extendScalars.{u, u, u} (specGermRingHom ch.A' y)).map
          (RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral
            (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K)
            ((affineDerivedSections ch.incU').obj K')
            (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n))) := by
  rw [ch.isIso_comparison_iff_forall_isIso_ringBaseChangeCohomologyMap K K' φ]
  exact forall_congr' fun _ =>
    Stacks.StalkLocalization.isIso_iff_forall_isIso_extendScalars_germ ch.A' _

end BaseChangeChart

end AlgebraicGeometry

end
