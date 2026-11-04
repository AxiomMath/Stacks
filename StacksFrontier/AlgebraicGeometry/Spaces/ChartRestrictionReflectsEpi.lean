module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiOver
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalDual
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# Restriction to a surjective étale chart reflects epimorphisms of modules

Let `F` be an algebraic space over a scheme `S` and let `U` be an étale chart of `F` whose
structure morphism `yoneda.obj U ⟶ F` is surjective on points. This file proves that a morphism of
`𝒪_F`-modules whose restriction to `U` is an epimorphism is itself an epimorphism, so that
restriction to a surjective étale chart **reflects** epimorphisms. The restriction is restriction
to the slice of the small étale site at the chart, `SheafOfModules.over`, which is the same functor
whose effect on quasi-coherence is condition (3) of Stacks 03M0 in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective`.

## Main results

* `Stacks.SheafOfModules.EpiMono.epi_of_coversTop_over`: **restriction to the slices of a family of
  objects covering the final object jointly reflects epimorphisms of sheaves of modules.** The
  converse of `Stacks.SheafOfModules.EpiMono.epi_over`.
* `AlgebraicGeometry.Space.epi_of_epi_over_of_isSurjective` and
  `AlgebraicGeometry.Space.epi_over_iff_of_isSurjective`: **restriction to one surjective étale
  chart of an algebraic space reflects epimorphisms of `𝒪_F`-modules**, and the two-sided form.
* `AlgebraicGeometry.Space.modules_epi_of_surjective_val_app_over_of_isSurjective`: the
  section-level sufficient condition — a morphism of `𝒪_F`-modules which is surjective on the
  sections over every étale chart admitting a morphism to a surjective étale chart is an
  epimorphism.

## Implementation notes

The chart restriction here is `SheafOfModules.over`, restriction along `CategoryTheory.Over.forget`
to the slice of the small étale site of `F` at the chart. It is *not*
`AlgebraicGeometry.Space.restrictToChartSchemeFunctor`, which lands in sheaves of modules on the
Zariski site of the scheme underlying the chart. The statements hold for an arbitrary morphism of
`𝒪_F`-modules; no quasi-coherence is assumed.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u u'

namespace Stacks.SheafOfModules.EpiMono

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **Restriction to the slices of a family of objects covering the final object jointly
reflects epimorphisms of sheaves of modules.**  If every object of the site is covered by the
objects of a family `Y` and the restriction of `p` to the slice site over each `Y i` is an
epimorphism, then `p` is an epimorphism. This is the converse of
`Stacks.SheafOfModules.EpiMono.epi_over`. -/
theorem epi_of_coversTop_over [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{t}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{t}]
    {M N : SheafOfModules.{t} R} (p : M ⟶ N) {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (h : ∀ i, Epi (p.over (Y i))) : Epi p :=
  epi_of_isLocallySurjective p
    (Presheaf.isLocallySurjective_of_coversTop J
      ((PresheafOfModules.toPresheaf R.obj).map p.val) hY
      fun i => have := h i; isLocallySurjective_of_epi (p.over (Y i)))

end Stacks.SheafOfModules.EpiMono

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Sheafification of presheaves of abelian groups on every slice of the small étale site of an
algebraic space, phrased for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
private instance hasSheafify_smallEtaleRingedSite_over :
    ∀ X : (smallEtaleRingedSite B S hS F hF).C,
      HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over X) AddCommGrpCat.{u} := by
  change ∀ X : SmallEtale B S hS F,
    HasSheafify ((SmallEtale.topology B S hS F).over X) AddCommGrpCat.{u}
  infer_instance

/-- Sheafification of presheaves of abelian groups on the small étale site of an algebraic
space, phrased for the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
private instance hasSheafify_smallEtaleRingedSite :
    HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} := by
  change HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u}
  infer_instance

/-- Local equivalences of presheaves of abelian groups on the small étale site of an algebraic
space are the locally bijective morphisms, phrased for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
private instance wEqualsLocallyBijective_smallEtaleRingedSite :
    (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  change (SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

/-- **Restriction to a surjective étale chart reflects epimorphisms of `𝒪_F`-modules.**  A
morphism of `𝒪_F`-modules whose restriction to the slice of the small étale site at an étale
chart with surjective structure morphism is an epimorphism is itself an epimorphism. -/
theorem epi_of_epi_over_of_isSurjective {M N : Modules.{u, u} B S hS F hF} (p : M ⟶ N)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom)
    (h : Epi (p.over U)) : Epi p :=
  Stacks.SheafOfModules.EpiMono.epi_of_coversTop_over p
    (SmallEtale.coversTop_of_isSurjective B S hS F hF U hsurj) fun _ => h

/-- **Epimorphy of a morphism of `𝒪_F`-modules is tested on one surjective étale chart.** A
morphism of `𝒪_F`-modules is an epimorphism if and only if its restriction to the slice of the
small étale site at an étale chart with surjective structure morphism is one. -/
theorem epi_over_iff_of_isSurjective {M N : Modules.{u, u} B S hS F hF} (p : M ⟶ N)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom) :
    Epi p ↔ Epi (p.over U) :=
  ⟨fun _ => Stacks.SheafOfModules.EpiMono.epi_over p U,
    epi_of_epi_over_of_isSurjective B S hS F hF p U hsurj⟩

/-- **A morphism of `𝒪_F`-modules which is surjective on the sections over every étale chart
lying over a surjective étale chart is an epimorphism.** -/
theorem modules_epi_of_surjective_val_app_over_of_isSurjective
    {M N : Modules.{u, u} B S hS F hF} (p : M ⟶ N)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom)
    (h : ∀ (V : (smallEtaleRingedSite B S hS F hF).C), (V ⟶ U) →
      Function.Surjective (p.val.app (op V))) :
    Epi p := by
  refine epi_of_epi_over_of_isSurjective B S hS F hF p U hsurj
    (Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
      (Presheaf.isLocallySurjective_of_surjective _ _ fun V => ?_))
  exact h V.unop.left V.unop.hom

end AlgebraicGeometry.Space

end
