module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiChartModules
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDerived

/-!
# `D_QCoh(O_S)` read on the affine Zariski charts of a scheme

Let `S` be a scheme in a big fppf site `B`, and let the sections of the `O_S`-modules lie in a
universe `max (u + 1) m`. This file identifies `D_QCoh(O_S)` — the full subcategory of the derived
category of `O_S`-modules of the objects with quasi-coherent cohomology sheaves, in any model of
that derived category — with the subcategory of Stacks 0GZS of the lifted chart site
`AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite`: the objects `K` with `Rε_*K` cartesian.

The 0GZS subcategory is that of the objects with cartesian cohomology sheaves
(`AlgebraicGeometry.ZariskiCharts.isCartesianPushforward_zariskiChartLiftedSite_iff`), and the
derived functor of the equivalence of module categories
`AlgebraicGeometry.ZariskiCharts.zariskiChartModulesEquivalence` matches quasi-coherent and
cartesian cohomology sheaves
(`AlgebraicGeometry.ZariskiCharts.isCartesianPresheaf_zariskiChartModulesEquivalence_iff`).

## Main definitions

* `AlgebraicGeometry.ZariskiCharts.zariskiChartCartesianEquivalenceQuasicoherentDerived`: the
  0GZS subcategory of the lifted chart site is equivalent to `D_QCoh(O_S)`.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.ChaoticComparison (IsCartesianPushforward cartesianSheaves)
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

universe u m

namespace AlgebraicGeometry.ZariskiCharts

section Abelian

variable (S : Scheme.{u})

/-- Presheaves of abelian groups with sections in `max (u + 1) m` on the opens of a scheme admit
sheafification, the site of opens being essentially small. -/
instance opens_hasSheafify_addCommGrpCat :
    HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{max (u + 1) m} :=
  haveI : EssentiallySmall.{max (u + 1) m} S.Opens := essentiallySmall_lift.{max (u + 1) m, u} _
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max (u + 1) m} _

/-- On the opens of a scheme, the morphisms of presheaves of abelian groups with sections in
`max (u + 1) m` inverted by sheafification are the locally bijective ones. -/
instance opens_wEqualsLocallyBijective_addCommGrpCat :
    (Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} := by
  have : EssentiallySmall.{max (u + 1) m} S.Opens := essentiallySmall_lift.{max (u + 1) m, u} _
  have (X : S.Opensᵒᵖ) : HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{max (u + 1) m} S.Opens).inverse.op)
      AddCommGrpCat.{max (u + 1) m} :=
    hasLimitsOfShape_of_essentiallySmall.{max (u + 1) m} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **`O_S`-modules with sections in `max (u + 1) m` form an abelian category**: the abelian
structure of sheaves of modules, recorded at this universe so that it is found before the
instances stated at a `max` pattern of universes, whose universe constraints would otherwise be
left unsolved here. -/
noncomputable instance schemeModules_abelian :
    Abelian (SheafOfModules.{max (u + 1) m} S.ringCatSheaf) :=
  SheafOfModules.instAbelian S.ringCatSheaf

end Abelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor of the equivalence of module categories with the lifted chart site is
additive. -/
instance zariskiChartModulesEquivalence_functor_additive :
    (zariskiChartModulesEquivalence.{u, m} B S hS).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The subcategory of Stacks 0GZS on the lifted chart site of `S` is `D_QCoh(O_S)`.** For
module sections in `max (u + 1) m` and any model of the derived category of `O_S`-modules, the
full subcategory of the derived category of sheaves of modules on
`AlgebraicGeometry.ZariskiCharts.zariskiChartLiftedSite` of the objects `K` with `Rε_*K`
cartesian is equivalent to the full subcategory of the derived category of `O_S`-modules of the
objects with quasi-coherent cohomology sheaves. -/
noncomputable def zariskiChartCartesianEquivalenceQuasicoherentDerived
    [HasDerivedCategory (SheafOfModules.{max (u + 1) m} S.ringCatSheaf)] :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
      (zariskiChartLiftedSite.{u, m} B S hS)
    (IsCartesianPushforward.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O)
        (baseChangeDataOfComm.{max (u + 1) m, max (u + 1) m, max (u + 1) m, max (u + 1) m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O).obj
          Stacks.TerminalBaseChange.CommSections.mul_comm)).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite S.ringCatSheaf :
        ObjectProperty (SheafOfModules.{max (u + 1) m} S.ringCatSheaf))).FullSubcategory :=
  letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
    (zariskiChartLiftedSite.{u, m} B S hS)
  letI : (cartesianSheaves.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (zariskiChartLiftedSite.{u, m} B S hS).O)).IsClosedUnderIsomorphisms :=
    ⟨fun {_ _} e hX => Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPresheaf.of_iso
      ((SheafOfModules.forget _).mapIso e) hX⟩
  letI : (DerivedCategoryB.derivedCategoryB (cartesianSheaves.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (zariskiChartLiftedSite.{u, m} B S hS).O))).IsClosedUnderIsomorphisms :=
    ⟨fun {_ _} e hX n => (cartesianSheaves.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O)).prop_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (hX n)⟩
  (CategoryTheory.Equivalence.refl.congrFullSubcategory (by
      ext K
      exact (isCartesianPushforward_zariskiChartLiftedSite_iff.{u, m} B S hS K).symm)).trans
    (Stacks.UniverseLift.derivedCategoryBEquivalence (zariskiChartModulesEquivalence.{u, m} B S hS)
      (SheafOfModules.isQuasicoherentOnSite S.ringCatSheaf)
      (cartesianSheaves.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiChartLiftedSite.{u, m} B S hS).O))
      (isCartesianPresheaf_zariskiChartModulesEquivalence_iff.{u, m} B S hS)).symm

end AlgebraicGeometry.ZariskiCharts
