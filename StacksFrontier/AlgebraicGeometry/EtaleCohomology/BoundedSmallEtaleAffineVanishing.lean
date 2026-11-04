module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomologyVanishing
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison

/-!
# The first cohomology of a quasi-coherent module on an affine, on the size-bounded étale site

Let `T` be an affine scheme and `𝓜` a quasi-coherent `𝒪_T`-module.  The first cohomology of the
associated module `𝓜^a` vanishes on the small étale site of `T` cut out of a chosen big étale
site, `AlgebraicGeometry.SmallEtale B T hT`.

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sectionsSheafOfModules` and
  `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_associatedModule`: the vanishing, for
  the pullback-sections sheaf of [Stacks, Tag 03DS] and for the associated module of [Stacks,
  Tag 03DU] respectively.  The `Ext` universe is a free parameter.

## Implementation notes

The restriction of `AlgebraicGeometry.smallEtaleAssociatedSheaf` along
`AlgebraicGeometry.SmallEtale.toEtaleSite` is the underlying abelian sheaf of the
pullback-sections sheaf of modules on the bounded site *on the nose*: both are the
pullback-sections presheaf `(f : X → T) ↦ Γ(X, f^*𝓜)` of [Stacks, Tag 03DS] precomposed with the
canonical functor to the schemes over `T`, and the two spellings of that functor —
`AlgebraicGeometry.SmallEtale.toEtaleSite ⋙ AlgebraicGeometry.Scheme.Etale.forget` and
`AlgebraicGeometry.SmallEtale.toOver` — are equal.

`CategoryTheory.Sheaf.H'`, in which the comparison with Zariski cohomology is stated, carries
its `Ext` universe at the morphism universe `u` of the sites; the conclusions on the size-bounded
site leave it free, which
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite` allows,
its two sides having unrelated `Ext` universes.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)

/-- The final object of the size-bounded small étale site goes to a final object of Mathlib's:
both are the identity of `T`. -/
public def isTerminal_toEtaleSite_final :
    IsTerminal ((toEtaleSite B T hT).obj (final B T hT)) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

/-- Abelian sheaves on Mathlib's small étale site have limits of the shape of every
structured-arrow category of the comparison functor from the size-bounded site: these categories
are essentially small, the size-bounded site being essentially small. -/
public theorem hasLimitsOfShape_structuredArrow_toEtaleSite :
    ∀ Y : (T.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (toEtaleSite B T hT).op) AddCommGrpCat.{u} :=
  fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- **The first cohomology of the associated module of a quasi-coherent module on an affine
scheme vanishes on Mathlib's small étale site.**  By [Stacks, Tag 03DW] clause (2) it is the
first Zariski cohomology of the module itself, which vanishes by [Stacks, Tag 01XB]. -/
public theorem subsingleton_sheafH_one_smallEtaleAssociatedSheaf [AlgebraicGeometry.IsAffine T]
    (M : T.Modules) [M.IsQuasicoherent] :
    Subsingleton (Sheaf.H.{u} (smallEtaleAssociatedSheaf T M) 1) := by
  have hzar : Subsingleton (Sheaf.H.{u}
      ((SheafOfModules.toSheaf T.ringCatSheaf).obj M) 1) :=
    (Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH
      T 1 M).1 (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen T M ⊤
        (isAffineOpen_top T) 1 Nat.one_pos)
  have hzar' : Subsingleton (Sheaf.H'.{u} ((SheafOfModules.toSheaf T.ringCatSheaf).obj M) 1 ⊤) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
      ((SheafOfModules.toSheaf T.ringCatSheaf).obj M) 1).1 hzar
  have hetale : Subsingleton
      (Sheaf.H'.{u} (smallEtaleAssociatedSheaf T M) 1 ((opensToEtale T).obj ⊤)) :=
    ((smallEtaleQuasiCoherentGlobalCohomologyIso T M 1).addCommGroupIsoToAddEquiv).toEquiv.symm
      |>.subsingleton
  exact (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'.{u, u, u + 1}
    (Scheme.smallEtaleTopology T) (smallEtaleAssociatedSheaf T M) 1 _
    (isTerminal_opensToEtale_top T)).2 hetale

/-- The restriction of `𝓜^a`, read on Mathlib's small étale site, along the embedding of the
size-bounded site is the underlying abelian sheaf of the pullback-sections sheaf of modules
there.  Both are the pullback-sections presheaf of [Stacks, Tag 03DS] precomposed with the
canonical functor to the schemes over `T`. -/
public theorem sheafPushforwardContinuous_toEtaleSite_smallEtaleAssociatedSheaf
    (M : T.Modules) [M.IsQuasicoherent] :
    ((toEtaleSite B T hT).sheafPushforwardContinuous AddCommGrpCat.{u}
        (topology B T hT) (Scheme.smallEtaleTopology T)).obj (smallEtaleAssociatedSheaf T M) =
      (SheafOfModules.toSheaf (structureSheaf B T hT)).obj (sectionsSheafOfModules' B T hT M) :=
  rfl

/-- **The first cohomology of the pullback-sections sheaf of a quasi-coherent module on an
affine scheme vanishes on the size-bounded small étale site.**  The bounded site is a dense
subsite of Mathlib's and carries its final object to a final object, so this is
`subsingleton_sheafH_one_smallEtaleAssociatedSheaf` read on the subsite. -/
public theorem subsingleton_sheafH_one_sectionsSheafOfModules [AlgebraicGeometry.IsAffine T]
    (M : T.Modules) [M.IsQuasicoherent]
    [HasExt.{w} (Sheaf (topology B T hT) AddCommGrpCat.{u})] :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj
        (sectionsSheafOfModules' B T hT M)) 1) := by
  have := hasLimitsOfShape_structuredArrow_toEtaleSite B T hT
  rw [← sheafPushforwardContinuous_toEtaleSite_smallEtaleAssociatedSheaf B T hT M]
  exact Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite.{w,
      u, u, u + 1, u, u + 1, u}
    (topology B T hT) (Scheme.smallEtaleTopology T) (toEtaleSite B T hT)
    (finalIsTerminal B T hT) (isTerminal_toEtaleSite_final B T hT)
    (smallEtaleAssociatedSheaf T M) 1
    (subsingleton_sheafH_one_smallEtaleAssociatedSheaf T M)

/-- **The first cohomology of the associated module of a quasi-coherent module on an affine
scheme vanishes on the size-bounded small étale site.**  The associated module of [Stacks,
Tag 03DU] is the pullback-sections sheaf of [Stacks, Tag 03DS], by
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules'`. -/
public theorem subsingleton_sheafH_one_associatedModule [AlgebraicGeometry.IsAffine T]
    (M : T.Modules) [M.IsQuasicoherent]
    [HasExt.{w} (Sheaf (topology B T hT) AddCommGrpCat.{u})] :
    Subsingleton (Sheaf.H.{w}
      ((SheafOfModules.toSheaf (structureSheaf B T hT)).obj
        ((associatedModule B T hT).obj M)) 1) :=
  Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    ((SheafOfModules.toSheaf (structureSheaf B T hT)).mapIso
      (associatedModuleIsoSectionsSheafOfModules' B T hT M)).symm 1
    (subsingleton_sheafH_one_sectionsSheafOfModules B T hT M)

end AlgebraicGeometry.SmallEtale

end
