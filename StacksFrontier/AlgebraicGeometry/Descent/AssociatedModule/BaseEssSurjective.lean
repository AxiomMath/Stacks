module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement

/-!
# The restriction `𝒢 ↦ 𝒢|_{(Sch/X)_τ}` at `τ = fppf`, and the fppf sheaf condition it carries

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseMemberLocalStep.lean` defines the
restriction `AlgebraicGeometry.BigFppfOver.baseObjRestrict` of a module on `(Sch/S)_τ` to the big
`τ`-site of the scheme of an object, and proves the local step of Descent 03DX (1) for it at every
`τ`; `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseEssentialSurjectivity.lean`
derives from it that a quasi-coherent module on `(Sch/S)_τ` is an fppf sheaf and the
essential-surjectivity half of 03DX (1) at every `τ`.  This file records two complements.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseObjRestrict_fppf`: at `τ = fppf` the restriction is
  `AlgebraicGeometry.BigFppfOver.objRestrict`, by `rfl` — one notion, not two.
* `AlgebraicGeometry.BigFppfOver.isSheaf_baseObjRestrict_of_hasGlobalPresentation`: the
  restriction of a module on `(Sch/S)_τ` with a global presentation on the localization at `T` is
  a sheaf for the **fppf** topology of the big site of the scheme of `T`, read through
  Descent, Lemma 03DT on the pullback-sections sheaf.

## Implementation notes

Nothing here carries a `stacks` attribute: Stacks 03DX (1) at every `τ` is registered on
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite'`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- At `τ = fppf` the restriction `AlgebraicGeometry.BigFppfOver.baseObjRestrict` is
`AlgebraicGeometry.BigFppfOver.objRestrict`: one notion, not two. -/
public theorem baseObjRestrict_fppf :
    baseObjRestrict B S hS .fppf T = objRestrict B S hS T := rfl

/-- **The restriction of a module on `(Sch/S)_τ` to the big site of the scheme of `T` is a sheaf
for the fppf topology there**, as soon as its restriction to the localization at `T` has a
global presentation.

By the local step `AlgebraicGeometry.BigFppfOver`
`.exists_isQuasicoherent_iso_baseAssociatedModule_baseObjRestrict` it is the associated module of
a quasi-coherent `𝒪_X`-module `𝓕` on the big `τ`-site of the scheme `X` of `T`; that associated
module is the pullback-sections sheaf of `𝓕`
(`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf`), whose underlying presheaf
satisfies the **fppf** sheaf condition by Stacks 03DT
(`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules`, unconditional through
`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`). -/
public theorem isSheaf_baseObjRestrict_of_hasGlobalPresentation (τ : SiteKind)
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (h : (G.over T).HasGlobalPresentation) :
    Presheaf.IsSheaf (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      ((baseObjRestrict B S hS τ T).obj G).val.presheaf := by
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    exists_isQuasicoherent_iso_baseAssociatedModule_baseObjRestrict B S hS τ T h
  have := hF
  refine (Presheaf.isSheaf_of_iso_iff ((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).mapIso (e.symm ≪≫ baseAssociatedModuleIsoSectionsSheaf B
      (objScheme B S hS T) (contains_objScheme B S hS T) τ F))).2 ?_
  exact isSheaf_sectionsPresheafOfModules B (objScheme B S hS T)
    (contains_objScheme B S hS T) fpqcDescentOfQuasicoherentHoms F

end AlgebraicGeometry.BigFppfOver

end
