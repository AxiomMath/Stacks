module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionConservative
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictOverCrystal

/-!
# The restrictions to the ambient schemes of a localised small crystalline site are conservative

Let `B` be an object of the small crystalline site of a global crystalline situation.  Every object
`Y` of the localisation `Cris(X/S)/B` carries the functor
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.restrictOverFunctor` from
the opens of its ambient scheme into `Cris(X/S)/B`, and restriction of sheaves of modules along it
is the restriction `F ↦ F_T` of [Stacks, Tag 07IQ] read on `Cris(X/S)/B`.

This file proves that the family of those restrictions, indexed by the objects of the *fixed*
localised site, is jointly conservative, and draws the consequence that a cofork of sheaves of
modules on `Cris(X/S)/B` is a cokernel as soon as each of them carries it to one.  It is the
small-site form of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverConservative`;
[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike, and a sheaf of
modules on `Cris(X/S)` is in general not the restriction of one on `CRIS(X/S)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.restrictOverFunctorObjTopIso` — the restriction of an object of a localised small crystalline
  site to the whole of its ambient scheme is that object.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.isIso_of_forall_isIso_moduleRestrictionSheafOver`
  — **the restrictions to the ambient schemes of the objects of a fixed localised small crystalline
  site are jointly conservative.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.isColimitCokernelCoforkOfForallRestrictOver`
  — **a cokernel of sheaves of modules on a localised small crystalline site is detected by those
  restrictions.**

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

namespace CohomologyRestriction

variable (B : CrystallineThickening S)

/-- **The restriction of an object of a localised small crystalline site to the whole of its
ambient scheme is that object.**  The greatest open of the ambient scheme of `Y` is carried by
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.restrictOverFunctor` to `Y`
restricted to it, whose structure morphism to `Y` is an isomorphism. -/
noncomputable def restrictOverFunctorObjTopIso (Y : Over B) :
    (restrictOverFunctor Y.hom).obj ⊤ ≅ Y :=
  Over.isoMk (@asIso _ _ _ _ (Y.left.restrictOpenHom ⊤)
    (CrystallineThickening.isIso_restrictOpenHom_top Y.left)) rfl

/-- **The restrictions to the ambient schemes of the objects of a fixed localised small crystalline
site are jointly conservative.**  A morphism of sheaves of `𝒪_{X/S}`-modules on `Cris(X/S)/B` whose
restriction `F ↦ F_T` at *every* object of that site is invertible is itself invertible. -/
theorem isIso_of_forall_isIso_moduleRestrictionSheafOver
    {M N : SheafOfModules.{v} ((structureSheaf S).over B)} (φ : M ⟶ N)
    (h : ∀ Y : Over B, IsIso ((moduleRestrictionSheafOverFunctor.{v} Y.hom).map φ)) :
    IsIso φ := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app φ fun W ↦ ?_
  obtain ⟨Y⟩ := W
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso φ
    (restrictOverFunctorObjTopIso B Y)
    (Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
      (restrictOverStructureHom Y.hom) φ (h Y) (op ⊤))

/-- Restriction of sheaves of modules along a morphism of crystalline thickenings preserves zero
morphisms. -/
instance preservesZeroMorphisms_moduleRestrictionSheafOverFunctor
    {A : CrystallineThickening S} (h : A ⟶ B) :
    (moduleRestrictionSheafOverFunctor.{v} h).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **A cokernel of sheaves of `𝒪_{X/S}`-modules on a localised small crystalline site is detected
by the restrictions to the ambient schemes of its objects.**  A cofork is a cokernel as soon as
each of those restrictions carries it to one. -/
noncomputable def isColimitCokernelCoforkOfForallRestrictOver
    {Q P N : SheafOfModules.{u + 1} ((structureSheaf S).over B)}
    {a : Q ⟶ P} {b : P ⟶ N} (hab : a ≫ b = 0) [HasCokernel a]
    (hb : ∀ Y : Over B, IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map b)
      (show (moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map a ≫
            (moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map b = 0 by
        rw [← Functor.map_comp, hab]
        exact (moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map_zero _ _))) :
    IsColimit (CokernelCofork.ofπ b hab) :=
  haveI : ∀ Y : Over B, PreservesColimit (parallelPair a 0)
      (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf Y.left.obj) from
        moduleRestrictionSheafOverFunctor.{u + 1} Y.hom) := fun Y ↦ by
    have := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} Y.hom
    have : PreservesColimitsOfSize.{0, 0}
        (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
            SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf Y.left.obj) from
          moduleRestrictionSheafOverFunctor.{u + 1} Y.hom) :=
      preservesColimitsOfSize_shrink _
    infer_instance
  isColimitCokernelCoforkOfConservativeFamily hab
    (fun Y : Over B ↦
      show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf Y.left.obj) from
        moduleRestrictionSheafOverFunctor.{u + 1} Y.hom)
    (fun _ _ f hf ↦ isIso_of_forall_isIso_moduleRestrictionSheafOver B f hf) hb

end CohomologyRestriction

end Crystalline.GlobalCrystallineSituation.SmallSite

end
