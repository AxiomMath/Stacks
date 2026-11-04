module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverCrystal

/-!
# The restrictions to the ambient schemes of a localised crystalline site are conservative

Let `B` be an object of the big crystalline site of a global crystalline situation.  Every object
`Y` of the localisation `CRIS(X/S)/B` carries the functor
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOverFunctor` from the opens of its
ambient scheme into `CRIS(X/S)/B`, and restriction of sheaves of modules along it is the
restriction `F ↦ F_T` of [Stacks, Tag 07IQ] read on `CRIS(X/S)/B`
(`Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheafOverFunctor`).

This file proves that the family of those restrictions, indexed by the objects of the *fixed*
localised site, is jointly conservative, and draws the consequence that a cofork of sheaves of
modules on `CRIS(X/S)/B` is a cokernel as soon as each of them carries it to one.

`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative` proves
the same two statements for the family of functors that goes through the slice of the opens at the
greatest open.  The family used here is the one along which the `f`-map of [Stacks, Tag 07IQ] is
available at an arbitrary module universe
(`Crystalline.GlobalCrystallineSituation.Thickening.fmapCompOver`), which is what the direction
(2) ⇒ (1) of [Stacks, Tag 07IT] needs in order to use the crystal property.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOverFunctorObjTopIso` — the
  restriction of an object of a localised crystalline site to the whole of its ambient scheme is
  that object.
* `Crystalline.GlobalCrystallineSituation.Thickening`
  `.isIso_of_forall_isIso_moduleRestrictionSheafOver`
  — **the restrictions to the ambient schemes of the objects of a fixed localised crystalline site
  are jointly conservative.**
* `Crystalline.GlobalCrystallineSituation.Thickening.isColimitCokernelCoforkOfForallRestrictOver`
  — **a cokernel of sheaves of modules on a localised crystalline site is detected by those
  restrictions.**

## Implementation notes

Joint conservativity is `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app`
together with `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward`: the
latter gives invertibility of the component of the morphism at every object in the image of one of
the functors, and the functor attached to `Y` carries the greatest open of the ambient scheme of
`Y` to an object isomorphic to `Y`, the structure morphism of the restriction to the greatest open
being an isomorphism.

The detection of a cokernel is
`CategoryTheory.Limits.isColimitCokernelCoforkOfConservativeFamily`, whose other input —
preservation of the cokernel by each member of the family — is
`Crystalline.GlobalCrystallineSituation.Thickening`
`.preservesColimitsOfSize_moduleRestrictionSheafOverFunctor`, the functors of sites being
continuous and cocontinuous.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

variable (B : Thickening S)

/-- **The restriction of an object of a localised crystalline site to the whole of its ambient
scheme is that object.**  The greatest open of the ambient scheme of `Y` is carried by
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOverFunctor` to `Y` restricted to it,
whose structure morphism to `Y` is an isomorphism, and which maps to the base through that
morphism. -/
noncomputable def restrictOverFunctorObjTopIso (Y : Over B) :
    (restrictOverFunctor Y.hom).obj ⊤ ≅ Y :=
  Over.isoMk (@asIso _ _ _ _ (Y.left.restrictOpenHom ⊤) Y.left.isIso_restrictOpenHom_top) rfl

/-- **The restrictions to the ambient schemes of the objects of a fixed localised crystalline site
are jointly conservative.**  A morphism of sheaves of `𝒪_{X/S}`-modules on `CRIS(X/S)/B` whose
restriction `F ↦ F_T` at *every* object of that site is invertible is itself invertible.

No single one of those restrictions reflects anything, but between them they see every object,
since the restriction of an object to the whole of its ambient scheme is that object. -/
theorem isIso_of_forall_isIso_moduleRestrictionSheafOver
    {M N : SheafOfModules.{v} ((crystallineStructureSheaf S).over B)} (φ : M ⟶ N)
    (h : ∀ Y : Over B, IsIso ((moduleRestrictionSheafOverFunctor.{v} Y.hom).map φ)) :
    IsIso φ := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app φ fun W ↦ ?_
  obtain ⟨Y⟩ := W
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso φ
    (restrictOverFunctorObjTopIso B Y)
    (Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
      (restrictOverStructureHom Y.hom) φ (h Y) (op ⊤))

/-- The restriction of sheaves of `𝒪_{X/S}`-modules along a morphism of thickenings preserves
zero morphisms. -/
instance preservesZeroMorphisms_moduleRestrictionSheafOverFunctor {A : Thickening S} (h : A ⟶ B) :
    (moduleRestrictionSheafOverFunctor.{v} h).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **A cokernel of sheaves of `𝒪_{X/S}`-modules on a localised crystalline site is detected by
the restrictions to the ambient schemes of its objects.**  A cofork is a cokernel as soon as each
of those restrictions carries it to one.

Each of them preserves the cokernel it has to preserve, being a pushforward along a continuous
*and cocontinuous* functor of sites, and the family is jointly conservative by
`Crystalline.GlobalCrystallineSituation.Thickening`
`.isIso_of_forall_isIso_moduleRestrictionSheafOver`. -/
noncomputable def isColimitCokernelCoforkOfForallRestrictOver
    {Q P N : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
    {a : Q ⟶ P} {b : P ⟶ N} (hab : a ≫ b = 0) [HasCokernel a]
    (hb : ∀ Y : Over B, IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map b)
      (show (moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map a ≫
            (moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map b = 0 by
        rw [← Functor.map_comp, hab]
        exact (moduleRestrictionSheafOverFunctor.{u + 1} Y.hom).map_zero _ _))) :
    IsColimit (CokernelCofork.ofπ b hab) :=
  haveI : ∀ Y : Over B, PreservesColimit (parallelPair a 0)
      (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} Y.left.ringRestrictionSheaf from
        moduleRestrictionSheafOverFunctor.{u + 1} Y.hom) := fun Y ↦ by
    haveI := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} Y.hom
    haveI : PreservesColimitsOfSize.{0, 0}
        (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
            SheafOfModules.{u + 1} Y.left.ringRestrictionSheaf from
          moduleRestrictionSheafOverFunctor.{u + 1} Y.hom) :=
      preservesColimitsOfSize_shrink _
    infer_instance
  isColimitCokernelCoforkOfConservativeFamily hab
    (fun Y : Over B ↦
      show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} Y.left.ringRestrictionSheaf from
        moduleRestrictionSheafOverFunctor.{u + 1} Y.hom)
    (fun _ _ f hf ↦ isIso_of_forall_isIso_moduleRestrictionSheafOver B f hf) hb

end Thickening

end Crystalline.GlobalCrystallineSituation

end
