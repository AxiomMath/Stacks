module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.StructureSheafAugmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentPullbackRestriction

/-!
# The pullback along the augmentation with the restricted structure sheaf is restriction

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`, and let
`a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` be the ringed augmentation of Remark 0D9W with `O` the
restriction of `O_C` along the localization functor `j_total`
(`CategoryTheory.SimplicialSemiRepresentable.structureAugmentation`). This file identifies the
pullback `a^*` of sheaves of modules with the literal restriction of sheaves of modules along
`j_total`, the source's `a^* = a⁻¹`.

## Main results

All in the namespace `CategoryTheory.SimplicialSemiRepresentable`:

* `structureAugmentation_fSharpInverseImageRing_ringSheafMap`: the structure map of `a`, read on
  sheaves of rings and then on underlying sheaves of sets, is the identification of Stacks 0D8B of
  the inverse image of `a` with restriction along `j_total`.
* `structurePullbackModulesRestrictionIso`: `a^* ≅ (-)|_{(C/K)_total}`.

## Implementation notes

The argument is that of
`CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso` for the component
morphisms: `a^*` is the inverse image of modules followed by extension of scalars along the
invertible structure map, which is restriction of scalars along its inverse; the inverse image of
modules is transported along the comparison of Stacks 0D8B to the inverse image along the
restriction functor, which is the literal restriction; three restrictions of scalars are left and
cancel.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- The comparison of the inverse image of the sheaf of rings `O_C` along restriction to the
total site with its restriction, read on sheaves of rings. -/
abbrev totalRestrictionRingIso :=
  @restrictionRingIso _ _ _ _ (situation X.J K).totalTopology X.J _ (totalForget K)
    (totalForget_isContinuous X.J K) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **The structure map of the augmentation on underlying sheaves of sets is the comparison of
Stacks 0D8B.** -/
theorem structureAugmentation_fSharpInverseImageRing_ringSheafMap :
    (sheafCompose (situation X.J K).totalTopology (forget RingCat.{u})).map
        (structureAugmentation X K).totalRingedHom.fSharpInverseImageRing =
      (structureInverseImageIso X K).hom.app
        ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O) := by
  rw [← AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
    (structureAugmentation X K).totalRingedHom]
  refine (congrArg (fun q ↦ (sheafCompose (situation X.J K).totalTopology
      (forget CommRingCat.{u})).map q) (structureAugmentation_fSharpInverseImage X K)).trans ?_
  exact structureSheafInverseImageIso_hom_forget X K

/-- The scalar map of the comparison of `a^*` with restriction: the structure map of `a`, on
sheaves of rings, followed by the inverse of the restriction comparison. -/
def structurePullbackRestrictionRingMap :=
  (structureAugmentation X K).totalRingedHom.fSharpInverseImageRing ≫
    (totalRestrictionRingIso X K).inv

/-- The inverse of the structure map of `a`, on sheaves of rings. -/
def structurePullbackStructureInv :=
  (asIso (structureAugmentation X K).totalRingedHom.toModulesHom.fSharpInverseImage).inv

/-- The scalar map has the comparison of Stacks 0D8B underneath. -/
theorem structurePullbackRestrictionRingMap_ringSheafMap :
    (sheafCompose (situation X.J K).totalTopology (forget RingCat.{u})).map
        (structurePullbackRestrictionRingMap X K) =
      (structureInverseImageIso X K).hom.app
        (Sheaf.ringSheaf.{u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ((sheafCompose (situation X.J K).totalTopology (forget RingCat.{u})).map_comp _ _).trans
    ((congrArg
        (fun q ↦ (sheafCompose (situation X.J K).totalTopology (forget RingCat.{u})).map
            (structureAugmentation X K).totalRingedHom.fSharpInverseImageRing ≫ q)
        (@restrictionRingIso_inv_ringSheafMap _ _ _ _ (situation X.J K).totalTopology X.J _ _
          (totalForget K) (totalForget_isContinuous X.J K)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).trans
      ((Category.comp_id _).trans
        (structureAugmentation_fSharpInverseImageRing_ringSheafMap X K)))

/-- The three scalar maps compose to the identity. -/
theorem structurePullbackStructureInv_comp :
    structurePullbackStructureInv X K ≫
        (structurePullbackRestrictionRingMap X K ≫ (totalRestrictionRingIso X K).hom) =
      𝟙 _ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q ↦ q ≫ (totalRestrictionRingIso X K).hom)
        (Iso.inv_hom_id_assoc
          (asIso (structureAugmentation X K).totalRingedHom.fSharpInverseImageRing)
          (totalRestrictionRingIso X K).inv)).trans
      (totalRestrictionRingIso X K).inv_hom_id)

/-- The inverse image of sheaves of modules along the morphism of topoi of the augmentation is
the transport along the comparison of Stacks 0D8B of the inverse image along restriction. -/
def structureInverseImageModulesRestrictionIso :=
  pullbackModuleFunctorIsoOfNatIso.{u, u, u, u, u, u} (situation X.J K).totalTopology
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (structureInverseImageIso X K)
    (structurePullbackRestrictionRingMap X K)
    (structurePullbackRestrictionRingMap_ringSheafMap X K)

/-- **`a^* = a⁻¹` is restriction along `j_total`.** The pullback of sheaves of modules along the
ringed augmentation with the restricted structure sheaf is the literal restriction of sheaves of
modules along the localization functor `j_total`. -/
def structurePullbackModulesRestrictionIso :
    (structureAugmentation X K).totalRingedHom.toModulesHom.pullbackModules ≅
      @restrictionModules _ _ _ _ (situation X.J K).totalTopology X.J (totalForget K)
        (totalForget_isContinuous X.J K) (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := by
  refine Iso.trans (Functor.isoWhiskerLeft _
    ((structureAugmentation X K).totalRingedHom.toModulesHom
      |>.extendScalarsFSharpIsoRestrictScalarsOfIsIso)) ?_
  refine Iso.trans
    (Functor.isoWhiskerRight (structureInverseImageModulesRestrictionIso X K) _) ?_
  refine Iso.trans (Functor.isoWhiskerRight (Functor.isoWhiskerRight
    (@restrictionModuleIso _ _ _ _ (situation X.J K).totalTopology X.J _ _ (totalForget K)
      (totalForget_isContinuous X.J K) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _) _) ?_
  refine Iso.trans (Functor.associator _ _ _) ?_
  exact Functor.isoWhiskerLeft _ (Stacks.Sheaves.RingedPoint.sheafRestrictScalarsComp₃IsoId'
    (totalRestrictionRingIso X K).hom (structurePullbackRestrictionRingMap X K)
    (structurePullbackStructureInv X K) (structurePullbackStructureInv_comp X K))

end CategoryTheory.SimplicialSemiRepresentable

end
