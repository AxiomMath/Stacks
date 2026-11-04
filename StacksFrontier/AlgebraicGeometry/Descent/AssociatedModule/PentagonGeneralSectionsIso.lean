module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PentagonGeneralSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalComparisonPseudonaturalProofRightAdjoint

/-!
# The comparison of sections of the associated module, computed

`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` is the comparison of sections of the
associated module with restriction to an object `T`, the mate of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` with respect to
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`. This file computes it.

## Main results

* `AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso_eq`: the comparison of sections is the
  comparison `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` of the two right adjoints
  of restriction, whiskered, followed by the mate of
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` with respect to
  `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction`.
* `AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso_eq_overMapStar`: the same with the
  comparison of right adjoints replaced by its closed form
  `Stacks.SheafOfModules.overMapStarPushforwardIsoOverPullback`.
* `AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso_eq_explicit`: the comparison of sections
  in closed form, every factor a `SheafOfModules.pushforwardComp`, a
  `SheafOfModules.pushforwardCongr₂`, a `SheafOfModules.pushforwardCongr`, a unit of a
  reindexing equivalence or a structural associator or unitor.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of sections, in terms of the mate with respect to the other adjunction of
restriction to an object.** The two adjunctions
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` and
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction` of one and the same functor give
two mates of `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, and the two differ
by the comparison `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` of the two right
adjoints, whiskered by `AlgebraicGeometry.BigFppfOver.restrictModule`. -/
public theorem objRestrictSectionsIso_eq (T : BigFppfOver B S hS) :
    objRestrictSectionsIso B S hS T =
      Functor.isoWhiskerRight (objRestrictRightAdjointIso B S hS T).symm
          (restrictModule B S hS) ≪≫
        conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp
            (objRestrictAdjunction B S hS T))
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
            (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
          (associatedModuleObjRestrictNatIso B S hS T) := by
  have hrefl : Adjunction.rightAdjointUniq (associatedModuleAdjunction B S hS)
      (associatedModuleAdjunction B S hS) = Iso.refl (restrictModule B S hS) :=
    Iso.ext (Adjunction.rightAdjointUniq_refl (associatedModuleAdjunction B S hS))
  refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_congr_target
    ((associatedModuleAdjunction B S hS).comp (objRestrictAdjunction B S hS T))
    ((associatedModuleAdjunction B S hS).comp (objRestrictOverPullbackAdjunction B S hS T))
    ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
      (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (associatedModuleObjRestrictNatIso B S hS T)) ?_
  refine congrArg (fun x => x ≪≫ conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp
      (objRestrictAdjunction B S hS T))
    ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
      (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (associatedModuleObjRestrictNatIso B S hS T)) ?_
  refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_refl _ _) ?_
  refine Eq.trans (Stacks.Mates.rightAdjointUniq_comp (associatedModuleAdjunction B S hS)
    (associatedModuleAdjunction B S hS) (objRestrictOverPullbackAdjunction B S hS T)
    (objRestrictAdjunction B S hS T)) ?_
  refine Eq.trans (congrArg (fun x => Functor.isoWhiskerRight
      (Adjunction.rightAdjointUniq (objRestrictOverPullbackAdjunction B S hS T)
        (objRestrictAdjunction B S hS T)) (restrictModule B S hS) ≪≫
      Functor.isoWhiskerLeft _ x) hrefl) ?_
  refine Eq.trans (congrArg (fun x => Functor.isoWhiskerRight
      (Adjunction.rightAdjointUniq (objRestrictOverPullbackAdjunction B S hS T)
        (objRestrictAdjunction B S hS T)) (restrictModule B S hS) ≪≫ x)
    (Functor.isoWhiskerLeft_refl _ _)) ?_
  exact Iso.trans_refl _

/-- **The comparison of sections with the comparison of right adjoints replaced by its closed
form.** The comparison of right adjoints is replaced by
`Stacks.SheafOfModules.overMapStarPushforwardIsoOverPullback` at the structure morphism of `T`:
the contraction `SheafOfModules.pushforwardComp` of the iterated pushforward followed by the
transport `SheafOfModules.pushforwardCongr₂` along an isomorphism of sites. -/
public theorem objRestrictSectionsIso_eq_overMapStar (T : BigFppfOver B S hS) :
    objRestrictSectionsIso B S hS T =
      Functor.isoWhiskerRight (overMapStarPushforwardIsoOverPullback
            (J := B.topology) T.hom B.structureSheaf).symm (restrictModule B S hS) ≪≫
        conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp
            (objRestrictAdjunction B S hS T))
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
            (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
          (associatedModuleObjRestrictNatIso B S hS T) :=
  Eq.trans (objRestrictSectionsIso_eq B S hS T)
    (congrArg (fun x => Functor.isoWhiskerRight (Iso.symm x) (restrictModule B S hS) ≪≫
        conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp
            (objRestrictAdjunction B S hS T))
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
            (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
          (associatedModuleObjRestrictNatIso B S hS T))
      (objRestrictRightAdjointIso_eq B S hS T))

/-- **The comparison of sections in closed form.** It is an isomorphism in which every factor is
a comparison of pushforwards of sheaves of modules or a structural associator or unitor:

* the transport along an isomorphism of sites and the contraction of the iterated pushforward,
  from the comparison of the two right adjoints of restriction;
* the contraction of the iterated pushforward through the localization at `T`, the transport along
  the square of ringed sites `AlgebraicGeometry.BigFppfOver.objStarIso`, and the contraction
  through the scheme of `T`, from the mate of
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`;
* the unit of the inverse reindexing equivalence and the transport along
  `AlgebraicGeometry.BigFppfOver.objSliceStructureMap_eq`, from the mate of the comparison between
  the two spellings of the ringed site. -/
public theorem objRestrictSectionsIso_eq_explicit (T : BigFppfOver B S hS) :
    objRestrictSectionsIso B S hS T =
      Functor.isoWhiskerRight (overMapStarPushforwardIsoOverPullback
            (J := B.topology) T.hom B.structureSheaf).symm (restrictModule B S hS) ≪≫
        (Functor.associator (Stacks.SheafOfModules.reindexEquivalence
              (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
              (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
                (SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver T))
                (restrictModule B S hS) ≪≫
          Functor.isoWhiskerLeft (Stacks.SheafOfModules.reindexEquivalence
            (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
            (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
              (SheafOfModules.pushforwardComp.{u} (structureMap B S hS)
                  (SheafOfModules.pushforwardOver T) ≪≫
                SheafOfModules.pushforwardCongr₂.{u} _ (objStarIso B S hS T)
                    (comparisonComp_objStarIso B S hS T) ≪≫
                  (SheafOfModules.pushforwardComp.{u} (objHom B S hS T).toRingCatSheafHom
                    (objSliceStructureMap B S hS T)).symm) ≪≫
            (Functor.associator (Stacks.SheafOfModules.reindexEquivalence
              (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
              (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
                  (SheafOfModules.pushforward.{u} (objSliceStructureMap B S hS T))
                  (Scheme.Modules.pushforward (objHom B S hS T))).symm ≪≫
              (Functor.isoWhiskerRight
                ((Functor.leftUnitor
                        (restrictModule B (objScheme B S hS T)
                          (contains_objScheme B S hS T))).symm ≪≫
                Functor.isoWhiskerRight (Stacks.SheafOfModules.reindexEquivalence
                  (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
                  (objEquiv B S hS T) ((structureSheaf B S hS).over T)).symm.unitIso
                    (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)) ≪≫
                  Functor.associator (Stacks.SheafOfModules.reindexEquivalence
                    (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
                    (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
                      (SheafOfModules.pushforward.{u} (objReindexSharp B S hS T))
                      (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)) ≪≫
                    Functor.isoWhiskerLeft (Stacks.SheafOfModules.reindexEquivalence
                      (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
                      (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
                      (SheafOfModules.pushforwardComp.{u}
                          (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T))
                          (objReindexSharp B S hS T) ≪≫
                        SheafOfModules.pushforwardCongr.{u}
                          (objSliceStructureMap_eq B S hS T).symm))
                (Scheme.Modules.pushforward (objHom B S hS T))).symm) :=
  Eq.trans (objRestrictSectionsIso_eq_overMapStar B S hS T)
    (congrArg (fun x => Functor.isoWhiskerRight (overMapStarPushforwardIsoOverPullback
          (J := B.topology) T.hom B.structureSheaf).symm (restrictModule B S hS) ≪≫ x)
      (conjugateIsoEquiv_associatedModuleObjRestrictNatIso B S hS T))

end AlgebraicGeometry.BigFppfOver

end
