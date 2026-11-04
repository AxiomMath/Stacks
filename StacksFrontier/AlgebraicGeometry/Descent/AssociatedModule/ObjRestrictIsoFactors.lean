module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality

/-!
# The factors of the comparison `associatedModuleObjRestrictIso`

`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso` compares two spellings of one and
the same ringed site: the localization of the big fppf site of `S` at an object `T`, and the big
fppf site of the scheme `X` of `T`. It identifies the localized pullback followed by the
reindexing with the associated-module functor of `X`, and it is a composite of five factors: a
transport of the pullback along an equality of comparisons of structure sheaves, the contraction
of an iterated pullback, the uniqueness of a left adjoint, the counit of the reindexing
equivalence, and a right unitor. This file names the comparison of structure sheaves carried by
the reindexing, which is the identity, factors
`AlgebraicGeometry.BigFppfOver.objSliceStructureMap` through it, and writes the composite as an
equality.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objReindexSharp`: the comparison of structure sheaves of the
  reindexing equivalence, which is the identity.

## Main results

* `AlgebraicGeometry.BigFppfOver.objSliceStructureMap_eq`: the comparison of ringed sites of the
  localization at `T` factors as the comparison of the big fppf site of the scheme of `T`
  followed by the (identity) comparison of the reindexing.
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso_eq`:
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso` is the composite of its five
  factors.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- Passing from the big fppf site of the scheme of `T` to the localization at `T` is continuous,
with the source site written as the big fppf category over that scheme. -/
public instance isContinuous_iteratedSliceBackward_objSite :
    Functor.IsContinuous
      (C := BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
      (Over.iteratedSliceBackward T)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      ((topology B S hS).over T) :=
  isContinuous_iteratedSliceBackward B S hS T

/-- The morphism of sheaves of rings presenting the reindexing
`AlgebraicGeometry.BigFppfOver.objEquiv` as a morphism of ringed sites, from the structure sheaf
of the big fppf site of the scheme of `T` to the transport of the structure sheaf of the
localization at `T`. It is the identity, the two sheaves being equal by
`AlgebraicGeometry.BigFppfOver.reindexRing_objEquiv`. -/
public noncomputable def objReindexSharp :
    structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T) ⟶
      ((Over.iteratedSliceBackward T).sheafPushforwardContinuous RingCat.{u}
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
        ((topology B S hS).over T)).obj ((structureSheaf B S hS).over T) :=
  𝟙 _

/-- The pushforward along `AlgebraicGeometry.BigFppfOver.objReindexSharp` is a right adjoint,
being the functor of the equivalence of module categories
`Stacks.SheafOfModules.reindexEquivalence`. -/
public instance isRightAdjoint_pushforward_objReindexSharp :
    (SheafOfModules.pushforward.{u} (objReindexSharp B S hS T)).IsRightAdjoint :=
  (Stacks.SheafOfModules.reindexEquivalence
    (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
    (objEquiv B S hS T)
    ((structureSheaf B S hS).over T)).symm.toAdjunction.isRightAdjoint

/-- The comparison of ringed sites `AlgebraicGeometry.BigFppfOver.objSliceStructureMap` of the
localization at `T` is the comparison `AlgebraicGeometry.BigFppfOver.structureMap` of the big
fppf site of the scheme of `T` followed by the image under the pushforward of the (identity)
comparison `AlgebraicGeometry.BigFppfOver.objReindexSharp` of the reindexing. -/
public theorem objSliceStructureMap_eq :
    objSliceStructureMap B S hS T =
      structureMap B (objScheme B S hS T) (contains_objScheme B S hS T) ≫
      ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)
        ).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS T))
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).map
        (objReindexSharp B S hS T) :=
  ((congrArg (fun k => structureMap B (objScheme B S hS T) (contains_objScheme B S hS T) ≫ k)
    (((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)
      ).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥(objScheme B S hS T))
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).map_id _)).trans
    (Category.comp_id _)).symm

/-- The pushforward along the factored comparison of
`AlgebraicGeometry.BigFppfOver.objSliceStructureMap_eq` is a right adjoint. -/
public instance isRightAdjoint_pushforward_objSliceStructureMapFactored :
    (SheafOfModules.pushforward.{u} (F := objToBig B S hS T)
      (R := (structureSheaf B S hS).over T)
      (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T) ≫
        ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)
          ).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology ↥(objScheme B S hS T))
          (topology B (objScheme B S hS T) (contains_objScheme B S hS T))).map
          (objReindexSharp B S hS T))).IsRightAdjoint :=
  have key : ∀ χ : (objScheme B S hS T).ringCatSheaf ⟶
      ((objToBig B S hS T).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS T))
        ((topology B S hS).over T)).obj ((structureSheaf B S hS).over T),
      objSliceStructureMap B S hS T = χ →
        (SheafOfModules.pushforward.{u} χ).IsRightAdjoint := by
    rintro χ rfl
    infer_instance
  key _ (objSliceStructureMap_eq B S hS T)

/-- `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso` is the composite of five
isomorphisms:

* `Stacks.SheafOfModules.pullbackCongr` of
  `AlgebraicGeometry.BigFppfOver.objSliceStructureMap_eq`, which transports the localized pullback
  to the factored comparison;
* the inverse of `SheafOfModules.pullbackComp` of
  `AlgebraicGeometry.BigFppfOver.structureMap` and
  `AlgebraicGeometry.BigFppfOver.objReindexSharp`, which splits that pullback into the
  associated-module functor of the scheme of `T` followed by the pullback along the reindexing;
* `CategoryTheory.Adjunction.leftAdjointUniq` identifying the pullback along the reindexing with
  the inverse of `Stacks.SheafOfModules.reindexEquivalence`, both being left adjoint to the
  pushforward along the identity;
* the counit isomorphism of that equivalence, which cancels the inverse against the reindexing
  itself;
* and the right unitor.

The first two factors are whiskered on the right by the reindexing
`AlgebraicGeometry.BigFppfOver.objRestrictFunctor`, the last three on the left by the
associated-module functor of the scheme of `T`. -/
public theorem associatedModuleObjRestrictIso_eq :
    associatedModuleObjRestrictIso B S hS T =
      Functor.isoWhiskerRight
          (@Stacks.SheafOfModules.pullbackCongr _ _ _ _ _ _ _ _ _ _ _ _
              (sheafPushforward_objSliceStructureMap_isRightAdjoint B S hS T)
              (isRightAdjoint_pushforward_objSliceStructureMapFactored B S hS T)
              (objSliceStructureMap_eq B S hS T) ≪≫
            (SheafOfModules.pullbackComp.{u}
              (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T))
              (objReindexSharp B S hS T)).symm)
          (objRestrictFunctor B S hS T) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
          (Adjunction.leftAdjointUniq
            (SheafOfModules.pullbackPushforwardAdjunction.{u} (objReindexSharp B S hS T))
            (Stacks.SheafOfModules.reindexEquivalence
              (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
              (objEquiv B S hS T) ((structureSheaf B S hS).over T)).symm.toAdjunction) _ ≪≫
          (Stacks.SheafOfModules.reindexEquivalence
            (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
            (objEquiv B S hS T) ((structureSheaf B S hS).over T)).counitIso) ≪≫
        Functor.rightUnitor _ :=
  rfl

end AlgebraicGeometry.BigFppfOver

end
