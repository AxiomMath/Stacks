module

public import StacksFrontier.Homology.HomComplex.TransportHomEquivValue
public import StacksFrontier.Homology.HomComplex.RHom.ScalarTransportReconciliation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsComponent

/-!
# The uncurried inverse component of [stacks 0E1W], with the scalar conjugation cancelled

`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app` displays the inverse
component of the change-of-rings isomorphism of [stacks 0E1W] as four factors, the last three of
which are images of the scalar equivalence of the `ULift` world. By
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom_eq` the bundle of [stacks 0A63] at the same
module universe is conjugated along the same equivalence, so taking the [stacks 0A63] transpose
of the component cancels that conjugation. This file computes the transpose over `R` of the
inverse component as one fixed-universe transpose together with two counits of the scalar
equivalence, and values those two counits through presentations of their arguments as localized
complexes.

## Main results

* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_eq` — **the
  cancellation**: given any presentation of the inverse component as a morphism `w` followed by
  the scalar equivalence applied to a morphism `x` of the `ULift` world, its [stacks 0A63]
  transpose over `R` is the fixed-universe transpose of `x` alone, precomposed with the
  fixed-universe tensor of `w` read through one counit, and postcomposed with the other counit.
* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_comp` — the presentation:
  the last three of the four factors of
  `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app` are all images of the
  scalar equivalence, so they merge into one.
* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app` — **the
  uncurried inverse component, valued**: the two together.  Two counits of the scalar
  equivalence, the scalar equivalence of the scalar-restriction comparison, and one
  fixed-universe transpose.
* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`
  — the same value with those two counits read as the counit and the inverse unit of the scalar
  equivalence of [stacks 0E1W], so that the whole of it is in one vocabulary.
* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_counit_values`
  — the same value with the two counits replaced by arbitrary morphisms equal to them.
* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_presentations`
  — **the uncurried inverse component with no equivalence data left**: given a presentation of
  each of the two counits' arguments as isomorphic to a localized complex, every factor of the
  value is a component of `CategoryTheory.Functor.mapDerivedCategoryFactors`, a localization of
  the unit or the counit of the `ULift` equivalence of complexes, one of the two presentations,
  or one of `eF`, `modelRestrictScalarsNatIso`, `δ` and `τ`.

## Implementation notes

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_eq` and
`…_of_counit_values` take the presentation of the component and the values of the two counits as
hypotheses rather than substituting them. The counit values are large composites that `rw` cannot
put into the conclusion: the implicit instance arguments of
`CategoryTheory.Functor.mapDerivedCategoryFactors` there agree only at default transparency.

`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` and
`StacksDraft.DerivedHom.derivedScalarEquivalence` are the same equivalence read in the two
directions, but only their functors agree definitionally. The conclusion of
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app` spells the two
counits with `derivedScalarEquivalence` and the functors with `scalarEquivalence`;
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`
is the same value with the counits rewritten through the identification of the unit and counit
isomorphisms of the two equivalences in
`StacksFrontier.Homology.HomComplex.RHom.ScalarTransportReconciliation`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **The uncurried inverse component of [stacks 0E1W].**

Suppose the inverse component of the change-of-rings isomorphism at `(K, M)` is presented as a
morphism `w` into the scalar equivalence of an object `Z` of the `ULift` world, followed by that
equivalence applied to a morphism `x` of it.  Then the [stacks 0A63] transpose of the component
over `R` is the *fixed-universe* transpose of `x`, precomposed with the fixed-universe tensor of
`w` read through the counit of the one adjunction of the scalar equivalence and postcomposed with
the counit of the other. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_eq
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
    (w : (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).obj
          (Opposite.op (F.obj K.unop), M)) ⟶
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
        max uR uA uM} R).inverse.obj Z)
    (x : Z ⟶ (DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)).obj
      (Opposite.op ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
          max uR uA uM} R).functor.obj K.unop),
        (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
            max uR uA uM} R).functor.obj
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj M))),
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M) =
        w ≫ (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
          max uR uA uM} R).inverse.map x →
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
            ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).obj
              (Opposite.op (F.obj K.unop), M)))
          K.unop
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj M)
          ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M)) =
        (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
              max uR uA uM} R).inverse.map
            ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
                (((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                        max uR uA uM} R).functor.map w ≫
                    (derivedScalarEquivalence.{uR, max uR uA uM,
                      max uR uA uM + 1} R).symm.toAdjunction.counit.app Z,
                  𝟙 ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                    max uR uA uM} R).functor.obj K.unop)) :
                  (((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                          max uR uA uM} R).functor.obj
                        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                          ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA,
                            max uR uA uM} A).obj (Opposite.op (F.obj K.unop), M))),
                      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                        max uR uA uM} R).functor.obj K.unop) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (Z,
                      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                        max uR uA uM} R).functor.obj K.unop)) ≫
              DerivedInternalHom.Model.homEquiv Z
                ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                  max uR uA uM} R).functor.obj K.unop)
                ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                    max uR uA uM} R).functor.obj
                  ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj M)) x) ≫
          (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).toAdjunction.counit.app
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj M) := by
  intro F comparison hF K M Z w x h
  rw [h]
  exact derivedHomAdjunctionOverRing_homEquiv_comp_functor_map.{uR, max uR uA uM,
    max uR uA uM + 1} R _ K.unop _ Z w x

/-- **The inverse component of [stacks 0E1W] as one morphism followed by the scalar
equivalence.** The inverse component is the component of the scalar-restriction comparison `δ`
followed by the image under the scalar equivalence of the `ULift` world of a single morphism, the
composite of the last three of the four factors of
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app`. -/
public theorem derivedHomRestrictScalarsNatIso_inv_app_comp
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)),
    let a :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA
      uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA
      uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M) =
      δ.hom.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)) ≫
        E.inverse.map
          (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.hom.app K.unop).op
              (𝟙 (S.functor.obj M)))) ≫
            (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
                (Opposite.op (E.functor.obj K.unop), S.functor.obj M) ≫
              HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
                (τ.inv.app M))) := by
  intro F comparison hF K M a E S f' U V T a' δ τ eF HR HA
  rw [derivedHomRestrictScalarsNatIso_inv_app.{uR, uA, uM} f F comparison K M,
    ← Functor.map_comp, ← Functor.map_comp]

/-- **The uncurried inverse component of [stacks 0E1W], valued.** The [stacks 0A63] transpose
over `R` of the inverse component is the composite of two counits of the scalar equivalence, the
scalar equivalence of the scalar-restriction comparison `δ`, and one fixed-universe transpose, of
the comparison of the two derived extensions of scalars followed by the inverse representative
model comparison and the transported restriction comparison. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)),
    let a :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA
      uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA
      uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        (U.obj (S.inverse.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
          S.functor.obj M))))
        K.unop (U.obj M)
        ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M)) =
      E.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
              ((E.functor.map (δ.hom.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                      S.functor.obj M))) ≫
                  (derivedScalarEquivalence.{uR, max uR uA uM,
                      max uR uA uM + 1} R).symm.toAdjunction.counit.app
                    (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                      S.functor.obj M))),
                𝟙 (E.functor.obj K.unop)) :
                  ((E.functor.obj (U.obj (S.inverse.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))),
                      E.functor.obj K.unop) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                        S.functor.obj M)),
                      E.functor.obj K.unop)) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))
              (E.functor.obj K.unop) (E.functor.obj (U.obj M))
              (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.hom.app K.unop).op
                  (𝟙 (S.functor.obj M)))) ≫
                (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
                    (Opposite.op (E.functor.obj K.unop), S.functor.obj M) ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
                    (τ.inv.app M)))) ≫
        (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).toAdjunction.counit.app (U.obj M) := by
  intro F comparison hF K M a E S f' U V T a' δ τ eF HR HA
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_eq.{uR, uA, uM} f F comparison K M
    (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))
    (δ.hom.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))
    (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.hom.app K.unop).op
        (𝟙 (S.functor.obj M)))) ≫
      (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
          (Opposite.op (E.functor.obj K.unop), S.functor.obj M) ≫
        HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
          (τ.inv.app M)))
    (derivedHomRestrictScalarsNatIso_inv_app_comp.{uR, uA, uM} f F comparison K M)

/-- **The uncurried inverse component of [stacks 0E1W] in a single vocabulary.**
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app` with its two
counits of `StacksDraft.DerivedHom.derivedScalarEquivalence` written as the counit isomorphism and
the inverse unit isomorphism of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, the equivalence
[stacks 0E1W] is stated with. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)),
    let a :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA
      uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA
      uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        (U.obj (S.inverse.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
          S.functor.obj M))))
        K.unop (U.obj M)
        ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M)) =
      E.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
              ((E.functor.map (δ.hom.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                      S.functor.obj M))) ≫
                  E.counitIso.hom.app
                    (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                      S.functor.obj M))),
                𝟙 (E.functor.obj K.unop)) :
                  ((E.functor.obj (U.obj (S.inverse.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))),
                      E.functor.obj K.unop) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                        S.functor.obj M)),
                      E.functor.obj K.unop)) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))
              (E.functor.obj K.unop) (E.functor.obj (U.obj M))
              (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.hom.app K.unop).op
                  (𝟙 (S.functor.obj M)))) ≫
                (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
                    (Opposite.op (E.functor.obj K.unop), S.functor.obj M) ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
                    (τ.inv.app M)))) ≫
        E.unitIso.inv.app (U.obj M) := by
  intro F comparison hF K M a E S f' U V T a' δ τ eF HR HA
  rw [← ScalarTransportedInternalHom.derivedScalarEquivalence_symm_counit_app.{uR,
      max uR uA uM, max uR uA uM + 1} R,
    ← ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app.{uR,
      max uR uA uM, max uR uA uM + 1} R]
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app.{uR, uA, uM} f F comparison K M

/-- **The uncurried inverse component of [stacks 0E1W] with its two counits passed in.**
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app` with the two
counits of `StacksDraft.DerivedHom.derivedScalarEquivalence` in its value replaced by arbitrary
morphisms `c₁` and `c₂` equal to them. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_counit_values
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)),
    let a :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA
      uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA
      uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    ∀ (c₁ : E.functor.obj (E.inverse.obj (V.obj (HA.obj
            (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))) ⟶
          V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))
    (c₂ : E.inverse.obj (E.functor.obj (U.obj M)) ⟶ U.obj M)
    (_hc₁ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).symm.toAdjunction.counit.app
        (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M))) = c₁)
    (_hc₂ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).toAdjunction.counit.app (U.obj M) = c₂),
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        (U.obj (S.inverse.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
          S.functor.obj M))))
        K.unop (U.obj M)
        ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M)) =
      E.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
              ((E.functor.map (δ.hom.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                      S.functor.obj M))) ≫
                  c₁,
                𝟙 (E.functor.obj K.unop)) :
                  ((E.functor.obj (U.obj (S.inverse.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))),
                      E.functor.obj K.unop) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                        S.functor.obj M)),
                      E.functor.obj K.unop)) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))
              (E.functor.obj K.unop) (E.functor.obj (U.obj M))
              (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.hom.app K.unop).op
                  (𝟙 (S.functor.obj M)))) ≫
                (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
                    (Opposite.op (E.functor.obj K.unop), S.functor.obj M) ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
                    (τ.inv.app M)))) ≫
        c₂ := by
  intro F comparison hF K M a E S f' U V T a' δ τ eF HR HA c₁ c₂ hc₁ hc₂
  subst hc₁ hc₂
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app.{uR, uA, uM} f F comparison K M

/-- **The uncurried inverse component of [stacks 0E1W] with no equivalence data left.**

Given presentations `e₁` and `e₂` of the arguments of the two counits of
`StacksDraft.DerivedHom.derivedScalarEquivalence` left by
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app` as localized
complexes, the [stacks 0A63] transpose over `R` of the inverse component is a composite of: the
two components of `CategoryTheory.Functor.mapDerivedCategoryFactors` for the two restriction
functors of the `ULift` equivalence, the localization of the unit and of the counit of that
equivalence of complexes, the two presentations, the comparison of the two derived extensions of
scalars `eF`, the representative model comparison `modelRestrictScalarsNatIso`, and the two
components of the scalar-restriction comparison `δ` and `τ`. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_presentations
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)),
    let a :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA
      uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA
      uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    ∀ (Z : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
    (e₁ : V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)) ≅
      DerivedCategory.Q.obj Z)
    (W : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (e₂ : U.obj M ≅ DerivedCategory.Q.obj W),
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        (U.obj (S.inverse.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
          S.functor.obj M))))
        K.unop (U.obj M)
        ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M)) =
      E.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
              ((E.functor.map (δ.hom.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                      S.functor.obj M))) ≫
                  ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).inverse.map
                        ((derivedScalarEquivalence.{uR, max uR uA uM,
                          max uR uA uM + 1} R).functor.map e₁.hom) ≫
                      ((uliftModuleEquivalence.{uR, max uR uA uM,
                              max uR uA uM} R).inverse.mapDerivedCategory.map
                            ((uliftModuleEquivalence.{uR, max uR uA uM,
                              max uR uA uM} R).functor.mapDerivedCategoryFactors.hom.app Z) ≫
                          (uliftModuleEquivalence.{uR, max uR uA uM,
                              max uR uA uM} R).inverse.mapDerivedCategoryFactors.hom.app
                              ((ScalarTransportedInternalHom.uliftComplexEquivalence.{uR,
                                max uR uA uM} R).functor.obj Z) ≫
                            DerivedCategory.Q.map
                              ((ScalarTransportedInternalHom.uliftComplexEquivalence.{uR,
                                max uR uA uM} R).unitIso.inv.app Z)) ≫
                    e₁.inv),
                𝟙 (E.functor.obj K.unop)) :
                  ((E.functor.obj (U.obj (S.inverse.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))),
                      E.functor.obj K.unop) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)),
                        S.functor.obj M)),
                      E.functor.obj K.unop)) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)))
              (E.functor.obj K.unop) (E.functor.obj (U.obj M))
              (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.hom.app K.unop).op
                  (𝟙 (S.functor.obj M)))) ≫
                (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
                    (Opposite.op (E.functor.obj K.unop), S.functor.obj M) ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
                    (τ.inv.app M)))) ≫
        ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
              ((derivedScalarEquivalence.{uR, max uR uA uM,
                max uR uA uM + 1} R).inverse.map e₂.hom) ≫
            ((uliftModuleEquivalence.{uR, max uR uA uM,
                    max uR uA uM} R).functor.mapDerivedCategory.map
                  ((uliftModuleEquivalence.{uR, max uR uA uM,
                    max uR uA uM} R).inverse.mapDerivedCategoryFactors.hom.app W) ≫
                (uliftModuleEquivalence.{uR, max uR uA uM,
                    max uR uA uM} R).functor.mapDerivedCategoryFactors.hom.app
                    ((ScalarTransportedInternalHom.uliftComplexEquivalence.{uR,
                      max uR uA uM} R).inverse.obj W) ≫
                  DerivedCategory.Q.map
                    ((ScalarTransportedInternalHom.uliftComplexEquivalence.{uR,
                      max uR uA uM} R).counitIso.hom.app W)) ≫
          e₂.inv) := by
  intro F comparison hF K M a E S f' U V T a' δ τ eF HR HA Z e₁ W e₂
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_counit_values.{uR, uA, uM} f F
    comparison K M _ _
    (ScalarTransportedInternalHom.derivedScalarEquivalence_symm_counit_app_of_iso.{uR,
      max uR uA uM, max uR uA uM + 1} R _ Z e₁)
    (ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app_of_iso.{uR,
      max uR uA uM, max uR uA uM + 1} R _ W e₂)

end Stacks.DerivedHom.BaseChange
end
