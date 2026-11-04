module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTranspose
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLiftInverse

/-!
# The uncurried inverse component of [stacks 0E1W] with its one content factor passed in

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app` values the
[stacks 0A63] transpose `ψ` of the inverse component of [stacks 0E1W] in six factors.  Five are
transport — two counits of the scalar equivalence, the scalar equivalence of the scalar-restriction
comparison `δ`, the comparison `eF` of the two derived extensions of scalars, and the transported
restriction comparison `τ` — and one carries the mathematics: the inverse component of the
descended comparison `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso` at the scalar lift
of the ring map.

`…_of_counit_values` already takes the two counits as hypotheses rather than substituting them,
because neither of them sits at a class and a consumer may hold several presentations of its
argument.  The content factor is in the same position for the same reason: its value depends on a
K-flat presentation of the contravariant variable and a K-injective presentation of the covariant
one, and at the keystone's pair those are
`Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` and
`Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift`, while another consumer may hold others.

So this file widens the hypothesis list by one: `ψ`'s value holds with whatever a consumer can
prove the content factor to be.  As with the counits the value is passed as a local variable, which
`subst` eliminates with no matching — the composite being far past the size at which `rw` fails on
two sides that print identically, the implicit instance arguments of
`CategoryTheory.Functor.mapDerivedCategoryFactors` being elaborated in different files and agreeing
only at default transparency.

The value to pass at the keystone's pair is
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap`, in
which the factor is the canonical chain-level map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` of [stacks 0E1W] and nothing else.

**What is not done here.**  No tag is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open: this is the
substitution hook for one factor of the identification `hmu`, and it says nothing about the
comparison identity `h`, whose frontier is
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_model_value`
  — the uncurried inverse component with the two counits **and** the descended comparison's
  inverse component all passed in.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **The uncurried inverse component of [stacks 0E1W] with its two counits and its one content
factor passed in.**

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_counit_values`
with a third hypothesis: the inverse component of the descended comparison
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso` at the scalar lift `f'`, read at the
contravariant object `E (K.unop)` and the covariant object `S M`, is also taken as a value rather
than written out.  That factor is the only one of the six carrying mathematics, every other being
a unit, a counit or a localization comparison, and its value depends on presentations of the two
variables that the consumer chooses.

At the keystone's pair the value to pass is
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap`,
whose only non-transport factor is the chain-level map of [stacks 0E1W]. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_model_value
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
    (m : V.obj (HA.obj (Opposite.op (T.B.obj (E.functor.obj K.unop)), S.functor.obj M)) ⟶
      HR.obj (Opposite.op (E.functor.obj K.unop), V.obj (S.functor.obj M)))
    (_hc₁ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).symm.toAdjunction.counit.app
        (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M))) = c₁)
    (_hc₂ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).toAdjunction.counit.app (U.obj M) = c₂)
    (_hm : (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
        (Opposite.op (E.functor.obj K.unop), S.functor.obj M) = m),
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
                m ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
                    (τ.inv.app M)))) ≫
        c₂ := by
  intro F comparison hF K M a E S f' U V T a' δ τ eF HR HA c₁ c₂ m hc₁ hc₂ hm
  have := hF
  subst hc₁ hc₂ hm
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app.{uR, uA, uM} f F comparison K M

/-- **The uncurried inverse component of [stacks 0E1W] at the keystone's pair, with its content
factor at its floor.**

`Dualizing.tensorBaseChangeMor_eq_of_kFlat_tensorTranspose` leaves one unknown, the [stacks 0A63]
transpose `ψ` of the inverse component of [stacks 0E1W] read at the contravariant object `Q L` and
the covariant object `F (Q K ⊗ᴸ_R Q L)` for a K-flat pair `K`, `L`.  This is the composition of
the two halves of its value:
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_model_value`
supplies the shape, and
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap`
supplies the one factor of it that is not transport.

What is left in the value is: the two counits `c₁` and `c₂`, still hypotheses because neither sits
at a class; the scalar equivalence of the scalar-restriction comparison `δ` and of the transported
one `τ`; the comparison `eF` of the two derived extensions of scalars; the two K-flat
presentations `eX` and `eY`; and, inside two nested fixed-universe transposes, the canonical
chain-level map `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` of [stacks 0E1W]
uninverted.

**This is the side of the keystone's `hmu` that the [stacks 068I] candidate has to be compared
with**, the candidate's own value being
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` and the right-hand side of the equation the unit of
[stacks 0GMT], valued by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_model`.
The equation itself is not proved here and no caveat is lifted. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat
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
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : CochainComplex.DerivedTensor.IsKFlat.{uR, max uR uA uM} K)
    (hL : CochainComplex.DerivedTensor.IsKFlat.{uR, max uR uA uM} L),
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
    let M := F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            ((CochainComplex.DerivedTensor.extensionOfScalarsCochain.{uR, uA,
              max uR uA uM} f).obj (CochainComplex.DerivedTensor.tensorComplex.{uR,
                max uR uA uM} K L))
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    letI : IsIso (T.alphaB.app K₀) :=
      isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    letI := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let eX := scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    ∀ (c₁ : E.functor.obj (E.inverse.obj (V.obj (HA.obj
            (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
              S.functor.obj M)))) ⟶
          V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
            S.functor.obj M)))
    (c₂ : E.inverse.obj (E.functor.obj (U.obj M)) ⟶ U.obj M)
    (_hc₁ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).symm.toAdjunction.counit.app
        (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
          S.functor.obj M))) = c₁)
    (_hc₂ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).toAdjunction.counit.app (U.obj M) = c₂),
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        (U.obj (S.inverse.obj (HA.obj
          (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))), S.functor.obj M))))
        (DerivedCategory.Q.obj L) (U.obj M)
        ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app
          (Opposite.op (DerivedCategory.Q.obj L), M)) =
      E.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
              ((E.functor.map (δ.hom.app (HA.obj
                      (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                        S.functor.obj M))) ≫
                  c₁,
                𝟙 (E.functor.obj (DerivedCategory.Q.obj L))) :
                  ((E.functor.obj (U.obj (S.inverse.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                          S.functor.obj M)))),
                      E.functor.obj (DerivedCategory.Q.obj L)) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (V.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                          S.functor.obj M)),
                      E.functor.obj (DerivedCategory.Q.obj L))) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                S.functor.obj M)))
              (E.functor.obj (DerivedCategory.Q.obj L)) (E.functor.obj (U.obj M))
              (V.map (HA.map (CategoryTheory.Prod.mkHom
                  (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M)))) ≫
                ((homRestrictTarget f' T.B).map
                      (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
                    (V.map (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM,
                            max uR uA uM, max uR uA uM} f').obj K₀) J
                          (asIso (T.alphaB.app K₀)) (Iso.refl _)).hom ≫
                        ((ModuleCat.restrictScalars.{max uR uA uM}
                            f').mapDerivedCategoryFactors.app Z).hom ≫
                          ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
                              (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
                            (((DerivedInternalHom.Model.adjunction
                                  (ULift.{max uR uA uM} R)).tensorIso P K₀
                                (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
                              DerivedCategory.Q.map
                                (DerivedInternalHom.Model.uncurry
                                  (homComplexChangeOfRingsMap f' K₀ J I q)))) ≫
                            ((DerivedInternalHom.Model.adjunction
                                (ULift.{max uR uA uM} R)).homIso K₀ I).hom ≫
                              (homModelIso K₀ I (Iso.refl _)
                                ((ModuleCat.restrictScalars.{max uR uA uM}
                                    f').mapDerivedCategoryFactors.app J ≪≫
                                  @asIso _ _ _ _ (DerivedCategory.Q.map q)
                                    ((DerivedCategory.isIso_Q_map_iff_quasiIso _
                                      q).2 inferInstance))).inv) ≫
                      (homRestrictSource f').map
                        (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
                  HR.map (CategoryTheory.Prod.mkHom
                    (𝟙 (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L))))
                    (τ.inv.app M)))) ≫
        c₂ := by
  intro F comparison hF K L hK hL a E S f' U V T a' δ τ eF HR HA M X₃ K₀ J I hJ hI q hq n hn
    eX eY Z P c₁ c₂ hc₁ hc₂
  have := hF
  have := hJ
  have := hI
  have := hq
  have := hn
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_model_value.{uR, uA, uM} f F
    comparison (Opposite.op (DerivedCategory.Q.obj L)) M c₁ c₂ _ hc₁ hc₂
    (modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap.{uR, uA, uM} f F comparison
      K L hK hL J I q n)

end Stacks.DerivedHom.BaseChange

end
