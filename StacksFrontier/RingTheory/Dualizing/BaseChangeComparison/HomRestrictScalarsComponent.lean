module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.KFlatKInjectiveJoin
public import StacksFrontier.Homology.HomComplex.RHom.BaseChangeLiftIso
import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionTransport

/-!
# A component formula for the change-of-rings isomorphism of derived Hom

`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso` — [stacks 0E1W] — is built from
four factors, and `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app` displays
them: the transported restriction comparison `τ`, the descended model comparison
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso`, the comparison of derived extension of
scalars with the scalar lift, and the inverse scalar-restriction comparison `δ`. This file
evaluates the model comparison by
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_hom_app_of_iso` and the third factor by
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_inv_app`, so that every factor of the
resulting formula is a unit or counit of one of the four adjunctions in play, the
scalar-restriction comparison, or the representative model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` at an explicit K-flat/K-injective
pair.

## Main results

* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective` — **the
  component formula for [stacks 0E1W]**, given a K-flat representative of the scalar lift of the
  contravariant variable and a K-injective representative of the scalar lift of the covariant one.
* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` — the
  same formula with the fourth factor evaluated too: the three occurrences of the
  scalar-restriction comparison are moved to classes of cochain complexes, where
  `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q` and
  `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_Q` evaluate them, and the transported
  comparison `τ` is expanded into a unit, a component of that comparison, and a counit.
* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app` — **the inverse of the
  composite**, in the four named factors of
  `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app`.
* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective` — **the
  inverse component formula for [stacks 0E1W]**, at the same data as the forward one.  Each factor
  is read in the direction that inverts nothing: the representative model comparison through its
  `inv`, which
  `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` values, and
  the comparison of the two derived extensions of scalars through its `hom`, expanded by
  `CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app`.
* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective_Q` — the
  same with every scalar-restriction comparison at a class.  Its three representatives are not
  the forward formula's: the comparison of the two derived extensions of scalars is read the other
  way round, so the object needing a representative is the scalar lift of `F K` rather than the
  derived base change of the lift of `K`.

## Implementation notes

`Stacks.DerivedHom.BaseChange.exists_kFlatKInjectiveJoin` produces the two representatives and the
K-injective resolution for any pair of objects, so the formulas apply at every component of the
isomorphism.

The statement repeats the `letI` instances and the `let` abbreviations of
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app` verbatim, and binds the
third factor by an ascribed `let` to
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso`, which is definitionally the local
`let` of that statement.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1V](https://stacks.math.columbia.edu/tag/0E1V)
-/

section HomRestrictScalarsComponent

open CategoryTheory StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChange

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- **The component formula for [stacks 0E1W].**

Let `f : R → A` be a homomorphism of commutative rings and `F` a total left derived functor of
extension of scalars along `f`.  Let `K₀` be a K-flat complex representing the scalar lift
`E.functor K` of the contravariant variable, `J` a K-injective complex representing the scalar
lift `S.functor M` of the covariant variable, and `q : J|_{R'} ⟶ I` a K-injective resolution of
the restriction of `J` along the lifted ring map.  Then the component of the change-of-rings
isomorphism at `(K, M)` is the displayed composite of four named morphisms: the transported
restriction comparison `τ`; the representative model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` at `(K₀, J, I, q)`, conjugated by
the two representations; the comparison of derived extension of scalars with the scalar lift,
expanded by `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_inv_app` into the units
and counits of the four adjunctions; and the inverse scalar-restriction comparison `δ`. -/
public theorem derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective
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
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    ∀ (K₀ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q] (hK₀ : K₀.KFlat)
      (eX : E.functor.obj K.unop ≅ DerivedCategory.Q.obj K₀)
      (eY : S.functor.obj M ≅ DerivedCategory.Q.obj J),
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).hom.app (K, M) =
      E.inverse.map (HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
          (τ.hom.app M))) ≫
        E.inverse.map ((homRestrictSource f').map
              (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
            (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q hK₀).hom ≫
              (homRestrictTarget f' T.B).map
                (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
          E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom
              (S.functor.map (F.map (E.toAdjunction.unit.app K.unop ≫
                    E.inverse.map (a'.unit.app (E.functor.obj K.unop)))) ≫
                  S.functor.map (F.map (δ.inv.app (T.B.obj (E.functor.obj K.unop)))) ≫
                    S.functor.map
                        (a.counit.app (S.inverse.obj (T.B.obj (E.functor.obj K.unop)))) ≫
                      S.toAdjunction.counit.app (T.B.obj (E.functor.obj K.unop))).op
              (𝟙 (S.functor.obj M))))) ≫
            δ.inv.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)) := by
  intro F comparison hF K M a E S f' U V T a' δ τ HR HA K₀ J I hJ hI q hq hK₀ eX eY
  rw [derivedHomRestrictScalarsNatIso_hom_app.{uR, uA, uM} f F comparison K M,
    modelRestrictScalarsNatIso_hom_app_of_iso f' T.B T.alphaB K₀ J I q hK₀ eX eY,
    Adjunction.leftAdjointUniq_comp_ofNatIsoRight_inv_app]

/-- **The component formula for [stacks 0E1W], with every scalar-restriction comparison at a
class.**

`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective` leaves the
comparison `δ` at three objects, none of them presented as the class of a cochain complex: the
internal-Hom object of the two scalar lifts, the derived base change of the contravariant lift,
and — inside the transported comparison `τ` — the scalar lift of the covariant variable.  Given
isomorphisms of those three objects with classes, every occurrence of `δ` here is at a class, where
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q` and
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_Q` evaluate it; and `τ` has disappeared
in favour of a unit of the scalar lift over `A`, a component of `δ`, and a counit of the scalar
lift over `R`. -/
public theorem derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q
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
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    ∀ (X₁ X₂ X₃ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (e₁ : HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M) ≅
        DerivedCategory.Q.obj X₁)
      (e₂ : T.B.obj (E.functor.obj K.unop) ≅ DerivedCategory.Q.obj X₂)
      (e₃ : S.functor.obj M ≅ DerivedCategory.Q.obj X₃)
      (K₀ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q] (hK₀ : K₀.KFlat)
      (eX : E.functor.obj K.unop ≅ DerivedCategory.Q.obj K₀)
      (eY : S.functor.obj M ≅ DerivedCategory.Q.obj J),
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).hom.app (K, M) =
      E.inverse.map (HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
          (E.functor.map (U.map (S.unitIso.hom.app M) ≫ U.map (S.inverse.map e₃.hom) ≫
              δ.hom.app (DerivedCategory.Q.obj X₃) ≫ E.inverse.map (V.map e₃.inv)) ≫
            E.counitIso.hom.app (V.obj (S.functor.obj M))))) ≫
        E.inverse.map ((homRestrictSource f').map
              (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
            (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q hK₀).hom ≫
              (homRestrictTarget f' T.B).map
                (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
          E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom
              (S.functor.map (F.map (E.toAdjunction.unit.app K.unop ≫
                    E.inverse.map (a'.unit.app (E.functor.obj K.unop)))) ≫
                  S.functor.map (F.map ((V ⋙ E.inverse).map e₂.hom ≫
                      δ.inv.app (DerivedCategory.Q.obj X₂) ≫
                        (S.inverse ⋙ U).map e₂.inv)) ≫
                    S.functor.map
                        (a.counit.app (S.inverse.obj (T.B.obj (E.functor.obj K.unop)))) ≫
                      S.toAdjunction.counit.app (T.B.obj (E.functor.obj K.unop))).op
              (𝟙 (S.functor.obj M))))) ≫
            (V ⋙ E.inverse).map e₁.hom ≫
              δ.inv.app (DerivedCategory.Q.obj X₁) ≫ (S.inverse ⋙ U).map e₁.inv := by
  intro F comparison hF K M a E S f' U V T a' δ HR HA X₁ X₂ X₃ e₁ e₂ e₃ K₀ J I hJ hI q hq hK₀
    eX eY
  rw [derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective.{uR, uA, uM} f F comparison K M
      K₀ J I q hK₀ eX eY,
    scalarRestrictionTransportedIso_hom_app.{uR, uA, uM} f M,
    scalarRestrictionIso_hom_app_of_iso.{uR, uA, uM} f _ X₃ e₃,
    scalarRestrictionIso_inv_app_of_iso.{uR, uA, uM} f _ X₂ e₂,
    scalarRestrictionIso_inv_app_of_iso.{uR, uA, uM} f _ X₁ e₁]

/-- **The inverse component of [stacks 0E1W], in the four named factors.**

`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app` displays the component of
the change-of-rings isomorphism as a composite of four factors, each of them a component of an
isomorphism; this is the inverse of that composite, the four inverses in the opposite order.  The
transported restriction comparison `τ`, the model comparison `modelRestrictScalarsNatIso` and the
scalar-restriction comparison `δ` are simply read in the other direction, and the comparison `eF`
of the two derived extensions of scalars — the factor whose expansion into units and counits is
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_inv_app` — appears through its `hom`,
which `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app` expands. -/
public theorem derivedHomRestrictScalarsNatIso_inv_app
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
        E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.hom.app K.unop).op
          (𝟙 (S.functor.obj M))))) ≫
        E.inverse.map ((modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
          (Opposite.op (E.functor.obj K.unop), S.functor.obj M)) ≫
        E.inverse.map (HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
          (τ.inv.app M))) := by
  intro _ _ _ _ F comparison _ K M
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

/-- **The inverse component formula for [stacks 0E1W].**

The companion of
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective`, at the
same data: a K-flat representative `K₀` of the scalar lift of the contravariant variable, a
K-injective representative `J` of the scalar lift of the covariant one, and a K-injective
resolution `q` of the restriction of `J`.  The inverse component at `(K, M)` is the scalar
restriction comparison `δ`; the comparison of the two derived extensions of scalars, now read
forwards and expanded into the units and counits of the four adjunctions; the *inverse* of the
representative model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`, conjugated by the two
representations; and the transported restriction comparison `τ` read backwards. -/
public theorem derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective
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
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    ∀ (K₀ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q] (hK₀ : K₀.KFlat)
      (eX : E.functor.obj K.unop ≅ DerivedCategory.Q.obj K₀)
      (eY : S.functor.obj M ≅ DerivedCategory.Q.obj J),
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M) =
      δ.hom.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)) ≫
        E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom
            (T.B.map (E.functor.map (a.unit.app K.unop)) ≫
                T.B.map (E.functor.map (U.map (S.toAdjunction.unit.app (F.obj K.unop)))) ≫
                  T.B.map (E.functor.map (δ.hom.app (S.functor.obj (F.obj K.unop)))) ≫
                    T.B.map (E.toAdjunction.counit.app
                      (V.obj (S.functor.obj (F.obj K.unop)))) ≫
                      a'.counit.app (S.functor.obj (F.obj K.unop))).op
            (𝟙 (S.functor.obj M))))) ≫
          E.inverse.map ((homRestrictTarget f' T.B).map
                (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
              (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q hK₀).inv ≫
                (homRestrictSource f').map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
            E.inverse.map (HR.map (CategoryTheory.Prod.mkHom
              (𝟙 (Opposite.op (E.functor.obj K.unop))) (τ.inv.app M))) := by
  intro F comparison hF K M a E S f' U V T a' δ τ HR HA K₀ J I hJ hI q hq hK₀ eX eY
  rw [derivedHomRestrictScalarsNatIso_inv_app.{uR, uA, uM} f F comparison K M,
    modelRestrictScalarsNatIso_inv_app_of_iso f' T.B T.alphaB K₀ J I q hK₀ eX eY,
    Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app]

/-- **The inverse component formula for [stacks 0E1W], with every scalar-restriction comparison at
a class.**

The companion of
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q`.
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective` leaves the
comparison `δ` at three objects, none of them a class: the internal-Hom object of the two scalar
lifts, the scalar lift of the covariant variable, and — inside the comparison of the two derived
extensions of scalars — the scalar lift of `F K`.  The third of those is *not* the object at which
the forward formula leaves `δ`: that one is the derived base change `T.B (E K)` of the
contravariant lift, and the two are the two ends of the comparison, so the inverse formula needs a
representative of the other end.  Given representatives of the three, every occurrence of `δ` is
at a class, where `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q` and
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_Q` evaluate it; and the transported
comparison `τ` has disappeared in favour of a counit of the scalar lift over `R`, a component of
`δ`, and a unit of the scalar lift over `A`. -/
public theorem derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective_Q
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
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    ∀ (X₁ X₂ X₃ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (e₁ : HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M) ≅
        DerivedCategory.Q.obj X₁)
      (e₂ : S.functor.obj (F.obj K.unop) ≅ DerivedCategory.Q.obj X₂)
      (e₃ : S.functor.obj M ≅ DerivedCategory.Q.obj X₃)
      (K₀ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q] (hK₀ : K₀.KFlat)
      (eX : E.functor.obj K.unop ≅ DerivedCategory.Q.obj K₀)
      (eY : S.functor.obj M ≅ DerivedCategory.Q.obj J),
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app (K, M) =
      (U.map (S.inverse.map e₁.hom) ≫ δ.hom.app (DerivedCategory.Q.obj X₁) ≫
          E.inverse.map (V.map e₁.inv)) ≫
        E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom
            (T.B.map (E.functor.map (a.unit.app K.unop)) ≫
                T.B.map (E.functor.map (U.map (S.toAdjunction.unit.app (F.obj K.unop)))) ≫
                  T.B.map (E.functor.map (U.map (S.inverse.map e₂.hom) ≫
                      δ.hom.app (DerivedCategory.Q.obj X₂) ≫
                        E.inverse.map (V.map e₂.inv))) ≫
                    T.B.map (E.toAdjunction.counit.app
                      (V.obj (S.functor.obj (F.obj K.unop)))) ≫
                      a'.counit.app (S.functor.obj (F.obj K.unop))).op
            (𝟙 (S.functor.obj M))))) ≫
          E.inverse.map ((homRestrictTarget f' T.B).map
                (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
              (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q hK₀).inv ≫
                (homRestrictSource f').map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
            E.inverse.map (HR.map (CategoryTheory.Prod.mkHom
              (𝟙 (Opposite.op (E.functor.obj K.unop)))
              (E.counitIso.inv.app (V.obj (S.functor.obj M)) ≫
                E.functor.map (((V ⋙ E.inverse).map e₃.hom ≫
                    δ.inv.app (DerivedCategory.Q.obj X₃) ≫
                      (S.inverse ⋙ U).map e₃.inv) ≫
                  U.map (S.unitIso.inv.app M))))) := by
  intro F comparison hF K M a E S f' U V T a' δ HR HA X₁ X₂ X₃ e₁ e₂ e₃ K₀ J I hJ hI q hq hK₀
    eX eY
  rw [derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective.{uR, uA, uM} f F comparison K M
      K₀ J I q hK₀ eX eY,
    scalarRestrictionTransportedIso_inv_app.{uR, uA, uM} f M,
    scalarRestrictionIso_inv_app_of_iso.{uR, uA, uM} f _ X₃ e₃,
    scalarRestrictionIso_hom_app_of_iso.{uR, uA, uM} f _ X₂ e₂,
    scalarRestrictionIso_hom_app_of_iso.{uR, uA, uM} f _ X₁ e₁]

end Stacks.DerivedHom.BaseChange

end HomRestrictScalarsComponent
