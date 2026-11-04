module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.CategoryTheory.Adjunction.UniqueCompApp

/-!
# The comparison of derived extension of scalars with the scalar lift

The tagged change-of-rings isomorphism for derived Hom,
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso`, is assembled from four factors,
and `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app` names three of them:
the scalar-restriction comparison `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, the
transported restriction comparison built from it, and the descended model comparison
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso`.  The fourth factor is the canonical
comparison between *lift scalars to a common universe, then extend along the lifted ring map* and
*extend along the original ring map, then lift scalars*.

Both composites are left adjoint to one and the same functor — derived restriction along the
lifted ring map followed by the inverse scalar lift — the first by composing the scalar-lift
equivalence with the derived extension–restriction adjunction over the lifted rings, the second
by composing over the original rings and then transporting along
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, and the comparison is the uniqueness
isomorphism of these two left adjoints.  This file defines it and computes its components.

## Main definitions

* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso`: the comparison itself, the
  isomorphism `E.functor ⋙ T.B ≅ F ⋙ S.functor` of the fourth factor.

## Main results

* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_eq`: the comparison is the
  uniqueness isomorphism of the two composite left adjoints.
* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_inv_app`: **the component
  formula**, in the inverse direction.  Each component is a composite of the unit of the
  scalar-lift equivalence, the unit of the derived extension–restriction adjunction over the
  lifted rings, the inverse scalar-restriction comparison, and the two counits over the original
  rings.
* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app`: the companion formula
  in the forward direction.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

section ScalarLiftComparison

open CategoryTheory StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChange

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- **The comparison of derived extension of scalars with the scalar lift.**

Let `f : R → A` be a homomorphism of commutative rings, let `F` be a total left derived functor
of extension of scalars along `f` with comparison `comparison`, let `E` and `S` be the
scalar-lift equivalences over `R` and over `A`, and let `T.B` be the canonical model of derived
extension of scalars along the lifted ring map `f'`.  Then `E.functor ⋙ T.B` and `F ⋙ S.functor`
are both left adjoint to `V ⋙ E.inverse`, the second one through
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, and this is the resulting comparison. -/
public noncomputable def derivedExtensionScalarsLiftIso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))],
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
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    (E.functor ⋙ T.B ≅ F ⋙ S.functor) := by
  intro F comparison hF E S f' T
  have := hF
  letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  exact (E.toAdjunction.comp
      (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
        _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB)).leftAdjointUniq
    (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison).comp S.toAdjunction).ofNatIsoRight (scalarRestrictionIso.{uR, uA, uM} f))

/-- `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso` is the uniqueness isomorphism
of the two composite left adjoints: the scalar lift composed with derived extension over the
lifted rings, and derived extension over the original rings composed with the scalar lift and
transported along `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`. -/
public theorem derivedExtensionScalarsLiftIso_eq
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))],
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
    derivedExtensionScalarsLiftIso.{uR, uA, uM} f F comparison =
      (E.toAdjunction.comp a').leftAdjointUniq
        ((a.comp S.toAdjunction).ofNatIsoRight δ) := by
  intro F comparison hF _a _E _S _f' _U _V _T _a' _δ
  rfl

/-- **The component formula for `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso`,
inverse direction.**

The component at `K` of the inverse of
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso` is the composite of: the unit of
the scalar-lift equivalence over `R` followed by the unit of derived extension of scalars over
the lifted rings, carried into `D(A)` by `F` and then lifted by `S.functor`; the inverse
scalar-restriction comparison `δ`, likewise carried over; the counit of derived extension of
scalars over the original rings, lifted; and the counit of the scalar-lift equivalence over `A`.
-/
public theorem derivedExtensionScalarsLiftIso_inv_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max uR uA uM} R)),
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
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      derivedExtensionScalarsLiftIso.{uR, uA, uM} f F comparison
    eF.inv.app K =
      S.functor.map (F.map (E.toAdjunction.unit.app K ≫
          E.inverse.map (a'.unit.app (E.functor.obj K)))) ≫
        S.functor.map (F.map (δ.inv.app (T.B.obj (E.functor.obj K)))) ≫
          S.functor.map (a.counit.app (S.inverse.obj (T.B.obj (E.functor.obj K)))) ≫
            S.toAdjunction.counit.app (T.B.obj (E.functor.obj K)) := by
  intro F comparison hF K a E S f' U V T a' δ eF
  exact Adjunction.leftAdjointUniq_comp_ofNatIsoRight_inv_app E.toAdjunction a' a
    S.toAdjunction δ K

/-- **The component formula for `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso`,
forward direction.**

The forward component is built from the unit of derived extension of scalars over the original
rings and the unit of the scalar-lift equivalence over `A`, then the scalar-restriction comparison
`δ`, then the counit of the scalar-lift equivalence over `R` and the counit of derived extension
of scalars over the lifted rings. -/
public theorem derivedExtensionScalarsLiftIso_hom_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max uR uA uM} R)),
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
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      derivedExtensionScalarsLiftIso.{uR, uA, uM} f F comparison
    eF.hom.app K =
      T.B.map (E.functor.map (a.unit.app K)) ≫
        T.B.map (E.functor.map (U.map (S.toAdjunction.unit.app (F.obj K)))) ≫
          T.B.map (E.functor.map (δ.hom.app (S.functor.obj (F.obj K)))) ≫
            T.B.map (E.toAdjunction.counit.app (V.obj (S.functor.obj (F.obj K)))) ≫
              a'.counit.app (S.functor.obj (F.obj K)) := by
  intro F comparison hF K a E S f' U V T a' δ eF
  exact Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app E.toAdjunction a' a
    S.toAdjunction δ K

end Stacks.DerivedHom.BaseChange

end ScalarLiftComparison
