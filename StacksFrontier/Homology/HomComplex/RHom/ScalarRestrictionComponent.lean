module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexChangeOfRings
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelRestrictScalars

/-!
# The components of the scalar-restriction comparison

`Stacks.DerivedHom.BaseChange.scalarRestrictionIso` is the comparison `δ` identifying *lift the
scalars, then restrict along the lifted ring map, then lift back* with *restrict along the
original ring map*, on derived categories.  It is one of the four factors of the change-of-rings
isomorphism for derived Hom, and it also occurs inside the transported restriction comparison `τ`
of that factorization.  This file computes its components at the class `DerivedCategory.Q.obj X`
of a cochain complex, as a composite of six named morphisms.

## Main results

* `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q` and
  `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_Q` — **the component formulas for
  `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`**, at the class of a cochain complex.  Every
  factor is a `CategoryTheory.Functor.mapDerivedCategoryFactors`, a
  `CategoryTheory.Functor.mapHomologicalComplexCompIso` of one of the two evident comparisons of
  restriction functors, or `DerivedCategory.Q` of such.
* `Stacks.DerivedHom.BaseChange.scalarEquivalenceInverseFactors` — the factorization of the
  inverse of the scalar-lift equivalence through `DerivedCategory.Q`.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Stacks.DerivedHom.BaseChange

universe u v uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- The comparison of a composite of derived exact functors with the derived composite, at the
class of a cochain complex. -/
private theorem derivedFunctorCompIso_hom_app_Q
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H)
    (X : CochainComplex C₁ ℤ) :
    (derivedFunctorCompIso F G H e).hom.app (DerivedCategory.Q.obj X) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app X) ≫
            H.mapDerivedCategoryFactors.inv.app X := by
  dsimp only [derivedFunctorCompIso]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- The inverse of `Stacks.DerivedHom.BaseChange.derivedFunctorCompIso` at the class of a cochain
complex. -/
private theorem derivedFunctorCompIso_inv_app_Q
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H)
    (X : CochainComplex C₁ ℤ) :
    (derivedFunctorCompIso F G H e).inv.app (DerivedCategory.Q.obj X) =
      H.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app X) ≫
          G.mapDerivedCategoryFactors.inv.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
            G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
  dsimp only [derivedFunctorCompIso]
  rw [Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- The component formula for `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, in the unfolded
spelling in which the two factors are visibly
`Stacks.DerivedHom.BaseChange.derivedFunctorCompIso`s. -/
private theorem scalarRestrictionIso_hom_app_Q_aux
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (X : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let upR := (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom
    let upA := (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom
    let U := ModuleCat.restrictScalars.{max uR uA uM} f
    let U' := ModuleCat.restrictScalars.{max uR uA uM} f'
    let RA := ModuleCat.restrictScalars.{max uR uA uM} upA
    let RR := ModuleCat.restrictScalars.{max uR uA uM} upR
    let H := ModuleCat.restrictScalars.{max uR uA uM} (upA.comp f)
    letI : U.IsRightAdjoint := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f).isRightAdjoint
    letI : U.IsLeftAdjoint := (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f).isLeftAdjoint
    letI : U'.IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : U'.IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : H.IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} (upA.comp f)).isRightAdjoint
    letI : H.IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} (upA.comp f)).isLeftAdjoint
    (derivedFunctorCompIso RA U H (ModuleCat.restrictScalarsComp f upA).symm ≪≫
        (derivedFunctorCompIso U' RR H
          (ModuleCat.restrictScalarsComp' upR f' (upA.comp f)
            (RingHom.ext fun _ => rfl)).symm).symm).hom.app (DerivedCategory.Q.obj X) =
      U.mapDerivedCategory.map (RA.mapDerivedCategoryFactors.hom.app X) ≫
        U.mapDerivedCategoryFactors.hom.app
            ((RA.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                  (ModuleCat.restrictScalarsComp f upA).symm (ComplexShape.up ℤ)).hom.app X) ≫
            DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso
                    (ModuleCat.restrictScalarsComp' upR f' (upA.comp f)
                      (RingHom.ext fun _ => rfl)).symm (ComplexShape.up ℤ)).inv.app X) ≫
              RR.mapDerivedCategoryFactors.inv.app
                  ((U'.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
                RR.mapDerivedCategory.map (U'.mapDerivedCategoryFactors.inv.app X) := by
  intro f' upR upA U U' RA RR H
  simp [derivedFunctorCompIso_hom_app_Q, derivedFunctorCompIso_inv_app_Q]

/-- The inverse component formula for `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, in the
unfolded spelling. -/
private theorem scalarRestrictionIso_inv_app_Q_aux
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (X : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let upR := (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom
    let upA := (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom
    let U := ModuleCat.restrictScalars.{max uR uA uM} f
    let U' := ModuleCat.restrictScalars.{max uR uA uM} f'
    let RA := ModuleCat.restrictScalars.{max uR uA uM} upA
    let RR := ModuleCat.restrictScalars.{max uR uA uM} upR
    let H := ModuleCat.restrictScalars.{max uR uA uM} (upA.comp f)
    letI : U.IsRightAdjoint := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f).isRightAdjoint
    letI : U.IsLeftAdjoint := (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f).isLeftAdjoint
    letI : U'.IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : U'.IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : H.IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} (upA.comp f)).isRightAdjoint
    letI : H.IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} (upA.comp f)).isLeftAdjoint
    (derivedFunctorCompIso RA U H (ModuleCat.restrictScalarsComp f upA).symm ≪≫
        (derivedFunctorCompIso U' RR H
          (ModuleCat.restrictScalarsComp' upR f' (upA.comp f)
            (RingHom.ext fun _ => rfl)).symm).symm).inv.app (DerivedCategory.Q.obj X) =
      RR.mapDerivedCategory.map (U'.mapDerivedCategoryFactors.hom.app X) ≫
        RR.mapDerivedCategoryFactors.hom.app
            ((U'.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                  (ModuleCat.restrictScalarsComp' upR f' (upA.comp f)
                    (RingHom.ext fun _ => rfl)).symm (ComplexShape.up ℤ)).hom.app X) ≫
            DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso
                    (ModuleCat.restrictScalarsComp f upA).symm
                      (ComplexShape.up ℤ)).inv.app X) ≫
              U.mapDerivedCategoryFactors.inv.app
                  ((RA.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
                U.mapDerivedCategory.map (RA.mapDerivedCategoryFactors.inv.app X) := by
  intro f' upR upA U U' RA RR H
  simp [derivedFunctorCompIso_hom_app_Q, derivedFunctorCompIso_inv_app_Q]

/-- The inverse of the scalar-lift equivalence
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` is derived restriction of
scalars along `ULift.ringEquiv.symm`; this is its factorization through `DerivedCategory.Q`. -/
public noncomputable def scalarEquivalenceInverseFactors (B : Type u) [CommRing B] :
    DerivedCategory.Q ⋙
        (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u,
          v} B).inverse ≅
      (ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (ModuleCat.restrictScalars.{max u v}
    (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapDerivedCategoryFactors

/-- **The component formula for `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`.**

At the class of a cochain complex `X` of modules over the lifted ring, the comparison is the
composite of: the scalar-lift factorization over `A`, pushed forward by derived restriction along
`f`; the factorization of derived restriction along `f`; the two evident comparisons of
restriction functors — along `upA ∘ f` as `restrict upA` then `restrict f`, and as `restrict f'`
then `restrict upR` — localized; and the scalar-lift factorization over `R`, inverted. -/
public theorem scalarRestrictionIso_hom_app_Q
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (X : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let upR := (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom
    let upA := (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom
    let U := ModuleCat.restrictScalars.{max uR uA uM} f
    let U' := ModuleCat.restrictScalars.{max uR uA uM} f'
    let RA := ModuleCat.restrictScalars.{max uR uA uM} upA
    (scalarRestrictionIso.{uR, uA, uM} f).hom.app (DerivedCategory.Q.obj X) =
      (U.mapDerivedCategory.map
          ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app X) ≫
        U.mapDerivedCategoryFactors.hom.app
            ((RA.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                  (ModuleCat.restrictScalarsComp f upA).symm (ComplexShape.up ℤ)).hom.app X) ≫
            DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso
                    (ModuleCat.restrictScalarsComp' upR f' (upA.comp f)
                      (RingHom.ext fun _ => rfl)).symm (ComplexShape.up ℤ)).inv.app X) ≫
              (scalarEquivalenceInverseFactors.{uR, max uR uA uM} R).inv.app
                  ((U'.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
                (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
                    max uR uA uM} R).inverse.map
                  (U'.mapDerivedCategoryFactors.inv.app X) :
        ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
              max uR uA uM} A).inverse ⋙ U.mapDerivedCategory).obj (DerivedCategory.Q.obj X) ⟶
          (U'.mapDerivedCategory ⋙
            (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
              max uR uA uM} R).inverse).obj (DerivedCategory.Q.obj X)) :=
  scalarRestrictionIso_hom_app_Q_aux.{uR, uA, uM} f X

/-- **The inverse component formula for `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`.**
The factors of `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q`, inverted and in the
opposite order. -/
public theorem scalarRestrictionIso_inv_app_Q
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (X : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let upR := (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom
    let upA := (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom
    let U := ModuleCat.restrictScalars.{max uR uA uM} f
    let U' := ModuleCat.restrictScalars.{max uR uA uM} f'
    let RA := ModuleCat.restrictScalars.{max uR uA uM} upA
    (scalarRestrictionIso.{uR, uA, uM} f).inv.app (DerivedCategory.Q.obj X) =
      ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
              max uR uA uM} R).inverse.map (U'.mapDerivedCategoryFactors.hom.app X) ≫
        (scalarEquivalenceInverseFactors.{uR, max uR uA uM} R).hom.app
            ((U'.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                  (ModuleCat.restrictScalarsComp' upR f' (upA.comp f)
                    (RingHom.ext fun _ => rfl)).symm (ComplexShape.up ℤ)).hom.app X) ≫
            DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso
                    (ModuleCat.restrictScalarsComp f upA).symm
                      (ComplexShape.up ℤ)).inv.app X) ≫
              U.mapDerivedCategoryFactors.inv.app
                  ((RA.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
                U.mapDerivedCategory.map
                  ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).inv.app X) :
        (U'.mapDerivedCategory ⋙
            (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
              max uR uA uM} R).inverse).obj (DerivedCategory.Q.obj X) ⟶
          ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
            max uR uA uM} A).inverse ⋙ U.mapDerivedCategory).obj (DerivedCategory.Q.obj X)) :=
  scalarRestrictionIso_inv_app_Q_aux.{uR, uA, uM} f X

end Stacks.DerivedHom.BaseChange
