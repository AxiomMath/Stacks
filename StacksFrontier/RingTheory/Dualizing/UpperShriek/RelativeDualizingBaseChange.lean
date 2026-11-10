module

public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChangeIsomorphism
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.TorIndependentBaseChange
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectAnyPresentation
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChangeIso

/-!
# Base change for the relative dualizing complex in the Noetherian case

Let `R → R'` be a homomorphism of Noetherian rings, let `φ : R → A` be of finite type and set
`A' = R' ⊗_R A`.  The relative dualizing complex of `φ` is `ω^•_{A/R} = φ^!(R)`, the value of
algebraic upper shriek at the base ring in degree zero.  This file proves that it commutes with
base change — there is an isomorphism `ω^•_{A/R} ⊗_A^L A' ≅ ω^•_{A'/R'}` in `D(A')` — in each of
three cases: `R → R'` flat, `R → A` flat, and `R → A` perfect with `A` and `R'` Tor independent
over `R`.

## Main definitions

* `Dualizing.PolynomialPresentation.ProjectionCompatibility` — the projection-formula compatibility
  read at the square of a polynomial presentation.

## Main results

* `Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq` — the general
  compatibility `Dualizing.KFlatAlgebraActionEq` implies it at every presentation.
* `Dualizing.relativeDualizingComplexBaseChange_of_flatBaseChange` — case (1).
* `Dualizing.relativeDualizingComplexBaseChange_of_flatAlgebra` — case (2).
* `Dualizing.relativeDualizingComplexBaseChange_of_isPerfect` — case (3).

## Implementation notes

Upper shriek is read at an arbitrary polynomial presentation `p` of `φ`, rather than at one chosen
by `Classical.choice`; `ω^•_{A'/R'}` is then read at the base-changed presentation
`Dualizing.PolynomialPresentation.baseChange`.  This is stronger than the statement for a chosen
presentation.  The derived tensor product `- ⊗_A^L A'` enters as an arbitrary left-derived model
of extension of scalars along `A → A'`; the base-changed algebra is written `R' ⊗[R] A`.

The module universe is the ring universe, the universe in which `ω^•_{A/R}` is an object of
`D(A)`.

## References

* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 0BZN](https://stacks.math.columbia.edu/tag/0BZN)
* [Stacks Project, Tag 0BZR](https://stacks.math.columbia.edu/tag/0BZR)
* [Stacks Project, Tag 0BZS](https://stacks.math.columbia.edu/tag/0BZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section PresentationUnit

attribute [local implicit_reducible] ModuleCat.ExtendScalars.obj' ModuleCat.extendScalars

end PresentationUnit

attribute [local implicit_reducible] extensionOfScalarsComplexGeneral

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- The compatibility of the two projection formulas — the hypothesis `hAct` of
`Dualizing.isIso_derivedHomBaseChange_app_of_flat` and of
`Dualizing.isIso_derivedHomBaseChange_of_isPerfect` — read at the square `P → A`, `P → P'` of a
polynomial presentation `P = R[x_1, …, x_n] ↠ A` and its base change `P' = R'[x_1, …, x_n]`.

The Tor independence of that square is quantified over, so the proposition depends on the
presentation and on `R'` only. -/
def PolynomialPresentation.ProjectionCompatibility
    (p : PolynomialPresentation (algebraMap R A)) (R' : Type u) [CommRing R'] [Algebra R R'] :
    Prop :=
  letI : Algebra (MvPolynomial (Fin p.variableCount) R) A := p.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R') := MvPolynomial.algebraMvPolynomial
  letI DP := derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap (MvPolynomial (Fin p.variableCount) R) (MvPolynomial (Fin p.variableCount) R'))
  letI DA := derivedExtensionScalarsGeneral.{u, u, u}
    (Algebra.TensorProduct.includeLeft :
      A →ₐ[MvPolynomial (Fin p.variableCount) R]
        TensorProduct (MvPolynomial (Fin p.variableCount) R) A
          (MvPolynomial (Fin p.variableCount) R')).toRingHom
  ∀ (hTorP : TorIndependent (MvPolynomial (Fin p.variableCount) R) A
      (MvPolynomial (Fin p.variableCount) R'))
    (X : CochainComplex (ModuleCat.{u} A) ℤ), CochainComplex.KFlat.{u, u} X →
    (algebraActionLeftCanonical.{u, u, u, 0} hTorP DP.functor DP.comparison DP.isLeftDerived
        DA.functor DA.comparison DA.isLeftDerived).app (DerivedCategory.Q.obj X) =
      (algebraActionRightCanonical.{u, u, u, 0} hTorP DP.functor DP.comparison DP.isLeftDerived
        DA.functor DA.comparison DA.isLeftDerived).app (DerivedCategory.Q.obj X)

/-- The general compatibility `Dualizing.KFlatAlgebraActionEq`, which quantifies over every
Tor-independent square of rings and every pair of models of the two derived extensions of scalars,
implies `Dualizing.PolynomialPresentation.ProjectionCompatibility` at every polynomial presentation
and every `R'`. -/
theorem PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq
    (hAct : KFlatAlgebraActionEq.{u}) (p : PolynomialPresentation (algebraMap R A)) :
    p.ProjectionCompatibility R' := by
  let : Algebra (MvPolynomial (Fin p.variableCount) R) A := p.toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R') := MvPolynomial.algebraMvPolynomial
  exact fun hTorP X hX => hAct hTorP _ _ _ _ _ _ X hX

/-- The base-change isomorphism `ω^•_{A/R} ⊗_A^L A' ≅ ω^•_{A'/R'}`, given invertibility of the
derived-Hom base-change morphism `Dualizing.derivedHomBaseChange` at the square of the
presentation, evaluated at `R ⊗_R^L P`. -/
private theorem relativeDualizingBaseChange_core
    (p : PolynomialPresentation (algebraMap R A))
    (hTor : TorIndependent R A R')
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (hδ : letI : Algebra (MvPolynomial (Fin p.variableCount) R) A := p.toRingHom.toAlgebra
      letI : Algebra (MvPolynomial (Fin p.variableCount) R)
          (MvPolynomial (Fin p.variableCount) R') := MvPolynomial.algebraMvPolynomial
      letI DP := derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap (MvPolynomial (Fin p.variableCount) R)
          (MvPolynomial (Fin p.variableCount) R'))
      letI DA := derivedExtensionScalarsGeneral.{u, u, u}
        (Algebra.TensorProduct.includeLeft :
          A →ₐ[MvPolynomial (Fin p.variableCount) R]
            TensorProduct (MvPolynomial (Fin p.variableCount) R) A
              (MvPolynomial (Fin p.variableCount) R')).toRingHom
      ∀ hTorP : TorIndependent (MvPolynomial (Fin p.variableCount) R) A
          (MvPolynomial (Fin p.variableCount) R'),
        IsIso ((derivedHomBaseChange.{u, u, u, 0} hTorP DP.functor DP.comparison DP.isLeftDerived
          DA.functor DA.comparison DA.isLeftDerived).app
            (p.derivedExtension.{u, 0}.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) :
    Nonempty (bcT.obj (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        (p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R'))) := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let p' := p.baseChange (R' := R')
  let : Algebra P A := p.toRingHom.toAlgebra
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P A := .of_algebraMap_eq' p.commutes.symm
  let : IsScalarTower R P P' := inferInstance
  let : IsScalarTower R R' P' := inferInstance
  let : Algebra.IsPushout R R' P P' := inferInstance
  have hmap : algebraMap P P' = MvPolynomial.map (algebraMap R R') :=
    MvPolynomial.algebraMap_def
  let α : P →ₐ[R] A := p.toAlgHom
  have hTorP : TorIndependent P A P' :=
    torIndependent_mvPolynomialBaseChange p.variableCount α hTor
  let A0 := TensorProduct P A P'
  let T := TensorProduct R R' A
  let fA0 := (Algebra.TensorProduct.includeLeft : A →ₐ[P] A0).toRingHom
  let f0 := (Algebra.TensorProduct.includeRight : P' →ₐ[P] A0).toRingHom
  let fT := (Algebra.TensorProduct.includeRight : A →ₐ[R] T).toRingHom
  let DP := derivedExtensionScalarsGeneral.{u, u, u} (algebraMap P P')
  let DA := derivedExtensionScalarsGeneral.{u, u, u} fA0
  let δ := derivedHomBaseChange.{u, u, u, 0} hTorP DP.functor DP.comparison DP.isLeftDerived
    DA.functor DA.comparison DA.isLeftDerived
  let e : A0 ≃+* T := pushoutEquiv p
  let EC := (ModuleCat.restrictScalars.{u} e.symm.toRingHom).mapDerivedCategory
  have heA : e.toRingHom.comp fA0 = fT := by
    let : Algebra P' A0 := Algebra.TensorProduct.rightAlgebra
    ext a
    change Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A
      ((Algebra.TensorProduct.commRight P P' A).symm (a ⊗ₜ[P] 1)) = 1 ⊗ₜ[R] a
    rw [Algebra.TensorProduct.commRight_symm_tmul,
      Algebra.IsPushout.cancelBaseChangeAlg_tmul]
  have heP : e.toRingHom.comp f0 = p'.toRingHom :=
    (baseChange_toRingHom_eq p rfl hmap).symm
  let eA : bcT ≅ DA.functor ⋙ EC :=
    derivedExtensionRingEquivRight fA0 e DA.functor DA.comparison
      DA.isLeftDerived heA bcT cmpT ldT
  let eH : derivedHom.{u, 0} p'.toRingHom ≅ derivedHom.{u, 0} f0 ⋙ EC :=
    heP ▸ derivedHomRingEquivRight f0 e
  let n : ℤ := p.variableCount
  let R0 := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let R0' := (DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')
  let E := PolynomialPresentation.derivedExtension.{u, 0} p
  let E' := PolynomialPresentation.derivedExtension.{u, 0} p'
  let H := derivedHom.{u, 0} p.toRingHom
  let H0 := derivedHom.{u, 0} f0
  let HT := derivedHom.{u, 0} p'.toRingHom
  have hiso : IsIso (δ.app (E.obj R0)) := hδ hTorP
  refine ⟨?_⟩
  change bcT.obj ((H.obj (E.obj R0))⟦n⟧) ≅ (HT.obj (E'.obj R0'))⟦n⟧
  calc bcT.obj ((H.obj (E.obj R0))⟦n⟧)
      ≅ EC.obj (DA.functor.obj ((H.obj (E.obj R0))⟦n⟧)) := eA.app _
    _ ≅ EC.obj ((DA.functor.obj (H.obj (E.obj R0)))⟦n⟧) :=
        EC.mapIso ((Functor.CommShift.commShiftIso DA.functor n).app _)
    _ ≅ (EC.obj (DA.functor.obj (H.obj (E.obj R0))))⟦n⟧ :=
        (Functor.CommShift.commShiftIso EC n).app _
    _ ≅ (HT.obj (E'.obj R0'))⟦n⟧ :=
        (shiftFunctor (DerivedCategory (ModuleCat.{u} T)) n).mapIso
          (EC.mapIso (@asIso _ _ _ _ (δ.app (E.obj R0)) hiso ≪≫
            H0.mapIso (DP.functor.mapIso p.derivedExtensionUnitIso ≪≫
              derivedExtensionScalarsRegularIso (algebraMap P P'))) ≪≫ (eH.app _).symm ≪≫
            HT.mapIso p'.derivedExtensionUnitIso.symm)

/-- Let `R` and `R'` be Noetherian rings, let `φ : R → A` be a perfect
homomorphism presented by `p`, and let `A` and `R'` be Tor independent over `R`.  Then the
relative dualizing complex commutes with base change to `R'`: there is an isomorphism
`ω^•_{A/R} ⊗_A^L A' ≅ ω^•_{A'/R'}` in `D(A')`, where `A' = R' ⊗_R A` and the derived tensor
product is read at the given left-derived model of extension of scalars.

Perfectness of `φ` is `RingHom.IsPerfectRingMap` at the given certified derived tensor product. -/
@[stacks 0BZV "case (3), R → A perfect and A, R' Tor independent"]
theorem relativeDualizingComplexBaseChange_of_isPerfect
    [IsNoetherianRing R] [IsNoetherianRing R']
    (p : PolynomialPresentation (algebraMap R A))
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hperf : RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived)
    (hTor : TorIndependent R A R')
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    Nonempty (bcT.obj (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        (p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R'))) := by
  refine relativeDualizingBaseChange_core p hTor bcT cmpT ldT ?_
  intro hTorP
  let : Algebra (MvPolynomial (Fin p.variableCount) R) A := p.toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin p.variableCount) R) (MvPolynomial (Fin p.variableCount) R') :=
    MvPolynomial.algebraMvPolynomial
  have hPerfModule : let : Module (MvPolynomial (Fin p.variableCount) R) A :=
        Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := MvPolynomial (Fin p.variableCount) R) A :=
    RingHom.isPerfectModule_of_isPerfectRingMap derivedTensor comparison isLeftDerived hperf
      p.variableCount (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes) p.surjective
  let DP := derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap (MvPolynomial (Fin p.variableCount) R) (MvPolynomial (Fin p.variableCount) R'))
  let DA := derivedExtensionScalarsGeneral.{u, u, u}
    (Algebra.TensorProduct.includeLeft :
      A →ₐ[MvPolynomial (Fin p.variableCount) R]
        TensorProduct (MvPolynomial (Fin p.variableCount) R) A
          (MvPolynomial (Fin p.variableCount) R')).toRingHom
  exact (NatTrans.isIso_iff_isIso_app _).mp (isIso_derivedHomBaseChange_of_isPerfect.{u, u, u, 0}
    hTorP DP.functor DP.comparison DP.isLeftDerived DA.functor DA.comparison DA.isLeftDerived
    hPerfModule) _

/-- Let `R → R'` be a flat homomorphism of Noetherian rings and let
`φ : R → A` be of finite type, presented by `p`.  Then the relative dualizing complex commutes
with base change to `R'`: there is an isomorphism `ω^•_{A/R} ⊗_A^L A' ≅ ω^•_{A'/R'}` in `D(A')`,
where `A' = R' ⊗_R A` and the derived tensor product is read at the given left-derived model of
extension of scalars. -/
@[stacks 0BZV "case (1), R → R' flat"]
theorem relativeDualizingComplexBaseChange_of_flatBaseChange
    [IsNoetherianRing R] [IsNoetherianRing R']
    (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R R').Flat)
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    Nonempty (bcT.obj (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        (p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R'))) := by
  let fT := (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom
  let R0 := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let D := derivedExtensionScalarsGeneral.{u, u, u} (algebraMap R R')
  have h₁ := flatDerivedExtension_isLeftDerivedFunctor fT (flat_includeRight hflat)
  have h₂ := flatDerivedExtension_isLeftDerivedFunctor (algebraMap R R') hflat
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  have h₃ : D.functor.IsLeftDerivedFunctor cmpD W := D.isLeftDerived
  let e₁ : bcT ≅ flatDerivedExtension fT (flat_includeRight hflat) :=
    Functor.leftDerivedUnique (LF := bcT) (LF' := flatDerivedExtension fT (flat_includeRight hflat))
      (α := cmpT) (α'₂ := flatDerivedExtensionComparison fT _)
      (W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
  let e₃ : flatDerivedExtension (algebraMap R R') hflat ≅ D.functor :=
    Functor.leftDerivedUnique (LF := flatDerivedExtension (algebraMap R R') hflat)
      (LF' := D.functor) (α := flatDerivedExtensionComparison _ hflat) (α'₂ := cmpD) (W := W)
  have hK : DerivedCategoryB.IsBoundedBelow R0 :=
    ⟨0, fun n hn => R0.isZero_of_isGE 0 n hn⟩
  have := p.isIso_upperShriekFlatBaseChange_app.{u, 0} hflat R0 hK
  exact ⟨e₁.app _ ≪≫ @asIso _ _ _ _ ((p.upperShriekFlatBaseChange.{u, 0} hflat).app R0) this ≪≫
    (p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.mapIso
      (e₃.app R0 ≪≫ derivedExtensionScalarsRegularIso (algebraMap R R'))⟩

/-- Let `R` and `R'` be Noetherian rings and let `φ : R → A` be flat
and of finite type, presented by `p`.  Then the relative dualizing complex commutes with base
change to `R'`: there is an isomorphism `ω^•_{A/R} ⊗_A^L A' ≅ ω^•_{A'/R'}` in `D(A')`, where
`A' = R' ⊗_R A` and the derived tensor product is read at the given left-derived model of
extension of scalars. -/
@[stacks 0BZV "case (2), R → A flat"]
theorem relativeDualizingComplexBaseChange_of_flatAlgebra
    [IsNoetherianRing R] [IsNoetherianRing R']
    (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R A).Flat)
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    Nonempty (bcT.obj (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        (p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R'))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  have hTor : TorIndependent R A R' := by
    rw [torIndependent_iff_isZero_tor]
    intro i hi
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact isZero_Tor_succ_of_flat (ModuleCat.of R A) (ModuleCat.of R R') k
  have hft : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  have hfp : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp hft
  let D := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R
  exact relativeDualizingComplexBaseChange_of_isPerfect p D.tensor D.comparison D.isLeftDerived
    ((RingHom.isPerfectRingMap_of_flat_of_finitePresentation R A).2 D.tensor D.comparison
      D.isLeftDerived) hTor bcT cmpT ldT

end Dualizing

end
