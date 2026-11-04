module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIsoLarge
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.TorIndependentBaseChange
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectAnyPresentation

/-!
# Upper shriek of a perfect homomorphism commutes with Tor-independent base change

Let `R → R'` be a ring homomorphism, let `φ : R → A` be a perfect ring map such that `A` and `R'`
are Tor independent over `R`, and let `φ' : R' → A' = R' ⊗_R A` be its base change.  Then
`φ^!(K) ⊗_A^L A' ≅ (φ')^!(K ⊗_R^L R')`, naturally in `K` in `D(R)`.

## Main results

* `Dualizing.PolynomialPresentation.upperShriekTorIndependentBaseChangeLarge` — the base-change
  map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')` at a presentation, for modules in any universe.
* `Dualizing.PolynomialPresentation.isIso_upperShriekTorIndependentBaseChangeLarge` — it is an
  isomorphism of functors when `φ` is perfect.
* `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_torIndependent` —
  **[stacks 0BZR]**, with `φ^!` and `(φ')^!` read at arbitrary polynomial presentations.

## Implementation notes

The construction is that of
`Dualizing.PolynomialPresentation.upperShriekTorIndependentBaseChange`, carried out with the rings
in one universe `u` and the modules in an arbitrary universe `max v u`, as in
`Dualizing.PolynomialPresentation.upperShriekFunctor`: the base-change morphism of [stacks 0E29]
at the square `P, A, P', A ⊗_P P'` of a presentation `P = R[x_1, …, x_n] ↠ A`, conjugated by the
identification `(K ⊗_R^L P) ⊗_P^L P' = (K ⊗_R^L R') ⊗_{R'}^L P'` of [stacks 08YU] and by the
transports along the ring isomorphism `A ⊗_P P' ≅ R' ⊗_R A` of `Dualizing.pushoutEquiv`.  The
proof of invertibility rebuilds the local definitions of the construction in the same order, so
the identification of the map with the conjugated morphism is `rfl`.

Perfectness of `φ` is `RingHom.IsPerfectRingMap`, relative to an arbitrary certified model of the
derived tensor product on `D(R)`.  By [stacks 068Y] it makes `A` a perfect module over the
polynomial algebra of every presentation of `φ`, which is the finiteness hypothesis of
[stacks 0BZP] at the square of the presentation.  The Noetherian hypotheses of the source are not
used.  `(φ')^!` is read at an arbitrary presentation of `φ'`, compared with the base-changed one
by [stacks 0BZJ], and the two derived tensor products at arbitrary left-derived models of
extension of scalars.

## References

* [Stacks Project, Tag 0BZR](https://stacks.math.columbia.edu/tag/0BZR)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open StacksDraft.DerivedRingEquivIso

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing

section Transport

/-- Derived Hom transported along a ring isomorphism of the target and then shifted, at the
module universe `max v u`; the transport commutes with the shift. -/
private def derivedHomRingEquivShiftIsoLarge
    {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C'] (eC : C' ≃+* C)
    (f : B →+* C) (n : ℤ) :
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eC)
    (derivedHom.{u, v} (eC.symm.toRingHom.comp f) ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{max v u} C')) n) ≅
      derivedHom.{u, v} f ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{max v u} C)) n ⋙ EC.functor := by
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eC)
  letI : EC.functor.CommShift ℤ := by
    change Functor.CommShift
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u}
        eC).functor.mapDerivedCategory) ℤ
    infer_instance
  have eId := mapDerivedCategoryIdIsoLarge.{u, v} (B := B)
  have h := derivedHomRingEquivIsoLarge.{u, v} (RingEquiv.refl B) eC f
  let h' : derivedHom.{u, v} (eC.symm.toRingHom.comp f) ≅
      derivedHom.{u, v} f ⋙ EC.functor := by
    exact (Functor.leftUnitor
        (derivedHom.{u, v} (eC.symm.toRingHom.comp f))).symm ≪≫
      Functor.isoWhiskerRight eId.symm
        (derivedHom.{u, v} (eC.symm.toRingHom.comp f)) ≪≫ h
  exact Functor.isoWhiskerRight h'
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} C')) n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedHom.{u, v} f)
      (Functor.CommShift.commShiftIso EC.functor n).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Derived extension of scalars along `e ∘ g`, for `e` a ring isomorphism of the target and any
ring map `g'` equal to `e ∘ g`, is derived extension along `g` followed by the equivalence induced
by `e`, at the module universe `max v u`. -/
private def derivedExtensionRingEquivRightLarge
    {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C']
    (g : B →+* C) (e : C ≃+* C')
    (F : DerivedCategory (ModuleCat.{max v u} B) ⥤ DerivedCategory (ModuleCat.{max v u} C))
    (cmpF : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, max v u} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldF : F.IsLeftDerivedFunctor cmpF
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ)))
    {g' : B →+* C'} (w : e.toRingHom.comp g = g')
    (G : DerivedCategory (ModuleCat.{max v u} B) ⥤ DerivedCategory (ModuleCat.{max v u} C'))
    (cmpG : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, max v u} g').mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldG : G.IsLeftDerivedFunctor cmpG
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))) :
    G ≅ F ⋙ (mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} e.symm)).functor := by
  subst w
  exact @derivedExtensionRingEquivIsoRightLarge.{u, v} B C C' _ _ _ e.symm g F cmpF ldF G cmpG ldG

end Transport

section Presentation

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- The comparison exhibiting the derived base change along the polynomial algebra of a
presentation as a left derived functor of extension of scalars, at the module universe
`max v u`. -/
private def presentationComparisonLarge (p : PolynomialPresentation f) :
    DerivedCategory.Q ⋙ p.derivedExtension.{u, v} ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
        (MvPolynomial.C : R →+* p.Poly)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ p.flat_C
  exact (ModuleCat.extendScalars.{u, u, max v u}
    (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategoryFactors.hom

/-- The derived base change of a presentation is its own left derived functor, at the module
universe `max v u`. -/
private theorem presentation_isLeftDerivedFunctorLarge (p : PolynomialPresentation f) :
    (p.derivedExtension.{u, v}).IsLeftDerivedFunctor (presentationComparisonLarge.{u, v} p)
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)) := by
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ p.flat_C
  exact Functor.isLeftDerivedFunctor_of_inverts _ _
    (ModuleCat.extendScalars.{u, u, max v u}
      (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategoryFactors

/-- Derived base change along the polynomial algebra of a presentation is left adjoint to
derived restriction of scalars along it, at the module universe `max v u`. -/
private def presentationAdjunctionLarge (p : PolynomialPresentation f) :
    p.derivedExtension.{u, v} ⊣
      (ModuleCat.restrictScalars.{max v u} (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategory :=
  letI := presentation_isLeftDerivedFunctorLarge.{u, v} p
  derivedExtensionScalarsAdjunction.{u, u, v} (MvPolynomial.C : R →+* p.Poly)
    p.derivedExtension.{u, v} (presentationComparisonLarge.{u, v} p)

end Presentation

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']

attribute [local implicit_reducible] extensionOfScalarsComplexGeneral
  extensionOfScalarsComplex

/-- **The base-change map of [stacks 0BZR], at every module universe.**  Let `φ : R → A` admit
the polynomial presentation `p` and let `A` and `R'` be Tor independent over `R`.  The base-change
map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')`, natural in `K` in `D(R)`, for
`φ' : R' → A' = R' ⊗_R A`; here `φ^!` is read at `p` and `(φ')^!` at the base-changed
presentation, the two derived tensor products at the given left-derived models of extension of
scalars, and the modules live in the universe `max v u`.

It is the base-change map for derived Hom of [stacks 0E29] at the square `P, A, P', A ⊗_P P'` of
the presentation, conjugated by the identification
`(K ⊗_R^L P) ⊗_P^L P' = (K ⊗_R^L R') ⊗_{R'}^L P'` of [stacks 08YU], obtained from uniqueness of
left adjoints, and by the transports along the ring isomorphism `A ⊗_P P' ≅ R' ⊗_R A` of
`Dualizing.pushoutEquiv`.  This is the construction of
`Dualizing.PolynomialPresentation.upperShriekTorIndependentBaseChange` at a module universe above
the rings. -/
@[no_expose]
def PolynomialPresentation.upperShriekTorIndependentBaseChangeLarge
    (p : PolynomialPresentation (algebraMap R A))
    (hTor : TorIndependent R A R')
    (bcR : DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{max v u} A) ⥤
      DerivedCategory (ModuleCat.{max v u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))) :
    p.upperShriekFunctor.{u, v} ⋙ bcT ⟶
      bcR ⋙ (p.baseChange (R' := R')).upperShriekFunctor.{u, v} := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let p' := p.baseChange (R' := R')
  let : Algebra P A := p.toRingHom.toAlgebra
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P A := by
    apply IsScalarTower.of_algebraMap_eq'
    change algebraMap R A = p.toRingHom.comp MvPolynomial.C
    exact p.commutes.symm
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
  let DP := derivedExtensionScalarsGeneral.{u, v, u} (algebraMap P P')
  let DA := derivedExtensionScalarsGeneral.{u, v, u} fA0
  let bcP := DP.functor
  let bcA := DA.functor
  let δ := derivedHomBaseChange.{u, u, u, v} hTorP bcP DP.comparison DP.isLeftDerived
    bcA DA.comparison DA.isLeftDerived
  let e : A0 ≃+* T := pushoutEquiv p
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} e.symm)
  letI : EC.functor.CommShift ℤ := by
    change Functor.CommShift
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u}
        e.symm).functor.mapDerivedCategory) ℤ
    infer_instance
  have heA : e.toRingHom.comp fA0 = fT := by
    let : Algebra P' A0 := Algebra.TensorProduct.rightAlgebra
    ext a
    change Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A
      ((Algebra.TensorProduct.commRight P P' A).symm (a ⊗ₜ[P] 1)) = 1 ⊗ₜ[R] a
    rw [Algebra.TensorProduct.commRight_symm_tmul,
      Algebra.IsPushout.cancelBaseChangeAlg_tmul]
  have heP : e.toRingHom.comp f0 = p'.toRingHom :=
    (baseChange_toRingHom_eq p rfl hmap).symm
  let eA : bcT ≅ bcA ⋙ EC.functor :=
    derivedExtensionRingEquivRightLarge.{u, v} fA0 e bcA DA.comparison DA.isLeftDerived heA
      bcT cmpT ldT
  let n : ℤ := p.variableCount
  let S0 := shiftFunctor (DerivedCategory (ModuleCat.{max v u} A0)) n
  let ST := shiftFunctor (DerivedCategory (ModuleCat.{max v u} T)) n
  let H := derivedHom.{u, v} p.toRingHom
  let H0 := derivedHom.{u, v} f0
  let HT : DerivedCategory (ModuleCat.{max v u} P') ⥤ DerivedCategory (ModuleCat.{max v u} T) :=
    derivedHom.{u, v} p'.toRingHom
  let eH : HT ⋙ ST ≅ H0 ⋙ S0 ⋙ EC.functor := by
    have h := derivedHomRingEquivShiftIsoLarge.{u, v} e.symm f0 n
    simpa only [RingEquiv.symm_symm, heP] using h
  let E := PolynomialPresentation.derivedExtension.{u, v} p
  let E' := PolynomialPresentation.derivedExtension.{u, v} p'
  let cP : R →+* P' := (MvPolynomial.C : R' →+* P').comp (algebraMap R R')
  have hsquare : cP = (algebraMap P P').comp (MvPolynomial.C : R →+* P) := by
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply, hmap, MvPolynomial.map_C]
  let eE : E ⋙ bcP ≅ bcR ⋙ E' := by
    have := DP.isLeftDerived
    have := ldR
    let adjE := presentationAdjunctionLarge.{u, v} p
    let adjP := derivedExtensionScalarsAdjunction.{u, u, v} (algebraMap P P') bcP DP.comparison
    let adjR := derivedExtensionScalarsAdjunction.{u, u, v} (algebraMap R R') bcR cmpR
    let adjE' := presentationAdjunctionLarge.{u, v} p'
    exact ((adjE.comp adjP).ofNatIsoRight
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, v}
          (MvPolynomial.C : R →+* P) (algebraMap P P') cP hsquare)).leftAdjointUniq
      ((adjR.comp adjE').ofNatIsoRight
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, v}
          (algebraMap R R') (MvPolynomial.C : R' →+* P') cP rfl))
  let eSource :
      p.upperShriekFunctor.{u, v} ⋙ bcT ≅
        E ⋙ (H ⋙ bcA) ⋙ (S0 ⋙ EC.functor) :=
    Functor.isoWhiskerLeft (E ⋙ H ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n) eA ≪≫
      Functor.isoWhiskerLeft E (Functor.isoWhiskerLeft H
        (Functor.isoWhiskerRight (Functor.CommShift.commShiftIso bcA n) EC.functor))
  let eTarget :
      E ⋙ (bcP ⋙ H0) ⋙ (S0 ⋙ EC.functor) ≅ bcR ⋙ p'.upperShriekFunctor.{u, v} :=
    Functor.isoWhiskerLeft (E ⋙ bcP) eH.symm ≪≫
      Functor.isoWhiskerRight eE (HT ⋙ ST)
  exact eSource.hom ≫
    Functor.whiskerLeft E (Functor.whiskerRight δ (S0 ⋙ EC.functor)) ≫ eTarget.hom

/-- **The base-change map of [stacks 0BZR] is invertible for a perfect ring map.**  Let
`φ : R → A` be perfect, presented by `p`, and let `A` and `R'` be Tor independent over `R`.  Then
the base-change map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')` of
`Dualizing.PolynomialPresentation.upperShriekTorIndependentBaseChangeLarge` is an isomorphism of
functors, at every module universe `max v u`.

The proof is the source's.  By [stacks 068Y] the polynomial algebra `P` of `p` makes `A` a
perfect module, and `A` and `P' = R'[x_1, …, x_n]` are Tor independent over `P`.  The map is the
base-change morphism of [stacks 0E29] at the square `P, A, P', A ⊗_P P'`, conjugated by
isomorphisms of functors and whiskered, and that morphism is invertible by [stacks 0BZP]. -/
theorem PolynomialPresentation.isIso_upperShriekTorIndependentBaseChangeLarge
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
    (bcR : DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{max v u} A) ⥤
      DerivedCategory (ModuleCat.{max v u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))) :
    IsIso (p.upperShriekTorIndependentBaseChangeLarge.{u, v} hTor bcR cmpR ldR bcT cmpT ldT) := by
  let : Algebra (MvPolynomial (Fin p.variableCount) R) A := p.toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin p.variableCount) R) (MvPolynomial (Fin p.variableCount) R') :=
    MvPolynomial.algebraMvPolynomial
  have hperfP : StacksDraft.Perfect.IsPerfectModule (R := MvPolynomial (Fin p.variableCount) R) A :=
    RingHom.isPerfectModule_of_isPerfectRingMap derivedTensor comparison isLeftDerived hperf
      p.variableCount p.toAlgHom p.surjective
  unfold PolynomialPresentation.upperShriekTorIndependentBaseChangeLarge
  dsimp only
  refine IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' ?_ (Iso.isIso_hom _))
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine @Functor.map_isIso _ _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _
    (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
      (isIso_derivedHomBaseChange_of_isPerfect.{u, u, u, v} _ _ _ _ _ _ _ hperfP) _))

/-- The base-changed presentation `Dualizing.PolynomialPresentation.baseChange`, read as a
presentation of the structure map `R' → R' ⊗_R A`; the two ring maps are equal. -/
private def PolynomialPresentation.baseChangeAlgebraMap'
    (p : PolynomialPresentation (algebraMap R A)) :
    PolynomialPresentation (algebraMap R' (TensorProduct R R' A)) where
  variableCount := (p.baseChange (R' := R')).variableCount
  toRingHom := (p.baseChange (R' := R')).toRingHom
  commutes := by
    rw [(p.baseChange (R' := R')).commutes]
    ext r
    simp
  surjective := (p.baseChange (R' := R')).surjective

/-- **Stacks 0BZR.**  Let `R → R'` be a ring homomorphism, let `φ : R → A` be a perfect ring map
such that `A` and `R'` are Tor independent over `R`, and let `φ' : R' → A' = R' ⊗_R A` be the
induced map.  Then `φ^!(K) ⊗_A^L A' ≅ (φ')^!(K ⊗_R^L R')`, naturally in `K` in `D(R)`.

Here `φ^!` is read at an arbitrary polynomial presentation `p` of `φ` and `(φ')^!` at an
arbitrary polynomial presentation `p'` of `φ'`, the two derived tensor products at arbitrary
left-derived models of extension of scalars, perfectness of `φ` relative to an arbitrary
certified model of the derived tensor product on `D(R)`, and the modules in an arbitrary universe
`max v u`.  The Noetherian hypotheses of the source are not needed.

The isomorphism is the base-change map
`Dualizing.PolynomialPresentation.upperShriekTorIndependentBaseChangeLarge` at `p` and its base
change, invertible by
`Dualizing.PolynomialPresentation.isIso_upperShriekTorIndependentBaseChangeLarge`, followed by the
comparison of [stacks 0BZJ] between the base-changed presentation and `p'`. -/
@[stacks 0BZR]
theorem PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_torIndependent
    (p : PolynomialPresentation (algebraMap R A))
    (p' : PolynomialPresentation (algebraMap R' (TensorProduct R R' A)))
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
    (bcR : DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{max v u} A) ⥤
      DerivedCategory (ModuleCat.{max v u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))) :
    Nonempty (p.upperShriekFunctor.{u, v} ⋙ bcT ≅ bcR ⋙ p'.upperShriekFunctor.{u, v}) := by
  have := p.isIso_upperShriekTorIndependentBaseChangeLarge.{u, v} derivedTensor comparison
    isLeftDerived hperf hTor bcR cmpR ldR bcT cmpT ldT
  obtain ⟨eJ⟩ := nonempty_upperShriekFunctor_iso.{u, v}
    (algebraMap R' (TensorProduct R R' A))
    (PolynomialPresentation.baseChangeAlgebraMap' (R' := R') p) p'
  exact ⟨asIso (p.upperShriekTorIndependentBaseChangeLarge.{u, v} hTor bcR cmpR ldR bcT cmpT
    ldT) ≪≫ Functor.isoWhiskerLeft bcR eJ⟩

end Dualizing

end
