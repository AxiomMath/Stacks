module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChangeUnconditional

/-!
# Flat base change for the algebraic upper shriek functor

Let `R → R'` be a flat homomorphism with `R` Noetherian, let `φ : R → A` be of finite type and
let `φ' : R' → A' = R' ⊗_R A` be its base change. For every polynomial presentation `p` of `φ`,
this file constructs the flat-base-change map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')`, natural in
`K` in `D(R)`, and proves that it is an isomorphism at every `K` in `D⁺(R)`.

## Main definitions

* `Dualizing.PolynomialPresentation.upperShriekFlatBaseChange`: the flat-base-change map.

## Main results

* `Dualizing.PolynomialPresentation.isIso_upperShriekFlatBaseChange_app`: the flat-base-change
  map is an isomorphism at every bounded below `K`.

## Implementation notes

The rings live in one universe `u` and the modules in an arbitrary universe `max v u`, as in
`Dualizing.PolynomialPresentation.upperShriekFunctor`. Only `R` is assumed Noetherian, and
everything is stated for an arbitrary presentation rather than one chosen by `Classical.choice`.

## References

* [Stacks Project, Tag 0BZN](https://stacks.math.columbia.edu/tag/0BZN)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
-/

@[expose] public section

open CategoryTheory
open StacksDraft.DerivedRingEquivIso

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- Derived Hom transported along a ring isomorphism of the target and then shifted, at the
module universe `max v u`; the transport commutes with the shift. -/
private noncomputable def derivedHomRingEquivIsoShiftLarge
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
      derivedHom.{u, v} f ⋙ EC.functor :=
    (Functor.leftUnitor
        (derivedHom.{u, v} (eC.symm.toRingHom.comp f))).symm ≪≫
      Functor.isoWhiskerRight eId.symm
        (derivedHom.{u, v} (eC.symm.toRingHom.comp f)) ≪≫ h
  exact Functor.isoWhiskerRight h'
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} C')) n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedHom.{u, v} f)
      (Functor.CommShift.commShiftIso EC.functor n).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Derived extension of scalars along a flat homomorphism commutes with the shift, at the module
universe `max v u`. -/
@[instance_reducible]
private noncomputable def flatDerivedExtensionLargeCommShift
    {B C : Type u} [CommRing B] [CommRing C]
    (f : B →+* C) (hf : f.Flat) :
    (flatDerivedExtensionLarge.{u, v} f hf).CommShift ℤ := by
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} f) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} f hf
  change (ModuleCat.extendScalars.{u, u, max v u} f).mapDerivedCategory.CommShift ℤ
  infer_instance

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- For a flat homomorphism `R → R'` and a polynomial
presentation `p` of `φ : R → A`, the flat-base-change map
`φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')`, natural in `K` in `D(R)`; here `φ^!` is read at `p`
and `(φ')^!` at the base-changed presentation of `φ' : R' → A' = R' ⊗_R A`. -/
@[no_expose]
noncomputable def PolynomialPresentation.upperShriekFlatBaseChange
    (p : PolynomialPresentation (algebraMap R A)) (hf : (algebraMap R R').Flat) :
    p.upperShriekFunctor.{u, v} ⋙
        flatDerivedExtensionLarge.{u, v}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom (flat_includeRight hf) ⟶
      flatDerivedExtensionLarge.{u, v} (algebraMap R R') hf ⋙
        (p.baseChange (R' := R')).upperShriekFunctor.{u, v} := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let p' := p.baseChange (R' := R')
  let : Algebra P A := p.toRingHom.toAlgebra
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' p.commutes.symm
  let : IsScalarTower R P P' := inferInstance
  let : IsScalarTower R R' P' := inferInstance
  let : Algebra.IsPushout R R' P P' := inferInstance
  have hmap : algebraMap P P' = MvPolynomial.map (algebraMap R R') :=
    MvPolynomial.algebraMap_def
  have hflatP : (algebraMap P P').Flat :=
    mvPolynomial_map_flat_of_flat (σ := Fin p.variableCount) hf
  let : Module.Flat P P' := RingHom.flat_algebraMap_iff.mp hflatP
  let fA0 := (Algebra.TensorProduct.includeLeft :
    A →ₐ[P] TensorProduct P A P').toRingHom
  have hflatA0 : fA0.Flat :=
    RingHom.Flat.isStableUnderBaseChange.tensorProduct A hflatP
  let bcP := flatDerivedExtensionLarge.{u, v} (algebraMap P P') hflatP
  let cmpP := flatDerivedExtensionLargeFactors.{u, v} (algebraMap P P') hflatP
  let ldP := flatDerivedExtensionLarge_isLeftDerived.{u, v} (algebraMap P P') hflatP
  let bcA := flatDerivedExtensionLarge.{u, v} fA0 hflatA0
  let cmpA := flatDerivedExtensionLargeFactors.{u, v} fA0 hflatA0
  let ldA := flatDerivedExtensionLarge_isLeftDerived.{u, v} fA0 hflatA0
  let hTor : RingTheory.TorIndependence.TorIndependent P A P' :=
    torIndependent_of_flat_right (R := P) (A := A) (B := P')
  let δ := derivedHomBaseChange.{u, u, u, v} hTor bcP cmpP ldP bcA cmpA ldA
  let A0 := TensorProduct P A P'
  let T := TensorProduct R R' A
  let e : A0 ≃+* T := pushoutEquiv p
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} e.symm)
  let f0 := (Algebra.TensorProduct.includeRight : P' →ₐ[P] A0).toRingHom
  let fT := (Algebra.TensorProduct.includeRight : A →ₐ[R] T).toRingHom
  have heA : e.toRingHom.comp fA0 = fT := by
    let : Algebra P' A0 := Algebra.TensorProduct.rightAlgebra
    ext a
    change Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A
      ((Algebra.TensorProduct.commRight P P' A).symm (a ⊗ₜ[P] 1)) = 1 ⊗ₜ[R] a
    rw [Algebra.TensorProduct.commRight_symm_tmul,
      Algebra.IsPushout.cancelBaseChangeAlg_tmul]
  have heP : e.toRingHom.comp f0 = p'.toRingHom :=
    (baseChange_toRingHom_eq p rfl hmap).symm
  let bcT := flatDerivedExtensionLarge.{u, v} fT (flat_includeRight hf)
  have heFlat : e.toRingHom.Flat := RingHom.Flat.of_bijective e.bijective
  let eA : bcT ≅ bcA ⋙ EC.functor := by
    have h := @derivedExtensionRingEquivIsoRightLarge.{u, v} _ _ _ _ _ _ e.symm fA0 bcA cmpA
      ldA
      (flatDerivedExtensionLarge.{u, v} (e.toRingHom.comp fA0) (hflatA0.comp heFlat))
      (flatDerivedExtensionLargeFactors.{u, v} (e.toRingHom.comp fA0) (hflatA0.comp heFlat))
      (flatDerivedExtensionLarge_isLeftDerived.{u, v} (e.toRingHom.comp fA0)
        (hflatA0.comp heFlat))
    simpa only [heA] using h
  let n : ℤ := p.variableCount
  let S0 := shiftFunctor (DerivedCategory (ModuleCat.{max v u} A0)) n
  let ST := shiftFunctor (DerivedCategory (ModuleCat.{max v u} T)) n
  let H := derivedHom.{u, v} p.toRingHom
  let H0 := derivedHom.{u, v} f0
  let HT : DerivedCategory (ModuleCat.{max v u} P') ⥤ DerivedCategory (ModuleCat.{max v u} T) :=
    derivedHom.{u, v} p'.toRingHom
  let eH : HT ⋙ ST ≅ H0 ⋙ S0 ⋙ EC.functor := by
    have h := derivedHomRingEquivIsoShiftLarge e.symm f0 n
    simpa only [RingEquiv.symm_symm, heP] using h
  have hC : (MvPolynomial.C : R →+* P).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hC' : (MvPolynomial.C : R' →+* P').Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  let E := PolynomialPresentation.derivedExtension.{u, v} p
  let E' := PolynomialPresentation.derivedExtension.{u, v} p'
  let bcR := flatDerivedExtensionLarge.{u, v} (algebraMap R R') hf
  have hsquare : (algebraMap P P').comp (MvPolynomial.C : R →+* P) =
      (MvPolynomial.C : R' →+* P').comp (algebraMap R R') := by
    ext r
    rw [RingHom.comp_apply, hmap, MvPolynomial.map_C]
    rfl
  let eE : E ⋙ bcP ≅ bcR ⋙ E' := by
    let e₁ := flatDerivedExtensionLargeComp.{u, v} (MvPolynomial.C : R →+* P)
      (algebraMap P P') hC hflatP
    let e₂ := flatDerivedExtensionLargeComp.{u, v} (algebraMap R R')
      (MvPolynomial.C : R' →+* P') hf hC'
    have e₂' : flatDerivedExtensionLarge.{u, v}
        ((MvPolynomial.C : R' →+* P').comp (algebraMap R R')) (hf.comp hC') ≅
        bcR ⋙ E' := by
      change _ ≅ bcR ⋙ flatDerivedExtensionLarge.{u, v} (MvPolynomial.C : R' →+* P') hC'
      exact e₂.symm
    exact e₁ ≪≫ (by simpa only [hsquare] using e₂')
  let : bcA.CommShift ℤ := flatDerivedExtensionLargeCommShift fA0 hflatA0
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

/-- A natural transformation of the form `a ≫ whiskerLeft E (whiskerRight δ S) ≫ b`, with `a`, `b`
isomorphisms, is an isomorphism at `K` as soon as `δ` is one at `E K`. -/
private theorem isIso_app_comp_whiskerLeft_whiskerRight_comp
    {C D D' D'' : Type*} [Category C] [Category D] [Category D'] [Category D'']
    {X Y : C ⥤ D''} (E : C ⥤ D) {F G : D ⥤ D'} (δ : F ⟶ G) (S : D' ⥤ D'')
    (a : X ≅ E ⋙ F ⋙ S) (b : E ⋙ G ⋙ S ≅ Y) (K : C) (h : IsIso (δ.app (E.obj K))) :
    IsIso ((a.hom ≫ Functor.whiskerLeft E (Functor.whiskerRight δ S) ≫ b.hom).app K) := by
  have : IsIso ((Functor.whiskerLeft E (Functor.whiskerRight δ S)).app K) :=
    inferInstanceAs (IsIso (S.map (δ.app (E.obj K))))
  simp only [NatTrans.comp_app]
  infer_instance

/-- Let `R` be Noetherian, let `R → R'` be flat, let `φ : R → A` be of finite type, presented by
`p`, and let `φ' : R' → A' = R' ⊗_R A` be its base change. The flat-base-change map
`φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')` of
`Dualizing.PolynomialPresentation.upperShriekFlatBaseChange`, a natural transformation of functors
`D(R) ⥤ D(A')`, is an isomorphism at every `K` in `D⁺(R)`; here `φ^!` is read at `p` and
`(φ')^!` at its base change. -/
@[stacks 0BZN]
theorem PolynomialPresentation.isIso_upperShriekFlatBaseChange_app [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hf : (algebraMap R R').Flat)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : DerivedCategoryB.IsBoundedBelow K) :
    IsIso ((p.upperShriekFlatBaseChange.{u, v} (R' := R') hf).app K) := by
  unfold PolynomialPresentation.upperShriekFlatBaseChange
  refine isIso_app_comp_whiskerLeft_whiskerRight_comp _ _ _ _ _ _ ?_
  let P := MvPolynomial (Fin p.variableCount) R
  let : Algebra P A := p.toRingHom.toAlgebra
  let : Algebra P (MvPolynomial (Fin p.variableCount) R') := MvPolynomial.algebraMvPolynomial
  obtain ⟨b, hb⟩ := p.derivedExtension_isBoundedBelow.{u, v} hK
  have hGE : (p.derivedExtension.{u, v}.obj K).IsGE b := (DerivedCategory.isGE_iff _ b).2 hb
  have hFin : Module.Finite P A := p.finite_toRingHom
  have hPC : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := P) A :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (R := P) ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
        (ModuleCat.of P P)) 0 A).2.2).2 hFin
  exact isIso_derivedHomBaseChange_app_of_flat_flatModelsLarge.{u, v} _ _ _
    (isPseudoCoherent_singleULiftAlgebra.{u, u, v} hPC) _ b hGE

end Dualizing

end
