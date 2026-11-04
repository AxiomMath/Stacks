module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.HomComplex.ShiftTensor
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedTensorFunctoriality
public import StacksFrontier.Homology.Tor.IteratedDerivedChangeOfRings
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Bounded
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso
import StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfectAnyModuleUniverse

/-!
# Algebraic upper shriek is a derived tensor functor

Let `φ : R → A` be a perfect ring homomorphism.  Then algebraic upper shriek is
derived tensor product over `R` with the single object `φ^!(R)` of `D(A)`:
`φ^!(K) = K ⊗_R^L φ^!(R)` for every `K` in `D(R)`, naturally in `K`.  So `φ^!` is determined by
its value on `R`.

## Main definitions

* `Dualizing.derivedTensorProductOver` — derived tensor product over `R` with a fixed object of
  `D(A)`, as a functor `D(R) ⥤ D(A)`.

## Main results

* `Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct` — the tensor
  formula, at an arbitrary polynomial presentation and an arbitrary module universe, with
  perfectness of `A` over the polynomial algebra as its only hypothesis.
* `Dualizing.PolynomialPresentation.tensorFormulaOfDerivedHomIso` — the same formula **with the
  isomorphism built**, as a function of an isomorphism of Tag 0BZE for the presentation's
  surjection and of the complex that isomorphism is taken at;
  `Dualizing.PolynomialPresentation.TensorFormula.classIso` identifies the class of the resulting
  factor in `D(A)` with `φ^!(R)`.

## Implementation notes

Upper shriek depends on the presentation and is well defined only up to isomorphism, that
independence being Tag 0BZJ; every statement below is therefore made at an arbitrary polynomial
presentation, which is the strongest reading and depends on no choice.

Writing `P` for the polynomial algebra of the presentation and `ψ : P → A` for its surjection,
`φ^!(K) = RHom_P(A, K ⊗_R^L P)[n]`.  Tag 0BZE turns `RHom_P(A, -)` into derived tensor product
over `P` with `RHom_P(A, P)`, the iterated change of rings of Tag 08YU cancels the intermediate
`- ⊗_R^L P`, and the remaining shift is moved into the tensor factor by the universal property of
the left derived functor, after which the factor is evaluated at `R` by the unitors of the tensor
product of complexes.  Perfectness of `φ` enters only through the hypothesis of Tag 0BZE, namely
that `A` is a perfect `P`-module, which is Tag 068Y; that reduction is
`Dualizing.PolynomialPresentation.isPerfectModule_poly_of_isPerfectRingMap`, and the second
statement below takes perfectness of `φ` in that form.

Tag 0BZE enters at the module universe `max v u` of these statements, independent of the ring
universe `u`, and that is the generality in which
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse` of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfectAnyModuleUniverse` states it: the
differential graded chapter (Tag 09JJ) proves the tag at module universe equal to the ring
universe, and that module renames the rings along `ULift.ringEquiv` to reach an independent one.
It assumes nothing beyond the perfectness `hp` that Tag 0BZE itself assumes, so the tensor formula
below assumes nothing beyond it either.

The identification is `Nonempty`-valued rather than a bundled isomorphism, and this is forced by
the shape in which one of its inputs is available, not by a choice made here.  The fixed derived
right factor of the tensor product is represented by a complex chosen through the object preimage
of the localization functor, and the comparison of two such representatives rests on
`CochainComplex.DerivedTensor.exists_derivedTensorNatTrans_isIso_of_quasiIso`, existential and
irreducibly so, since two representatives of one object of the derived category are related only
by a fraction.  An isomorphism inside a proposition cannot be extracted into a data-valued goal,
so the conclusion is a proposition too.

That is the *only* such input.  The cancellation of the intermediate `- ⊗_R^L P` is
`CochainComplex.DerivedTensor.IteratedChangeOfRings.doubleBaseChangeIso`, which builds Tag 08YU's
associativity comparison; the theorem
`CochainComplex.DerivedTensor.IteratedChangeOfRings.derivedTensorProduct_doubleBaseChange` states
the same isomorphism inside an existential, and pins it uniquely there.  So at the tensor factor
the proof itself produces — rather than at a prescribed representative of `φ^!(R)` — the tensor
formula is an isomorphism, which is
`Dualizing.PolynomialPresentation.tensorFormulaOfDerivedHomIso`.

## References

* [The Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU), the statement.
* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE), derived Hom from a
  perfect algebra as a tensor functor.
* [The Stacks Project, Tag 08YU](https://stacks.math.columbia.edu/tag/08YU), iterated derived
  change of rings.
* [The Stacks Project, Tag 068Y](https://stacks.math.columbia.edu/tag/068Y), perfectness through
  a polynomial presentation.
* [The Stacks Project, Tag 0BZI](https://stacks.math.columbia.edu/tag/0BZI) for `φ^!`.
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor
open scoped TensorProduct ChangeOfRings

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing

private noncomputable def trightCochainShiftIso
    (C : Type*) [Category* C] [Preadditive C] [MonoidalCategory C]
    [CategoryTheory.MonoidalPreadditive C] [Limits.HasZeroObject C]
    [Limits.HasColimits C] (N : CochainComplex C ℤ) (n : ℤ) :
    TrightCochain N ⋙ shiftFunctor (CochainComplex C ℤ) n ≅
      TrightCochain ((shiftFunctor (CochainComplex C ℤ) n).obj N) := by
  let T := (curriedTensor C).map₂CochainComplex
  letI : T.CommShift₂Int := inferInstance
  exact Iso.symm <| NatIso.ofComponents (fun K => ((T.obj K).commShiftIso n).app N) (by
    intro K L f
    let : NatTrans.CommShift (T.map f) ℤ := inferInstance
    simpa [T, TrightCochain] using (NatTrans.shift_app_comm (T.map f) n N).symm)

-- Comparing the two derived-functor models after postcomposing with shift is expensive
-- because Lean checks the right-Kan extension uniqueness data for the composite.
private noncomputable def derivedTensorDirectShiftIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (N N' : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ)
    (hN' : N' = (shiftFunctor (CochainComplex (ModuleCat.{max v u} A) ℤ) n).obj N) :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N).directTensor ⋙
        shiftFunctor (CochainComplex (ModuleCat.{max v u} A) ℤ) n ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N').directTensor := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N
  let T' := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N'
  let Sc := shiftFunctor (CochainComplex (ModuleCat.{max v u} A) ℤ) n
  letI : MonoidalCategoryStruct (ModuleCat.{max v u} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  letI : MonoidalCategory (ModuleCat.{max v u} A) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  let eShift : TrightCochain N ⋙ Sc ≅ TrightCochain N' := by
    rw [hN']
    exact trightCochainShiftIso (ModuleCat.{max v u} A) N n
  let eAssociator :=
    (Functor.associator (CochainComplex.extendScalarsLarge f) (TrightCochain N) Sc).symm
  let e₁ := Functor.isoWhiskerRight T.directTensorComparison Sc
  let e₂ := Functor.isoWhiskerLeft (CochainComplex.extendScalarsLarge f) eShift
  let e₃ := T'.directTensorComparison.symm
  exact (e₁ ≪≫ eAssociator) ≪≫ (e₂ ≪≫ e₃)

private noncomputable def derivedTensorPostcomposeShiftIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (N N' : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ)
    (hN' : N' = (shiftFunctor (CochainComplex (ModuleCat.{max v u} A) ℤ) n).obj N) :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N).F ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N').F := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N
  let T' := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N'
  let Q_R := DerivedCategory.Q (C := ModuleCat.{max v u} R)
  let Q_A := DerivedCategory.Q (C := ModuleCat.{max v u} A)
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)
  let Sd := shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n
  let Sc := shiftFunctor (CochainComplex (ModuleCat.{max v u} A) ℤ) n
  let eDirect : T.directTensor ⋙ Sc ≅ T'.directTensor :=
    derivedTensorDirectShiftIso f N N' n hN'
  let eQ : (T.directTensor ⋙ Q_A) ⋙ Sd ≅ (T.directTensor ⋙ Sc) ⋙ Q_A :=
    Functor.associator T.directTensor Q_A Sd ≪≫
      Functor.isoWhiskerLeft T.directTensor (Functor.commShiftIso Q_A n).symm ≪≫
      (Functor.associator T.directTensor Sc Q_A).symm
  let eAll : (T.directTensor ⋙ Q_A) ⋙ Sd ≅ T'.directTensor ⋙ Q_A :=
    eQ ≪≫ Functor.isoWhiskerRight eDirect Q_A
  let α₁ : Q_R ⋙ (T.F ⋙ Sd) ⟶ (T.directTensor ⋙ Q_A) ⋙ Sd :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight T.alphaF Sd
  let α : Q_R ⋙ (T.F ⋙ Sd) ⟶ T'.directTensor ⋙ Q_A := α₁ ≫ eAll.hom
  have hPost : (T.F ⋙ Sd).IsRightKanExtension α₁ := by
    rw [Functor.isRightKanExtension_postcompose₂_iff T.F T.alphaF Sd]
    exact T.isLeftDerivedF.isRightKanExtension
  have hKan : (T.F ⋙ Sd).IsRightKanExtension α :=
    (Functor.isRightKanExtension_iff_of_iso₂ α₁ α eAll (Iso.refl _) (by simp [α])).mp hPost
  letI : T'.F.IsLeftDerivedFunctor T'.alphaF W := T'.isLeftDerivedF
  letI : (T.F ⋙ Sd).IsLeftDerivedFunctor α W :=
    (Functor.isLeftDerivedFunctor_iff_isRightKanExtension (T.F ⋙ Sd) α W).2 hKan
  exact (Functor.leftDerivedNatIso T'.F (T.F ⋙ Sd) T'.alphaF α W (Iso.refl _)).symm

/-- Extension of scalars along the structure map of an algebra, as the tensor product
`A ⊗_R M`. -/
public noncomputable def extendScalarsTensorIsoUnit
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : ModuleCat.{max v u} R) :
    (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R A)).obj M ≅
      ModuleCat.of A (A ⊗[R] M) := by
  change (letI := (algebraMap R A).toAlgebra
    ModuleCat.of A (TensorProduct R A M)) ≅ _
  rw [toAlgebra_algebraMap]

/-- Extension of scalars carries the unit complex of `R` to the unit complex of `A`. -/
public noncomputable def extendScalarsComplexUnitIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    (CochainComplex.extendScalarsLarge f).obj
        (HomologicalComplex.tensorUnit (ModuleCat.{max v u} R) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.tensorUnit (ModuleCat.{max v u} A) (ComplexShape.up ℤ) := by
  let F := ModuleCat.extendScalars.{u, u, max v u} f
  letI : F.Additive := extendScalars_additive f
  letI : Algebra R A := f.toAlgebra
  let U_R := MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R)
  let U_A := MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} A)
  let eTensor : F.obj U_R ≅ ModuleCat.of A (A ⊗[R] ULift.{v, u} R) := by
    change (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R A)).obj U_R ≅ _
    exact extendScalarsTensorIsoUnit U_R
  let eModule : ModuleCat.of A (A ⊗[R] ULift.{v, u} R) ≅ U_A :=
    LinearEquiv.toModuleIso
      (((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
        (ULift.moduleEquiv : ULift.{v, u} R ≃ₗ[R] R)).trans
        (TensorProduct.AlgebraTensorModule.rid R A A)).trans
        (ULift.moduleEquiv : ULift.{v, u} A ≃ₗ[A] A).symm)
  exact (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app U_R ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).mapIso (eTensor ≪≫ eModule)

/-- Derived tensor product over `R` with a complex `N` of `A`-modules, evaluated at `R` in
degree zero, is `N`. -/
public noncomputable def derivedTensorUnitEvaluationIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (N : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f N).F.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))) ≅
      (DerivedCategory.Q (C := ModuleCat.{max v u} A)).obj N := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f N
  let U_R := HomologicalComplex.tensorUnit (ModuleCat.{max v u} R) (ComplexShape.up ℤ)
  let U_A := HomologicalComplex.tensorUnit (ModuleCat.{max v u} A) (ComplexShape.up ℤ)
  let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
    (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
  let Q_R := DerivedCategory.Q (C := ModuleCat.{max v u} R)
  let Q_A := DerivedCategory.Q (C := ModuleCat.{max v u} A)
  let hR₀ : R₀ ≅ Q_R.obj U_R := by
    change ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))) ≅ _
    exact (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} R) 0).app _
  have hU : CochainComplex.KFlat U_R := by
    intro M hM
    exact HomologicalComplex.Acyclic.of_iso (HomologicalComplex.rightUnitor M).symm hM
  have hα : IsIso (T.alphaF.app U_R) := T.isIso_alphaF U_R hU
  let eDirect := T.directTensorComparison.app U_R
  let eTensor : (TrightCochain N).obj U_A ≅ N := HomologicalComplex.leftUnitor N
  let e : T.directTensor.obj U_R ≅ N :=
    T.directTensorComparison.app U_R ≪≫
      (TrightCochain N).mapIso (extendScalarsComplexUnitIso f) ≪≫ HomologicalComplex.leftUnitor N
  exact asIso (T.F.map hR₀.hom) ≪≫ asIso (T.alphaF.app U_R) ≪≫ Q_A.mapIso e

private noncomputable def canonicalTensorUnitIsoMapDerivedCategory
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} S) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} S) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} f) :=
      extendScalars_preservesFiniteLimits_of_flat' f hf
    letI : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, max v u} f) :=
      inferInstance
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f
      (HomologicalComplex.tensorUnit (ModuleCat.{max v u} S) (ComplexShape.up ℤ))).F ≅
    (ModuleCat.extendScalars.{u, u, max v u} f).mapDerivedCategory := by
  letI : MonoidalCategoryStruct (ModuleCat.{max v u} S) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  letI : MonoidalCategory (ModuleCat.{max v u} S) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  let F := ModuleCat.extendScalars.{u, u, max v u} f
  let N := HomologicalComplex.tensorUnit (ModuleCat.{max v u} S) (ComplexShape.up ℤ)
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N
  let eTensor : CochainComplex.tensorRightLarge.{u, max v u} N ≅
      𝟭 (CochainComplex (ModuleCat.{max v u} S) ℤ) :=
    trightCochainTensorUnitIso (ModuleCat.{max v u} S)
  let eDirect : T.directTensor ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) := by
    simpa [T, N, F, CochainComplex.extendScalarsLarge] using
      (T.directTensorComparison ≪≫
        Functor.isoWhiskerLeft (CochainComplex.extendScalarsLarge f) eTensor ≪≫
        Functor.rightUnitor (CochainComplex.extendScalarsLarge f))
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)
  letI : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  letI : Limits.PreservesFiniteColimits F := inferInstance
  letI : F.Additive := inferInstance
  have hmap : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactors
  exact Functor.leftDerivedNatIso T.F F.mapDerivedCategory T.alphaF
    F.mapDerivedCategoryFactors.hom W (Functor.isoWhiskerRight eDirect DerivedCategory.Q)

/-- Two complexes with isomorphic classes in the derived category are both targets of
quasi-isomorphisms out of a common complex. -/
public lemma exists_common_source_for_iso
    {A : Type u} [CommRing A]
    (L N : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (e : (DerivedCategory.Qh (C := ModuleCat.{max v u} A)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj L) ≅
      (DerivedCategory.Qh (C := ModuleCat.{max v u} A)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj N)) :
    ∃ (K : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : K ⟶ L) (b : K ⟶ N),
      QuasiIso a ∧ QuasiIso b := by
  let Q := HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ)
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction
    (DerivedCategory.Qh (C := ModuleCat.{max v u} A)) W e.hom
  have : IsIso (φ.map DerivedCategory.Qh (Localization.inverts DerivedCategory.Qh W)) := by
    rw [← hφ]
    infer_instance
  have : IsIso (DerivedCategory.Qh.map φ.s) :=
    Localization.inverts DerivedCategory.Qh W φ.s φ.hs
  have : IsIso (DerivedCategory.Qh.map φ.f) := by
    rw [← φ.map_s_comp_map DerivedCategory.Qh (Localization.inverts DerivedCategory.Qh W)]
    infer_instance
  have hf : W φ.f := (DerivedCategory.isIso_Qh_map_iff φ.f).1 inferInstance
  obtain ⟨s, hs⟩ := Q.map_surjective φ.s
  obtain ⟨g, hg⟩ := Q.map_surjective φ.f
  refine ⟨φ.X'.as, s, g, ?_, ?_⟩
  · exact (HomologicalComplex.mem_quasiIso_iff s).2
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 (hs ▸ φ.hs))
  · exact (HomologicalComplex.mem_quasiIso_iff g).2
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 (hg ▸ hf))

/-- Derived tensor product over `R` with a complex of `A`-modules depends, up to isomorphism, only
on the class of that complex in the derived category. -/
public theorem derivedTensorRepresentative_congr
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (L N : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (e : (DerivedCategory.Qh (C := ModuleCat.{max v u} A)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj L) ≅
      (DerivedCategory.Qh (C := ModuleCat.{max v u} A)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj N)) :
    Nonempty ((CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f L).F ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f N).F) := by
  obtain ⟨K, a, b, ha, hb⟩ := exists_common_source_for_iso L N e
  let T₀ := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f K
  let TL := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f L
  let TN := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f N
  let : MonoidalCategoryStruct (ModuleCat.{max v u} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} A) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  obtain ⟨tL, -, htL⟩ :=
    CochainComplex.DerivedTensor.exists_derivedTensorNatTrans_isIso_of_quasiIso.{u, u, v}
      f a T₀.F TL.F T₀.directCounit TL.directCounit
  obtain ⟨tN, -, htN⟩ :=
    CochainComplex.DerivedTensor.exists_derivedTensorNatTrans_isIso_of_quasiIso.{u, u, v}
      f b T₀.F TN.F T₀.directCounit TN.directCounit
  have : IsIso tL := htL ha
  have : IsIso tN := htN hb
  exact ⟨(asIso tL).symm ≪≫ asIso tN⟩

private theorem derivedTensorProductOver_congr
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (L N : DerivedCategory (ModuleCat.{max v u} A)) (e : L ≅ N) :
    Nonempty ((CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f
        ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage L).as).F ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f
        ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage N).as).F) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)
  let Qh := DerivedCategory.Qh (C := ModuleCat.{max v u} A)
  let Lc := (Qh.objPreimage L).as
  let Nc := (Qh.objPreimage N).as
  let eL : Qh.obj (Q.obj Lc) ≅ L := Qh.objObjPreimageIso L
  let eN : Qh.obj (Q.obj Nc) ≅ N := Qh.objObjPreimageIso N
  exact derivedTensorRepresentative_congr f Lc Nc (eL ≪≫ e ≪≫ eN.symm)

/-- Derived tensor product over `R` with a fixed object of `D(A)`, valued in `D(A)`. -/
public noncomputable def derivedTensorProductOver
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (L : DerivedCategory (ModuleCat.{max v u} A)) :
    DerivedCategory (ModuleCat.{max v u} R) ⥤
      DerivedCategory (ModuleCat.{max v u} A) :=
  (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f
    ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage L).as).F

private noncomputable def derivedTensorProductOverUniverseIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (L : DerivedCategory (ModuleCat.{max v u} A)) :
    derivedTensorProductOver.{u, v} f L ≅ derivedTensorProductOver.{u, max v u} f L := by
  let Lc := ((DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage L).as
  change (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} f Lc).F ≅
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u} f Lc).F
  exact CochainComplex.DerivedTensor.canonicalDerivedTensorUniverseIso.{u, v} f Lc

private theorem derivedTensorRepresentativeIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (N : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    Nonempty ((CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f N).F ≅
      derivedTensorProductOver f ((DerivedCategory.Q (C := ModuleCat.{max v u} A)).obj N)) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)
  let Qh := DerivedCategory.Qh (C := ModuleCat.{max v u} A)
  let L := (DerivedCategory.Q (C := ModuleCat.{max v u} A)).obj N
  let Nc := (Qh.objPreimage L).as
  let eL : Qh.obj (Q.obj N) ≅ Qh.obj (Q.obj Nc) :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).app N ≪≫
      (Qh.objObjPreimageIso L).symm
  exact derivedTensorRepresentative_congr f N Nc eL


namespace PolynomialPresentation

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- **The conclusion of Tag 0BZE for the surjection of a polynomial presentation**, at an
arbitrary module universe and at the chain-level representative of `RHom_P(A, P)` chosen by
`objPreimage`.

This is `Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse`
read at that representative; the only step is that its class in `D(A)` is the value of
`RHom_P(A, -)` at the monoidal unit, which is
`CategoryTheory.Functor.objObjPreimageIso`.  The monoidal unit of
`ModuleCat.liftedModuleMonoidalStruct` is the free module of rank one on the lifted carrier, which
is the module that form of Tag 0BZE is stated at, so no further identification is needed. -/
public theorem nonempty_derivedHom_iso_canonicalDerivedTensor_presentation
    (p : PolynomialPresentation f)
    (hp : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} p.Poly) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} p.Poly) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    let P₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} p.Poly) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} p.Poly))
    let L := (DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage
      ((Dualizing.derivedHom.{u, v} p.toRingHom).obj P₀)
    Nonempty (Dualizing.derivedHom.{u, v} p.toRingHom ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u}
        p.toRingHom L.as).F) := by
  let : MonoidalCategoryStruct (ModuleCat.{max v u} p.Poly) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} p.Poly) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  let : Algebra p.Poly A := p.toRingHom.toAlgebra
  refine Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse
    p.toRingHom hp _ ⟨?_⟩
  exact (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).symm.app _ ≪≫
    DerivedCategory.Qh.objObjPreimageIso _

/-- **Stacks 0BZU.** Let `φ : R → A` be a ring homomorphism, let `p` be a
polynomial presentation of `φ` with polynomial algebra `P` and surjection `ψ : P → A`, and assume
`A` is a perfect `P`-module, which for a perfect `φ` is Tag 068Y.  Then the algebraic upper shriek
functor of `p` is derived tensor product over `R` with the single object `φ^!(R)` of `D(A)`:
`φ^!(K) = K ⊗_R^L φ^!(R)`, naturally in `K` in `D(R)`.

Perfectness of `A` over `P` is exactly the hypothesis of Tag 0BZE, and Tag 0BZE for `ψ` is the one
external input of the argument: it identifies `RHom_P(A, -)` with derived tensor product over `P`
with `RHom_P(A, P)`.  At the arbitrary module universe `max v u` of this statement that tag is
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse`.

The rest is the cancellation of the intermediate `- ⊗_R^L P` by the iterated change of rings of
Tag 08YU, the passage of the shift by `n` into the tensor factor through the universal property of
the left derived functor, and the evaluation of that factor at `R` by the unitors of the tensor
product of complexes. -/
@[stacks 0BZU "at an arbitrary polynomial presentation and an arbitrary module universe"]
public theorem upperShriekFunctor_iso_derivedTensorProduct
    (p : PolynomialPresentation f)
    (hp : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
    Nonempty (p.upperShriekFunctor.{u, v} ≅
      derivedTensorProductOver.{u, v} f (p.upperShriekFunctor.{u, v}.obj R₀)) := by
  classical
  let : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  let P := p.Poly
  let g : P →+* A := p.toRingHom
  let f₀ : R →+* P := MvPolynomial.C
  let n : ℤ := p.variableCount
  let pUpper := p.upperShriekFunctor.{u, v}
  let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
    (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
  let : MonoidalCategoryStruct (ModuleCat.{max v u} P) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  let : MonoidalCategory (ModuleCat.{max v u} P) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  let P₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj
    (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} P))
  let LP := (DerivedCategory.Qh (C := ModuleCat.{max v u} A)).objPreimage
    ((Dualizing.derivedHom.{u, v} g).obj P₀)
  have hcompose : g.comp f₀ = f := p.commutes
  obtain ⟨eHom⟩ := p.nonempty_derivedHom_iso_canonicalDerivedTensor_presentation.{u, v} hp
  let K := (shiftFunctor (CochainComplex (ModuleCat.{max v u} A) ℤ) n).obj LP.as
  let Tg :=
    CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u} g LP.as
  let TgShift :=
    CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u} g K
  let E := p.derivedExtension.{u, v}
  let Sd := shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n
  obtain ⟨C, eToAC⟩ : Σ' C : CochainComplex (ModuleCat.{max v u} A) ℤ, pUpper ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u}
        (g.comp f₀) C).F :=
    ⟨_, (Functor.isoWhiskerRight (Functor.isoWhiskerLeft E eHom) Sd ≪≫
        Functor.associator E Tg.F Sd ≪≫
        Functor.isoWhiskerLeft E
          (derivedTensorPostcomposeShiftIso.{u, max v u} g LP.as K n rfl)) ≪≫
      Functor.isoWhiskerRight
        (canonicalTensorUnitIsoMapDerivedCategory.{u, max v u} f₀
          (RingHom.flat_algebraMap_iff.mpr inferInstance)).symm TgShift.F ≪≫
      IteratedChangeOfRings.doubleBaseChangeIso.{u, u, u, v} f₀ g _ K⟩
  obtain ⟨eRepresentative⟩ := derivedTensorRepresentativeIso.{u, max v u} (g.comp f₀) C
  obtain ⟨eFactor⟩ := derivedTensorProductOver_congr.{u, max v u}
    (g.comp f₀) ((DerivedCategory.Q (C := ModuleCat.{max v u} A)).obj C) (pUpper.obj R₀)
    (eToAC.app R₀ ≪≫ derivedTensorUnitEvaluationIso.{u, max v u} (g.comp f₀) C).symm
  have eResultLarge : pUpper ≅
      derivedTensorProductOver.{u, max v u} (g.comp f₀) (pUpper.obj R₀) :=
    eToAC ≪≫ eRepresentative ≪≫ eFactor
  rw [hcompose] at eResultLarge
  exact ⟨eResultLarge ≪≫
    (derivedTensorProductOverUniverseIso.{u, v} f (pUpper.obj R₀)).symm⟩

/-- **Stacks 0BZU.** Let `φ : R → A` be a perfect ring homomorphism and let `p` be
a polynomial presentation of `φ`.  Then the algebraic upper shriek functor of `p` is derived
tensor product over `R` with the single object `φ^!(R)` of `D(A)`: `φ^!(K) = K ⊗_R^L φ^!(R)`,
naturally in `K` in `D(R)`.  A flat homomorphism of finite type is perfect, so the hypothesis is
not vacuous.

Perfectness is taken in the form of `RingHom.IsPerfectRingMap`, which is relative to a certified
model of the derived tensor product on `D(R)`; by Tag 068Y it gives perfectness of `A` as a module
over the polynomial algebra of `p`, which is the hypothesis of Tag 0BZE.  That is the only thing
`Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct` asks for, so this
is exactly that statement with its perfectness rewritten. -/
@[stacks 0BZU "for a perfect homomorphism of Noetherian rings, at an arbitrary polynomial \
presentation and an arbitrary module universe"]
public theorem upperShriekFunctor_iso_derivedTensorProduct_of_isPerfectRingMap
    (p : PolynomialPresentation f)
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
    (hf : letI : Algebra R A := f.toAlgebra
      RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived) :
    letI : MonoidalCategoryStruct (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
    letI : MonoidalCategory (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))
    Nonempty (p.upperShriekFunctor.{u, v} ≅
      derivedTensorProductOver.{u, v} f (p.upperShriekFunctor.{u, v}.obj R₀)) :=
  p.upperShriekFunctor_iso_derivedTensorProduct.{u, v}
    (by
      let : Algebra R A := f.toAlgebra
      exact RingHom.isPerfectModule_of_isPerfectRingMap derivedTensor comparison isLeftDerived
        hf p.variableCount (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes)
        p.surjective)

/-! ### The tensor formula with the isomorphism built

The two statements above conclude `Nonempty`, for the reason recorded in the module
documentation: the comparison of Tag 08YU was available only inside an existential, and the right
factor of `Dualizing.derivedTensorProductOver` is a representative chosen by `objPreimage`, which
only a fraction relates to the complex the proof produces.

Both obstructions go away at once if the tensor factor is the complex the proof produces rather
than a prescribed representative, and if Tag 08YU's comparison is taken as data —
`CochainComplex.DerivedTensor.IteratedChangeOfRings.doubleBaseChangeIso`. Nothing below extracts
a witness from an existential: given the conclusion of Tag 0BZE for the surjection of the
presentation *as an isomorphism*, the tensor formula is an isomorphism too, at a constructed
tensor factor.
-/

/-- **The tensor formula of Stacks 0BZU, as data.** A complex `factor` of `A`-modules together
with an isomorphism of the algebraic upper shriek functor of `p` with derived tensor product over
`R` with `factor`, at the canonical model of Tag 06Y6. The class of `factor` in `D(A)` is
`φ^!(R)`, which is `Dualizing.PolynomialPresentation.TensorFormula.classIso`, so the two fields
together say `φ^!(K) = K ⊗_R^L φ^!(R)` naturally in `K` — Stacks 0BZU, with the isomorphism given
rather than asserted to exist. -/
public structure TensorFormula (p : PolynomialPresentation f) where
  /-- The complex of `A`-modules the formula tensors with. Its class in `D(A)` is `φ^!(R)`. -/
  factor : CochainComplex (ModuleCat.{max v u} A) ℤ
  /-- The tensor formula itself, at the canonical model of Tag 06Y6. -/
  iso : p.upperShriekFunctor.{u, v} ≅
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u} f factor).F

/-- **The tensor factor of a `Dualizing.PolynomialPresentation.TensorFormula` is `φ^!(R)`.**
Evaluating the formula at `R` and using that the unit complex computes the derived tensor product
identifies the class of the factor in `D(A)` with the value of the algebraic upper shriek functor
at `R`. So such a formula is the tensor formula of Stacks 0BZU, and not merely some tensor
formula. -/
@[no_expose]
public def TensorFormula.classIso {p : PolynomialPresentation f} (T : TensorFormula.{u, v} p) :
    letI : MonoidalCategory (ModuleCat.{max v u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, max v u}
    p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (MonoidalCategoryStruct.tensorUnit (ModuleCat.{max v u} R))) ≅
      (DerivedCategory.Q (C := ModuleCat.{max v u} A)).obj T.factor :=
  T.iso.app _ ≪≫ derivedTensorUnitEvaluationIso.{u, max v u} f T.factor

/-- **Stacks 0BZU with the isomorphism built.** Let `φ : R → A` be a ring homomorphism,
let `p` be a polynomial presentation of `φ` with polynomial algebra `P` and surjection
`ψ : P → A`, and let `ω` be a complex of `A`-modules at which the conclusion of Tag 0BZE holds
for `ψ` *as an isomorphism*: `eBZE` identifies `RHom_P(A, -)` with the canonical derived
change-of-rings tensor product of Tag 06Y6 with `ω`. Then the algebraic upper shriek functor of
`p` *is* derived tensor product over `R` with a constructed complex whose class in `D(A)` is
`φ^!(R)`.

The factor is the complex of Tag 08YU: the direct change-of-rings tensor product along `ψ` of the
chosen K-flat resolution of `ω[n]` with the chosen K-flat resolution of the unit complex of `P`,
where `n` is the number of variables of `p`.

No existential witness is chosen along the way. The cancellation of the intermediate
`- ⊗_R^L P` is
`CochainComplex.DerivedTensor.IteratedChangeOfRings.doubleBaseChangeIso`, the passage of the
shift by `n` into the tensor factor is `Dualizing.derivedTensorPostcomposeShiftIso`, and the
evaluation of the unit factor is `Dualizing.canonicalTensorUnitIsoMapDerivedCategory`. This is
the chain of isomorphisms of
`Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct`, stopped before
the two steps that are propositions there: the replacement of the factor by the `objPreimage`
representative of `φ^!(R)`, and the comparison of the two models of derived tensor product that
replacement needs. -/
@[no_expose]
public def tensorFormulaOfDerivedHomIso
    (p : PolynomialPresentation f)
    (ω : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (eBZE : Dualizing.derivedHom.{u, v} p.toRingHom ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u}
        p.toRingHom ω).F) :
    TensorFormula.{u, v} p := by
  let P := p.Poly
  let f₀ : R →+* P := MvPolynomial.C
  have hcompose : p.toRingHom.comp f₀ = f := p.commutes
  have hflat : f₀.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  obtain ⟨C, e⟩ : Σ' C : CochainComplex (ModuleCat.{max v u} A) ℤ,
      p.upperShriekFunctor.{u, v} ≅
        (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u}
          (p.toRingHom.comp f₀) C).F := by
    let n : ℤ := p.variableCount
    let K := (shiftFunctor (CochainComplex (ModuleCat.{max v u} A) ℤ) n).obj ω
    let Tg := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u}
      p.toRingHom ω
    let TgShift := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, max v u}
      p.toRingHom K
    let E := p.derivedExtension.{u, v}
    exact ⟨_, (Functor.isoWhiskerRight (Functor.isoWhiskerLeft E eBZE)
            (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n) ≪≫
          Functor.associator E _
            (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n) ≪≫
          Functor.isoWhiskerLeft E
            (derivedTensorPostcomposeShiftIso.{u, max v u} p.toRingHom ω K n rfl)) ≪≫
      Functor.isoWhiskerRight
        (canonicalTensorUnitIsoMapDerivedCategory.{u, max v u} f₀ hflat).symm _ ≪≫
      CochainComplex.DerivedTensor.IteratedChangeOfRings.doubleBaseChangeIso.{u, u, u, v}
        f₀ p.toRingHom _ K⟩
  rw [hcompose] at e
  exact ⟨C, e⟩

/-- **Stacks 0BZU with the isomorphism built, from perfectness alone.** Let `φ : R → A` be a ring
homomorphism and `p` a polynomial presentation of `φ` whose polynomial algebra
makes `A` a perfect module. Then the algebraic upper shriek functor of `p` *is* derived tensor
product over `R` with a constructed complex whose class in `D(A)` is `φ^!(R)`.

This is `Dualizing.PolynomialPresentation.tensorFormulaOfDerivedHomIso` at the representative of
`RHom_P(A, P)` chosen by `objPreimage`, with the isomorphism of Tag 0BZE there taken from
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse`. That tag
is available as a proposition rather than as data, because passing between two representatives of
one object of `D(A)` goes through a fraction, so the isomorphism is chosen; everything after the
choice is a construction. -/
@[stacks 0BZU "at an arbitrary polynomial presentation and an arbitrary module universe, with the \
tensor formula built as an isomorphism at a constructed tensor factor whose class in D(A) is the \
value of upper shriek at R", no_expose]
public def tensorFormulaOfPerfect
    (p : PolynomialPresentation f)
    (hp : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A) :
    TensorFormula.{u, v} p := by
  classical
  letI : MonoidalCategoryStruct (ModuleCat.{max v u} p.Poly) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  letI : MonoidalCategory (ModuleCat.{max v u} p.Poly) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  exact p.tensorFormulaOfDerivedHomIso.{u, v} _
    (Classical.choice (p.nonempty_derivedHom_iso_canonicalDerivedTensor_presentation.{u, v} hp))

end PolynomialPresentation

end Dualizing

end
