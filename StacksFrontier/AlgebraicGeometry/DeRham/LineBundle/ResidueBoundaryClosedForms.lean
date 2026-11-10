module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryEvaluation
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.SingleShiftBoundary
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.ComplexBoundaryCocycle

/-!
# Closed one-forms and the first Chern class

Let `D` be a line-bundle situation and `Ω^•` the relative de Rham complex. The degree-zero cycles
of the abelian sheaf complex underlying `Ω^•[1]` are the closed one-forms `Z = ker(d : Ω¹ ⟶ Ω²)`.
Logarithmic differentiation `d log : 𝒪_X^* ⟶ Ω¹` factors through `Z`, so the morphism of
complexes `d log : 𝒪_X^*[-1] ⟶ Ω^•` of [Stacks, Tag 0FLE] factors through the inclusion
`Z[-1] ⟶ Ω^•`. On cohomology this expresses the de Rham first Chern class through the first
cohomology of `Z`.

## Main definitions

* `Stacks.LineBundle.Situation.closedForms`: the sheaf `Z` of closed one-forms, as the degree-zero
  cycles of the abelian complex underlying `Ω^•[1]`.
* `Stacks.LineBundle.Situation.closedFormsInclusion`: the inclusion `Z[-1] ⟶ Ω^•`.
* `Stacks.LineBundle.Situation.logarithmicDifferentialClosed`: `d log : 𝒪_X^* ⟶ Z`.

## Main results

* `Stacks.LineBundle.Situation.logarithmicDifferentialComplexMapPlus_comp`: the factorization of
  `d log` through `Z[-1]`.

## References

* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- A morphism killing a differential, through a commutative square, with every object and
morphism a variable. -/
private theorem comp_comm_zero {C : Type*} [Category* C] [Preadditive C] {p q r s t : C}
    (a : p ⟶ q) (e₁ : q ⟶ r) (d' : r ⟶ s) (d : q ⟶ t) (e₂ : t ⟶ s) (hc : e₁ ≫ d' = d ≫ e₂)
    (h : a ≫ d = 0) : a ≫ e₁ ≫ d' = 0 := by
  rw [hc, ← Category.assoc, h, zero_comp]

/-- **`d log u` is a closed one-form**, read in the complex underlying the de Rham complex of
sheaves of `A`-modules. -/
theorem logarithmicDifferentialAbelian_comp_iso_d :
    logarithmicDifferentialAbelian B D ≫ (deRhamAbelianComplexPlusIso B D).hom.hom.f 1 ≫
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.obj
        (deRhamComplexPlus B D)).obj.d 1 2 = 0 :=
  comp_comm_zero _ _ _ _ _ ((deRhamAbelianComplexPlusIso B D).hom.hom.comm 1 2)
    (logarithmicDifferentialAbelian_comp_d B D)

end AlgebraicGeometry.SheafOfModules

namespace CochainComplex

variable {V : Type*} [Category* V] [Abelian V]

/-- **A morphism from an object in degree zero to a translate, translated back by one**, is the
morphism from that object placed in degree one with the same component. -/
theorem singleFunctors_shiftIso_inv_comp_shift_mkHomFromSingle (K : CochainComplex V ℤ)
    {Z : V} (i : Z ⟶ (K⟦(1 : ℤ)⟧).X 0)
    (hi : ∀ k, (ComplexShape.up ℤ).Rel 0 k → i ≫ (K⟦(1 : ℤ)⟧).d 0 k = 0)
    (hi' : ∀ k, (ComplexShape.up ℤ).Rel 1 k → (i : Z ⟶ K.X 1) ≫ K.d 1 k = 0) :
    ((CochainComplex.singleFunctors V).shiftIso (-1) 1 0 (by omega)).inv.app Z ≫
      (HomologicalComplex.mkHomFromSingle i hi)⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (CochainComplex V ℤ) (1 : ℤ) (-1) (by omega)).hom.app K =
      HomologicalComplex.mkHomFromSingle (K := K) (j := 1) i hi' := by
  refine HomologicalComplex.from_single_hom_ext ?_
  simp only [Functor.id_obj, Int.reduceNeg, Functor.comp_obj, HomologicalComplex.mkHomFromSingle,
    shiftFunctor_obj_X', HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom, Int.reduceAdd,
    HomologicalComplex.XIsoOfEq, eqToIso.inv, shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, HomologicalComplex.comp_f, shiftFunctor_map_f', add_neg_cancel,
    ↓reduceDIte, eqToHom_refl, Category.comp_id, shiftFunctorAdd'_inv_app_f', eqToIso_refl,
    Iso.refl_hom, shiftFunctorZero_hom_app_f]
  have e : ((singleFunctor V 1).obj Z).X 1 =
      ((CategoryTheory.shiftFunctor (CochainComplex V ℤ) (-1)).obj
        ((singleFunctor V 0).obj Z)).X 1 :=
    (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) 1 Z).trans (by
      change Z = ((HomologicalComplex.single V (ComplexShape.up ℤ) 0).obj Z).X (1 + -1)
      rw [show (1 : ℤ) + -1 = 0 by omega]
      exact (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) 0 Z).symm)
  rw [AlgebraicGeometry.SheafOfModules.singleFunctors_shiftIso_inv_app_f (-1) 1 0 (by omega) Z 1 e,
    eqToHom_trans_assoc]

end CochainComplex

namespace Stacks.LineBundle

attribute [local instance 5000] HasDerivedCategory.standard

variable (D : Situation.{u})

open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

/-- A morphism killing a differential kills its translate, with every object and morphism a
variable. -/
private theorem comp_map_shift_eq_zero {C D' : Type*} [Category* C] [Category* D']
    [Preadditive C] [Preadditive D'] (F : C ⥤ D') [F.Additive] {p : D'} {q r : C}
    (i : p ⟶ F.obj q) (g : q ⟶ r) (h : i ≫ F.map g = 0) :
    i ≫ F.map ((1 : ℤ).negOnePow • g) = 0 := by
  rw [Int.negOnePow_one, Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul,
    F.map_neg, Preadditive.comp_neg, h, neg_zero]

/-- A morphism killing the translate of a differential kills the differential, with every object
and morphism a variable. -/
private theorem comp_map_eq_zero_of_shift {C D' : Type*} [Category* C] [Category* D']
    [Preadditive C] [Preadditive D'] (F : C ⥤ D') [F.Additive] {p : D'} {q r : C}
    (i : p ⟶ F.obj q) (g : q ⟶ r) (h : i ≫ F.map ((1 : ℤ).negOnePow • g) = 0) :
    i ≫ F.map g = 0 := by
  simpa using comp_map_shift_eq_zero F i _ h

/-- The abelian complex underlying the de Rham complex, bounded below. -/
abbrev Situation.deRhamAbelianPlus : CochainComplex.Plus (AbelianSheaf D.baseSpace.carrier) :=
  (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus.obj D.deRhamPlus

/-- The abelian complex underlying the translate `Ω^•[1]` of the de Rham complex. -/
abbrev Situation.deRhamShiftAbelianPlus :
    CochainComplex.Plus (AbelianSheaf D.baseSpace.carrier) :=
  (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus.obj
    D.residuePlusSequence.X₁

/-- **The sheaf of closed one-forms**, as the degree-zero cycles of the abelian complex underlying
`Ω^•[1]`. -/
abbrev Situation.closedForms : AbelianSheaf D.baseSpace.carrier :=
  D.deRhamShiftAbelianPlus.obj.cycles 0

/-- The degree-zero term of `Ω^•[1]` is the degree-one term of `Ω^•`. -/
abbrev Situation.shiftXOne : D.deRhamShiftAbelianPlus.obj.X 0 ⟶ D.deRhamAbelianPlus.obj.X 1 :=
  𝟙 _

/-- A closed form is killed by the de Rham differential. -/
theorem Situation.closedForms_d :
    ∀ k, (ComplexShape.up ℤ).Rel 1 k →
      (D.deRhamShiftAbelianPlus.obj.iCycles 0 ≫ D.shiftXOne) ≫
        D.deRhamAbelianPlus.obj.d 1 k = 0 := by
  intro k hk
  obtain rfl : k = 2 := by simp at hk; omega
  have h := D.deRhamShiftAbelianPlus.obj.iCycles_d 0 1
  change D.deRhamShiftAbelianPlus.obj.iCycles 0 ≫
    (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).map
      ((1 : ℤ).negOnePow • D.deRhamPlus.obj.d 1 2) = 0 at h
  exact (Category.comp_id _).trans (comp_map_eq_zero_of_shift
    (SheafOfModules.toSheaf (structureSheafRing D.baseSpace))
    (D.deRhamShiftAbelianPlus.obj.iCycles 0 : _ ⟶ (SheafOfModules.toSheaf
      (structureSheafRing D.baseSpace)).obj (D.deRhamPlus.obj.X 1))
    (D.deRhamPlus.obj.d 1 2) h)

/-- **The inclusion `Z[-1] ⟶ Ω^•`** of the closed one-forms, placed in degree one. -/
def Situation.closedFormsInclusion :
    (CochainComplex.singleFunctor (AbelianSheaf D.baseSpace.carrier) 1).obj D.closedForms ⟶
      D.deRhamAbelianPlus.obj :=
  HomologicalComplex.mkHomFromSingle _ D.closedForms_d

/-- The sheaf of units `𝒪_X^*`, written additively, read as a sheaf on the space of
`(X, f^{-1}𝒪_S)`. -/
abbrev Situation.unitsSheafBase : AbelianSheaf D.baseSpace.carrier :=
  AlgebraicGeometry.SheafOfModules.unitsAbelianSheaf D.X.toRingedSpace

/-- `d log : 𝒪_X^* ⟶ Ω¹`, into the degree-zero term of the abelian complex underlying
`Ω^•[1]`. -/
abbrev Situation.logarithmicDifferentialBase :
    D.unitsSheafBase ⟶ D.deRhamAbelianPlus.obj.X 1 :=
  AlgebraicGeometry.SheafOfModules.logarithmicDifferentialAbelian (Scheme.Hom.deRhamAlgebras D.f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) ≫
    (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras D.f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras D.f))).hom.hom.f 1

/-- `d log u` is a closed one-form. -/
theorem Situation.logarithmicDifferentialBase_comp_d :
    D.logarithmicDifferentialBase ≫ D.deRhamAbelianPlus.obj.d 1 2 = 0 :=
  (Category.assoc _ _ _).trans
    (AlgebraicGeometry.SheafOfModules.logarithmicDifferentialAbelian_comp_iso_d
      (X := D.X.toRingedSpace) (Scheme.Hom.deRhamAlgebras D.f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))

/-- `d log u` is killed by the differential out of degree one. -/
theorem Situation.logarithmicDifferentialBase_d :
    ∀ k, (ComplexShape.up ℤ).Rel 1 k →
      D.logarithmicDifferentialBase ≫ D.deRhamAbelianPlus.obj.d 1 k = 0 := by
  intro k hk
  obtain rfl : k = 2 := by simp at hk; omega
  exact D.logarithmicDifferentialBase_comp_d

/-- **`d log : 𝒪_X^* ⟶ Z`**, logarithmic differentiation into the closed one-forms. -/
def Situation.logarithmicDifferentialClosed : D.unitsSheafBase ⟶ D.closedForms :=
  D.deRhamShiftAbelianPlus.obj.liftCycles D.logarithmicDifferentialBase 1 (by simp) (by
    change _ ≫ (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).map
      ((1 : ℤ).negOnePow • D.deRhamPlus.obj.d 1 2) = 0
    exact comp_map_shift_eq_zero (SheafOfModules.toSheaf (structureSheafRing D.baseSpace))
      D.logarithmicDifferentialBase (D.deRhamPlus.obj.d 1 2) D.logarithmicDifferentialBase_comp_d)

/-- `d log` into the closed forms, followed by the inclusion of the closed forms. -/
@[reassoc (attr := simp)]
theorem Situation.logarithmicDifferentialClosed_iCycles :
    D.logarithmicDifferentialClosed ≫ D.deRhamShiftAbelianPlus.obj.iCycles 0 =
      D.logarithmicDifferentialBase :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- `𝒪_X^*[-1]`, on the space of `(X, f^{-1}𝒪_S)`. -/
abbrev Situation.unitsComplexBase : CochainComplex.Plus (AbelianSheaf D.baseSpace.carrier) :=
  AlgebraicGeometry.SheafOfModules.singleOneComplexPlus D.baseSpace.carrier D.unitsSheafBase

/-- **`d log : 𝒪_X^*[-1] ⟶ Ω^•`**, into the abelian complex underlying the de Rham complex of
sheaves of `f^{-1}𝒪_S`-modules. -/
def Situation.logarithmicDifferentialComplexBase : D.unitsComplexBase ⟶ D.deRhamAbelianPlus :=
  ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle D.logarithmicDifferentialBase
    D.logarithmicDifferentialBase_d)

/-- The degree-one computation of `logarithmicDifferentialComplexBase_eq`, with every object and
morphism a variable. -/
private theorem single_paste {C : Type*} [Category* C] {p q r t w : C} (s : p ≅ q) (s' : r ≅ t)
    (c : q ⟶ t) (i : t ⟶ w) (b : q ⟶ w) (h : c ≫ i = b) :
    s.hom ≫ b = (s.hom ≫ c ≫ s'.inv) ≫ s'.hom ≫ i ≫ 𝟙 w := by
  simp [h]

/-- **`d log : 𝒪_X^*[-1] ⟶ Ω^•` factors through the closed one-forms**: it is `d log` into the
closed forms, placed in degree one, followed by the inclusion `Z[-1] ⟶ Ω^•`. -/
theorem Situation.logarithmicDifferentialComplexBase_eq :
    D.logarithmicDifferentialComplexBase =
      (ObjectProperty.homMk ((CochainComplex.singleFunctor _ 1).map
          D.logarithmicDifferentialClosed) :
        D.unitsComplexBase ⟶ (Stacks.DerivedIndexing.singlePlusFunctor _ 1).obj D.closedForms) ≫
      ObjectProperty.homMk D.closedFormsInclusion := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.from_single_hom_ext ?_)
  change (HomologicalComplex.mkHomFromSingle _ D.logarithmicDifferentialBase_d).f 1 =
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 1).map _).f 1 ≫
      (HomologicalComplex.mkHomFromSingle _ D.closedForms_d).f 1
  rw [HomologicalComplex.mkHomFromSingle_f D.logarithmicDifferentialBase
      D.logarithmicDifferentialBase_d,
    HomologicalComplex.mkHomFromSingle_f _ D.closedForms_d, HomologicalComplex.single_map_f_self]
  exact single_paste _ _ _ _ _ D.logarithmicDifferentialClosed_iCycles

end Stacks.LineBundle

end
