module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.TargetShiftIso

/-!
# The degree-`n` cohomology of a Hom complex, read in degree zero at the shifted target

Let `K` and `L` be cochain complexes in a preadditive category. A degree-`n` cohomology class of
`Hom^•(K, L)` gives a morphism `K ⟶ L[n]` of the homotopy category in two ways: directly, by
Tag 0A5X in degree `n` (`CochainComplex.HomComplex.homComplexHomologyAddEquiv`), or by moving the
class to `H^0(Hom^•(K, L[n]))` along `CochainComplex.HomComplex.homComplexDegreeShift` and
applying Tag 0A5X in degree zero. The two agree.

## Main definitions

* `CochainComplex.HomComplex.homComplexDegreeShift`: the comparison
  `H^n(Hom^•(K, L)) ⟶ H^0(Hom^•(K, L[n]))`.

## Main results

* `CochainComplex.HomComplex.homComplexHomologyAddEquiv_degreeShift`: the degree-zero reading of
  `CochainComplex.HomComplex.homComplexDegreeShift` of a class, followed by the comparison
  `(L[n])[0] ≅ L[n]`, is the degree-`n` reading of that class.
* `CochainComplex.HomComplex.homComplexHomologyAddEquiv_degreeShift_Q`: the same with the source
  class presented as a degree-`n` homology class of the Hom complex in `D(Ab)`.
* `CochainComplex.HomComplex.derivedCategoryIsoShift_inv_app_Q_obj`: the comparison
  `H^n(Q D) ⟶ H^0(D[n])` of the derived category is the one of cochain complexes.

## Implementation notes

The shift sequence and the components of `Hom^•(K, L)[n]` in degree `0` are indexed by `0 + n`,
which is only propositionally `n`; `CochainComplex.HomComplex.cochain_XIsoOfEq_inv_v` removes the
resulting `HomologicalComplex.XIsoOfEq`. The terms involved typecheck only at default
transparency, so several proofs are chains of `congrArg` and `Eq.trans` rather than `rw`.

## References

* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### The transport along an equality of degrees -/

/-- The transport of a cochain along an equality of degrees does not change its homogeneous
components. -/
lemma cochain_XIsoOfEq_inv_v {K L : CochainComplex C ℤ} {m m' : ℤ} (h : m = m')
    (c : Cochain K L m') (p q : ℤ) (hpq : p + m = q) :
    (AddCommGrpCat.Hom.hom
          ((HomologicalComplex.XIsoOfEq (K.HomComplex L) h).inv) c).v p q hpq =
      c.v p q (by rw [← h]; exact hpq) := by
  subst h
  rfl

/-! ### The degree-zero target shift of a cocycle -/

/-- The degree-zero right shift of a `0`-cocycle is the cocycle itself, read through the
comparison `M[0] ≅ M`. -/
lemma homOf_rightShift_zero {K M : CochainComplex C ℤ} (z : Cocycle K M 0) :
    Cocycle.homOf (z.rightShift 0 0 (zero_add 0)) ≫
        ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app M).hom =
      Cocycle.homOf z := by
  ext p
  simp [Cocycle.homOf, Iso.app_hom,
    Cochain.rightShift_v _ 0 0 (zero_add 0) p p (add_zero p) p (add_zero p),
    CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq]

/-- On a cocycle, Tag 0A5X in degree zero at the shifted target computes Tag 0A5X in degree `n`:
the morphism of the homotopy category attached to the degree-zero class of the right
shift of a degree-`n` cocycle, followed by `(L[n])[0] ≅ L[n]`, is the morphism attached to the
degree-`n` class of the cocycle itself. -/
lemma toHom_rightShift {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    CohomologyClass.toHom (CohomologyClass.mk (z.rightShift n 0 (zero_add n))) ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app (L⟦n⟧)).hom =
      CohomologyClass.toHom (CohomologyClass.mk z) := by
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_apply, Cocycle.equivHomShift_symm_apply,
    ← CategoryTheory.Functor.map_comp, homOf_rightShift_zero]

/-! ### The comparison on homology -/

variable (K L : CochainComplex C ℤ) (n : ℤ)

/-- The comparison `H^n(Hom^•(K, L)) ⟶ H^0(Hom^•(K, L)[n]) ≅ H^0(Hom^•(K, L[n]))`, given by the
shift sequence of the homology functors followed by
`CochainComplex.HomComplex.homComplexTargetShiftIso`. -/
def homComplexDegreeShift :
    (K.HomComplex L).homology n ⟶ (K.HomComplex (L⟦n⟧)).homology 0 :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) 0).shiftIso
      n 0 n (add_zero n)).inv.app (K.HomComplex L) ≫
    HomologicalComplex.homologyMap (homComplexTargetShiftIso K L n).hom 0

/-- On a cochain, the degreewise effect of `CochainComplex.HomComplex.homComplexDegreeShift` is
`CochainComplex.HomComplex.Cochain.rightShift`, with no sign. -/
lemma homComplexTargetShiftIso_shiftShortComplex (c : Cochain K L n) :
    AddCommGrpCat.Hom.hom ((homComplexTargetShiftIso K L n).hom.f 0)
        (AddCommGrpCat.Hom.hom ((CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat.{v}
          n 0 n (add_zero n)).inv.app (K.HomComplex L)).τ₂ c) =
      c.rightShift n 0 (zero_add n) := by
  simp only [CochainComplex.shiftShortComplexFunctorIso_inv_app_τ₂]
  refine Cochain.ext _ _ fun p q hpq => ?_
  refine (homComplexTargetShiftIso_hom_f_apply_v K L n 0 _ p q hpq).trans ?_
  refine (congrArg (fun w => w ≫ (L.shiftFunctorObjXIso n q (q + n) rfl).inv)
    (cochain_XIsoOfEq_inv_v _ c p (q + n) (by omega))).trans ?_
  exact (Cochain.rightShift_v c n 0 (zero_add n) p q hpq (q + n) (by omega)).symm

/-- `CochainComplex.HomComplex.homologyAddEquiv` sends the class of a cycle to the cohomology class
of the corresponding cocycle. -/
private lemma homologyAddEquiv_homologyπ (m : ℤ) (w : (K.HomComplex L).cycles m) :
    homologyAddEquiv K L m ((K.HomComplex L).homologyπ m w) =
      CohomologyClass.mk ((leftHomologyData K L m).cyclesIso.hom w) :=
  ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom
      ((K.HomComplex L).sc m) (leftHomologyData K L m)) w

/-- `CochainComplex.HomComplex.homComplexDegreeShift` sends the class of a cocycle to the class of
its right shift. -/
lemma homologyAddEquiv_homComplexDegreeShift_homologyπ (w : (K.HomComplex L).cycles n) :
    homologyAddEquiv K (L⟦n⟧) 0
        (homComplexDegreeShift K L n ((K.HomComplex L).homologyπ n w)) =
      CohomologyClass.mk (((leftHomologyData K L n).cyclesIso.hom w).rightShift n 0
        (zero_add n)) := by
  set φ := (CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat.{v} n 0 n
    (add_zero n)).inv.app (K.HomComplex L) with hφ
  have e1 := CochainComplex.ShiftSequence.shiftIso_inv_app (C := AddCommGrpCat.{v})
    n 0 n (add_zero n) (K.HomComplex L)
  refine (congrArg (fun z => homologyAddEquiv K (L⟦n⟧) 0
      (HomologicalComplex.homologyMap (homComplexTargetShiftIso K L n).hom 0 z))
    (ConcreteCategory.congr_hom e1 ((K.HomComplex L).homologyπ n w))).trans ?_
  have h1 : (ShortComplex.homologyMap φ) (((K.HomComplex L).sc n).homologyπ w) =
      (((K.HomComplex L)⟦n⟧).homologyπ 0) (ShortComplex.cyclesMap φ w) :=
    ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) w
  refine (congrArg (fun z => homologyAddEquiv K (L⟦n⟧) 0
      (HomologicalComplex.homologyMap (homComplexTargetShiftIso K L n).hom 0 z)) h1).trans ?_
  have h2 : (HomologicalComplex.homologyMap (homComplexTargetShiftIso K L n).hom 0)
        ((((K.HomComplex L)⟦n⟧).homologyπ 0) (ShortComplex.cyclesMap φ w)) =
      ((K.HomComplex (L⟦n⟧)).homologyπ 0)
        ((HomologicalComplex.cyclesMap (homComplexTargetShiftIso K L n).hom 0)
          (ShortComplex.cyclesMap φ w)) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      (homComplexTargetShiftIso K L n).hom 0) _
  refine (congrArg (fun z => homologyAddEquiv K (L⟦n⟧) 0 z) h2).trans ?_
  refine (homologyAddEquiv_homologyπ K (L⟦n⟧) 0 _).trans ?_
  congr 1
  refine Cocycle.ext ?_
  have g1 := ConcreteCategory.congr_hom
    (leftHomologyData K (L⟦n⟧) 0).cyclesIso_hom_comp_i
    ((HomologicalComplex.cyclesMap (homComplexTargetShiftIso K L n).hom 0)
      (ShortComplex.cyclesMap φ w))
  have g2 := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (homComplexTargetShiftIso K L n).hom 0)
    (ShortComplex.cyclesMap φ w)
  have g3 := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) w
  have g4 := ConcreteCategory.congr_hom (leftHomologyData K L n).cyclesIso_hom_comp_i w
  refine g1.trans <| g2.trans ?_
  refine (congrArg (AddCommGrpCat.Hom.hom ((homComplexTargetShiftIso K L n).hom.f 0)) g3).trans ?_
  refine (congrArg (fun c => AddCommGrpCat.Hom.hom ((homComplexTargetShiftIso K L n).hom.f 0)
    (AddCommGrpCat.Hom.hom φ.τ₂ c)) g4.symm).trans ?_
  refine (homComplexTargetShiftIso_shiftShortComplex K L n _).trans ?_
  exact (Cocycle.rightShift_coe _ n 0 (zero_add n)).symm

/-- Tag 0A5X in degree zero at the shifted target computes Tag 0A5X in degree `n`: the
degree-zero identification of the cohomology of `Hom^•(K, L[n])` with the morphisms
`K ⟶ (L[n])[0]` of the homotopy category, applied to the comparison
`CochainComplex.HomComplex.homComplexDegreeShift` of a degree-`n` class and followed by
`(L[n])[0] ≅ L[n]`, is the degree-`n` identification of Tag 0A5X applied to that class. -/
lemma homComplexHomologyAddEquiv_degreeShift (ξ : (K.HomComplex L).homology n) :
    homComplexHomologyAddEquiv K (L⟦n⟧) 0 (homComplexDegreeShift K L n ξ) ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app (L⟦n⟧)).hom =
      homComplexHomologyAddEquiv K L n ξ := by
  obtain ⟨w, rfl⟩ : ∃ w, (K.HomComplex L).homologyπ n w = ξ :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance ξ
  rw [homComplexHomologyAddEquiv, homComplexHomologyAddEquiv, AddEquiv.trans_apply,
    AddEquiv.trans_apply, homologyAddEquiv_homologyπ,
    homologyAddEquiv_homComplexDegreeShift_homologyπ]
  exact toHom_rightShift _

/-! ### The comparison on the derived category -/

section DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The `isoShiftZero` of the shift sequence of the homology functor of the homotopy category is
the identity. -/
lemma homotopyCategoryIsoShiftZero_hom [CategoryWithHomology A] :
    ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).isoShiftZero ℤ).hom = 𝟙 _ := by
  apply ((Functor.whiskeringLeft _ _ _).obj
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))).map_injective
  ext D
  refine (Functor.ShiftSequence.induced.isoZero_hom_app_obj
    (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) 0) ℤ
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ))
      (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ)) D).trans ?_
  show (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) 0).hom.app D ≫
      𝟙 _ ≫ (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) 0).inv.app D = 𝟙 _
  rw [Category.id_comp, Iso.hom_inv_id_app]

/-- The `isoShiftZero` of the shift sequence of the homology functor of the derived category is
the identity. -/
lemma derivedCategoryIsoShiftZero_hom [HasDerivedCategory A] :
    ((DerivedCategory.homologyFunctor A 0).isoShiftZero ℤ).hom = 𝟙 _ := by
  apply ((Functor.whiskeringLeft _ _ _).obj (DerivedCategory.Qh (C := A))).map_injective
  ext X
  refine (Functor.ShiftSequence.induced.isoZero_hom_app_obj
    (DerivedCategory.homologyFunctorFactorsh A 0) ℤ (DerivedCategory.homologyFunctor A)
      (DerivedCategory.homologyFunctorFactorsh A) X).trans ?_
  rw [show ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).isoShiftZero ℤ).hom.app X =
      𝟙 _ from NatTrans.congr_app homotopyCategoryIsoShiftZero_hom X]
  show (DerivedCategory.homologyFunctorFactorsh A 0).hom.app X ≫
      𝟙 _ ≫ (DerivedCategory.homologyFunctorFactorsh A 0).inv.app X = 𝟙 _
  rw [Category.id_comp, Iso.hom_inv_id_app]

/-- If `a ≫ s = p ≫ t ≫ u` for isomorphisms `s`, `a`, `t`, `u`, then
`s⁻¹ ≫ a⁻¹ ≫ p = u⁻¹ ≫ t⁻¹`. -/
private lemma inv_comp_eq_of_comp_hom_eq {D : Type*} [Category D] {X₁ X₂ X₃ X₄ X₅ : D}
    (s : X₂ ≅ X₁) (a : X₃ ≅ X₂) (p : X₃ ⟶ X₄) (t : X₄ ≅ X₅) (u : X₅ ≅ X₁)
    (h : a.hom ≫ s.hom = p ≫ t.hom ≫ u.hom) :
    s.inv ≫ a.inv ≫ p = u.inv ≫ t.inv := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq, ← Category.assoc, ← Category.assoc, h]
  simp

/-- Postcomposing both sides of `x ≫ y ≫ z = w ≫ v` with `m`. -/
private lemma comp_eq_comp_right {D : Type*} [Category D] {X₁ X₂ X₃ X₄ X₅ X₆ : D}
    {x : X₁ ⟶ X₂} {y : X₂ ⟶ X₃} {z : X₃ ⟶ X₄} {w : X₁ ⟶ X₅} {v : X₅ ⟶ X₄} (m : X₄ ⟶ X₆)
    (h : x ≫ y ≫ z = w ≫ v) : x ≫ y ≫ z ≫ m = w ≫ v ≫ m := by
  simpa using congrArg (fun t => t ≫ m) h

/-- The comparison `H^n(Y) ⟶ H^0(Y[n])` of the derived category given by
`CategoryTheory.Functor.isoShift` agrees with the one given by
`CategoryTheory.Functor.shiftIso`. -/
lemma derivedCategoryIsoShift_inv_app [HasDerivedCategory A] (n : ℤ) (Y : DerivedCategory A) :
    ((DerivedCategory.homologyFunctor A 0).isoShift n).inv.app Y =
      ((DerivedCategory.homologyFunctor A 0).shiftIso n 0 n (add_zero n)).inv.app Y := by
  rw [Functor.isoShift]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Iso.symm_inv, NatTrans.congr_app derivedCategoryIsoShiftZero_hom]
  exact Category.comp_id _

/-- At the class of a complex, the shift isomorphism of the homology functors of the derived
category is the one of cochain complexes. -/
lemma shiftIso_hom_app_Q_obj [HasDerivedCategory A] (D : CochainComplex A ℤ) (m a a' : ℤ)
    (h : m + a = a') :
    (DerivedCategory.homologyFunctor A a).map ((DerivedCategory.Q.commShiftIso m).hom.app D) ≫
        ((DerivedCategory.homologyFunctor A 0).shiftIso m a a' h).hom.app
          (DerivedCategory.Q.obj D) =
      (DerivedCategory.homologyFunctorFactors A a).hom.app (D⟦m⟧) ≫
        ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso m a a' h).hom.app
            D ≫
          (DerivedCategory.homologyFunctorFactors A a').inv.app D := by
  have hid := DerivedCategory.shiftMap_homologyFunctor_map_Q (C := A) (𝟙 (D⟦m⟧)) a a' h
  simp only [Functor.shiftMap, ShiftedHom.map, DerivedCategory.Q.map_id, Category.id_comp] at hid
  refine hid.trans ?_
  congr 2
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- The comparison `H^n(Q D) ⟶ H^0(D[n])`: the degree-`n` homology of the class of a complex in
the derived category, carried into the degree-zero homology of the `n`-shift of the complex by the
shift sequence of the homology functors of the derived category and the commutation of the
localization functor with the translation, is carried there by the shift sequence of the homology
functors of cochain complexes. -/
lemma derivedCategoryIsoShift_inv_app_Q_obj [HasDerivedCategory A] (D : CochainComplex A ℤ)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor A 0).isoShift n).inv.app (DerivedCategory.Q.obj D) ≫
        (DerivedCategory.homologyFunctor A 0).map
            ((DerivedCategory.Q.commShiftIso n).inv.app D) ≫
          (DerivedCategory.homologyFunctorFactors A 0).hom.app (D⟦n⟧) =
      (DerivedCategory.homologyFunctorFactors A n).hom.app D ≫
        ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso n 0 n
          (add_zero n)).inv.app D := by
  rw [derivedCategoryIsoShift_inv_app]
  exact inv_comp_eq_of_comp_hom_eq
    (((DerivedCategory.homologyFunctor A 0).shiftIso n 0 n (add_zero n)).app
      (DerivedCategory.Q.obj D))
    ((DerivedCategory.homologyFunctor A 0).mapIso ((DerivedCategory.Q.commShiftIso n).app D))
    ((DerivedCategory.homologyFunctorFactors A 0).hom.app (D⟦n⟧))
    (((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso n 0 n
      (add_zero n)).app D)
    ((DerivedCategory.homologyFunctorFactors A n).app D).symm
    (shiftIso_hom_app_Q_obj D n 0 n (add_zero n))

end DerivedCategory

/-- The comparison `H^n(Hom^•(K, L)) ⟶ H^0(Hom^•(K, L[n]))`, read on the derived category: the
degree-`n` homology of the class of the Hom complex in `D(Ab)`, moved into degree zero by the
shift sequence of the homology functors of the derived category and then along the target shift of
the Hom complex, is `CochainComplex.HomComplex.homComplexDegreeShift` of the degree-`n` cohomology
of the Hom complex itself. -/
lemma homComplexDegreeShift_Q [HasDerivedCategory AddCommGrpCat.{v}]
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} n).obj
      (DerivedCategory.Q.obj (K.HomComplex L)) : Type v)) :
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} 0).app
          (K.HomComplex (L⟦n⟧))).hom
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).map
          ((DerivedCategory.Q.commShiftIso n).inv.app (K.HomComplex L) ≫
            DerivedCategory.Q.map (homComplexTargetShiftIso K L n).hom)
          (((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).isoShift n).inv.app
            (DerivedCategory.Q.obj (K.HomComplex L)) η)) =
      homComplexDegreeShift K L n
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n).app
          (K.HomComplex L)).hom η) := by
  have key : ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).isoShift n).inv.app
          (DerivedCategory.Q.obj (K.HomComplex L)) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).map
            ((DerivedCategory.Q.commShiftIso n).inv.app (K.HomComplex L) ≫
              DerivedCategory.Q.map (homComplexTargetShiftIso K L n).hom) ≫
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} 0).hom.app
            (K.HomComplex (L⟦n⟧)) =
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n).hom.app (K.HomComplex L) ≫
        homComplexDegreeShift K L n := by
    rw [CategoryTheory.Functor.map_comp, homComplexDegreeShift]
    have hnat : (DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).map
            (DerivedCategory.Q.map (homComplexTargetShiftIso K L n).hom) ≫
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} 0).hom.app
            (K.HomComplex (L⟦n⟧)) =
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} 0).hom.app
            ((K.HomComplex L)⟦n⟧) ≫
          HomologicalComplex.homologyMap (homComplexTargetShiftIso K L n).hom 0 :=
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} 0).hom.naturality
        (homComplexTargetShiftIso K L n).hom
    rw [Category.assoc, hnat]
    exact comp_eq_comp_right _ (derivedCategoryIsoShift_inv_app_Q_obj (K.HomComplex L) n)
  exact ConcreteCategory.congr_hom key η

/-- Tag 0A5X in degree zero at the shifted target computes Tag 0A5X in degree `n`, for a
degree-`n` homology class of the Hom complex in `D(Ab)` carried into degree zero at the shifted
target. -/
lemma homComplexHomologyAddEquiv_degreeShift_Q [HasDerivedCategory AddCommGrpCat.{v}]
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} n).obj
      (DerivedCategory.Q.obj (K.HomComplex L)) : Type v)) :
    CohomologyClass.homAddEquiv (homologyAddEquiv K (L⟦n⟧) 0
          (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} 0).app
              (K.HomComplex (L⟦n⟧))).hom
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).map
              ((DerivedCategory.Q.commShiftIso n).inv.app (K.HomComplex L) ≫
                DerivedCategory.Q.map (homComplexTargetShiftIso K L n).hom)
              (((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).isoShift n).inv.app
                (DerivedCategory.Q.obj (K.HomComplex L)) η)))) ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app (L⟦n⟧)).hom =
      homComplexHomologyAddEquiv K L n
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n).app
          (K.HomComplex L)).hom η) := by
  rw [homComplexDegreeShift_Q]
  exact homComplexHomologyAddEquiv_degreeShift K L n _

end CochainComplex.HomComplex

end
