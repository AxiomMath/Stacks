module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Shift.Quotient
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The translations of `Comp(A)` and `K(A)` attached to a family of differential graded shifts

Two of the thirteen fields of axiom (B), in either its strict form `DGCategory.ShiftAxiomB` or
its isomorphism-valued form `DGCategory.ShiftAxiomBIso`, are translations
`HasShift A.Comp ℤ` and `HasShift A.K ℤ` of the two ordinary categories attached to a
differential graded category, pinned by two further fields to a given family of differential
graded shift functors. This file produces both for `CochainComplex.dgCategory B`, the
differential graded category of complexes of Tag 09L9 and the `C` of Tag 09LK, out of Mathlib's
shift on `CochainComplex B ℤ`.

Both translations are obtained from `CategoryTheory.HasShift.induced`, which transports a shift
along a functor whose precomposition operation is fully faithful, and whose shift functors are by
definition the given ones (`CategoryTheory.shiftFunctor_of_induced`).

## Main definitions

* `DGCategory.kShiftOfCompShift`: for an arbitrary differential graded category, a translation of
  `Comp(A)` realized by a family of differential graded functors induces a translation of `K(A)`
  realized by the same family, along `DGCategory.compToK`.
* `CochainComplex.dgCompShift` and `CochainComplex.dgCategoryKShift`: the translations of the
  category of complexes and of the homotopy category of `CochainComplex.dgCategory B`, realized
  by `CochainComplex.dgShiftFunctor`.

## Main results

* `DGCategory.whiskeringLeft_compToK_full` and `DGCategory.whiskeringLeft_compToK_faithful`:
  precomposition with `DGCategory.compToK` is fully faithful.
* `CochainComplex.cochainToComplexFunctor_map_shift`: the differential graded shift of the closed
  degree-zero cochain of a map of complexes is the closed degree-zero cochain of the shifted map.
* `CochainComplex.cochainToComplexShiftEq`: the differential graded shift and Mathlib's shift
  are equal as functors through the comparison.
* `CochainComplex.dgCompShift_shiftFunctor` and `CochainComplex.dgCategoryKShift_shiftFunctor`:
  the two translations are the differential graded shift functors.

## Implementation notes

`DGCategory.Comp` and `DGCategory.K` are both definitionally the type of objects of the
differential graded category, and `DGCategory.compToK` is the identity on objects;
`DGCategory.kToCompObj` reads an object of `K(A)` as an object of `Comp(A)`.

## References

* [Stacks Project, Tag 09L7](https://stacks.math.columbia.edu/tag/09L7), the two categories;
  [Tag 09L8](https://stacks.math.columbia.edu/tag/09L8), the functors they induce;
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded category of
  complexes; [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B).
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- An object of the homotopy category read as an object of the category of complexes: the two
categories have the same objects, namely those of the differential graded category. -/
def kToCompObj (x : A.K) : A.Comp := x

/-- `DGCategory.compToK` sends `DGCategory.kToCompObj x` to `x`. -/
@[simp] theorem compToK_obj_kToCompObj (x : A.K) :
    (compToK A).obj (kToCompObj x) = x := rfl

/-- Precomposition with `DGCategory.compToK` is faithful. -/
instance whiskeringLeft_compToK_faithful (D : Type*) [Category D] :
    ((Functor.whiskeringLeft A.Comp A.K D).obj (compToK A)).Faithful where
  map_injective h := NatTrans.ext (funext fun x => NatTrans.congr_app h (kToCompObj x))

/-- Precomposition with `DGCategory.compToK` is full. -/
instance whiskeringLeft_compToK_full (D : Type*) [Category D] :
    ((Functor.whiskeringLeft A.Comp A.K D).obj (compToK A)).Full where
  map_surjective {_ _} α :=
    ⟨{ app := fun x => α.app (kToCompObj x)
       naturality x y f :=
         Quotient.inductionOn f fun c => α.naturality (X := kToCompObj x) (Y := kToCompObj y) c },
     by apply NatTrans.ext; funext _; rfl⟩

/-- The translation of `K(A)` induced along `DGCategory.compToK` by a translation of `Comp(A)`
whose shift functors are those of a family of differential graded functors; its shift functors
are those of the same family. -/
@[instance_reducible]
noncomputable def kShiftOfCompShift (Sh : ℤ → DGFunctor A A) [HasShift A.Comp ℤ]
    (h : ∀ n : ℤ, CategoryTheory.shiftFunctor A.Comp n = (Sh n).onComp) :
    HasShift A.K ℤ :=
  HasShift.induced (compToK A) ℤ (fun n => (Sh n).onK)
    (fun n => eqToIso (by rw [h n]; exact (dgFunctor_induces_functors (Sh n)).2.2.2.2.symm))

/-- The shift functors of `DGCategory.kShiftOfCompShift Sh h` are those induced by `Sh`. -/
theorem kShiftOfCompShift_shiftFunctor (Sh : ℤ → DGFunctor A A) [HasShift A.Comp ℤ]
    (h : ∀ n : ℤ, CategoryTheory.shiftFunctor A.Comp n = (Sh n).onComp) (n : ℤ) :
    letI := kShiftOfCompShift Sh h
    CategoryTheory.shiftFunctor A.K n = (Sh n).onK := rfl

/-- `DGCategory.compToK` commutes with the translations of `Comp(A)` and of
`DGCategory.kShiftOfCompShift`, with comparison isomorphisms the `eqToIso` of the equalities of
functors inducing the translation of `K(A)`. -/
@[instance_reducible]
noncomputable def compToKCommShift (Sh : ℤ → DGFunctor A A) [HasShift A.Comp ℤ]
    (h : ∀ n : ℤ, CategoryTheory.shiftFunctor A.Comp n = (Sh n).onComp) :
    letI := kShiftOfCompShift Sh h
    (compToK A).CommShift ℤ :=
  Functor.CommShift.ofInduced (compToK A) ℤ (fun n => (Sh n).onK)
    (fun n => eqToIso (by rw [h n]; exact (dgFunctor_induces_functors (Sh n)).2.2.2.2.symm))

end DGCategory

namespace CochainComplex

open CochainComplex.HomComplex

universe v u

variable (B : Type u) [Category.{v} B] [Preadditive B]

/-- `CochainComplex.cochainToComplexFunctor` is full. -/
instance cochainToComplexFunctor_full : (cochainToComplexFunctor B).Full :=
  ⟨fun {_ _} f => ⟨Cocycle.homOf f, Cocycle.ofHom_homOf_eq_self f⟩⟩

/-- `CochainComplex.cochainToComplexFunctor` is faithful. -/
instance cochainToComplexFunctor_faithful : (cochainToComplexFunctor B).Faithful :=
  ⟨fun {_ _ f g} h => by
    rw [← Cocycle.homOf_ofHom_eq_self f, ← Cocycle.homOf_ofHom_eq_self g]
    exact congrArg Cocycle.homOf h⟩

/-- `CochainComplex.cochainToComplexFunctor` is essentially surjective. -/
instance cochainToComplexFunctor_essSurj : (cochainToComplexFunctor B).EssSurj :=
  ⟨fun X => ⟨X, ⟨Iso.refl X⟩⟩⟩

/-- `CochainComplex.cochainToComplexFunctor` is an equivalence. -/
instance cochainToComplexFunctor_isEquivalence : (cochainToComplexFunctor B).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The differential graded shift of the cochain of a map of complexes is the cochain of the
shifted map. -/
theorem cochainToComplexFunctor_map_shift (n : ℤ) {X Y : CochainComplex B ℤ} (f : X ⟶ Y) :
    (dgShiftFunctor B n).map (Cochain.ofHom f) =
      Cochain.ofHom ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) n).map f) := by
  show (n * 0).negOnePow • (Cochain.ofHom f).shift n = _
  rw [mul_zero, Int.negOnePow_zero, one_smul]
  ext p
  rw [(Cochain.ofHom f).shift_v' n p p (add_zero p)]
  simp

/-- The differential graded shift on the category of complexes of `CochainComplex.dgCategory B`
agrees with Mathlib's shift on `CochainComplex B ℤ` through
`CochainComplex.cochainToComplexFunctor`. -/
theorem cochainToComplexShiftEq (n : ℤ) :
    cochainToComplexFunctor B ⋙ (dgShiftFunctor B n).onComp =
      CategoryTheory.shiftFunctor (CochainComplex B ℤ) n ⋙ cochainToComplexFunctor B :=
  CategoryTheory.Functor.hext (fun _ => rfl)
    (fun _ _ f => heq_of_eq (Subtype.ext (cochainToComplexFunctor_map_shift B n f)))

/-- The translation of the category of complexes of `CochainComplex.dgCategory B` whose shift
functors are the differential graded shift functors. -/
@[sga "4½ Etat_0 1.2.1"]
noncomputable instance dgCompShift : HasShift (dgCategory B).Comp ℤ :=
  HasShift.induced (cochainToComplexFunctor B) ℤ (fun n => (dgShiftFunctor B n).onComp)
    (fun n => eqToIso (cochainToComplexShiftEq B n))

/-- The translation of the category of complexes is the differential graded shift functor. -/
theorem dgCompShift_shiftFunctor (n : ℤ) :
    CategoryTheory.shiftFunctor (dgCategory B).Comp n = (dgShiftFunctor B n).onComp := rfl

/-- The translation of the homotopy category of `CochainComplex.dgCategory B` whose shift
functors are the differential graded shift functors. -/
noncomputable instance dgCategoryKShift : HasShift (dgCategory B).K ℤ :=
  DGCategory.kShiftOfCompShift (dgShiftFunctor B) (dgCompShift_shiftFunctor B)

/-- The translation of the homotopy category is the differential graded shift functor. -/
theorem dgCategoryKShift_shiftFunctor (n : ℤ) :
    CategoryTheory.shiftFunctor (dgCategory B).K n = (dgShiftFunctor B n).onK := rfl

/-! ### The comparison of the homotopy categories commutes with the translations -/

/-- `CochainComplex.cochainToComplexFunctor` commutes with the translations. -/
noncomputable instance cochainToComplexFunctor_commShift :
    (cochainToComplexFunctor B).CommShift ℤ :=
  Functor.CommShift.ofInduced (cochainToComplexFunctor B) ℤ
    (fun n => (dgShiftFunctor B n).onComp) (fun n => eqToIso (cochainToComplexShiftEq B n))

/-- `DGCategory.compToK` commutes with the translations, for the differential graded category of
complexes. -/
noncomputable instance compToK_commShift :
    (DGCategory.compToK (dgCategory B)).CommShift ℤ :=
  DGCategory.compToKCommShift (dgShiftFunctor B) (dgCompShift_shiftFunctor B)

/-- The comparison functor of the homotopy categories commutes with the translations. -/
noncomputable instance homotopyCategoryComparisonFunctor_commShift :
    (homotopyCategoryComparisonFunctor B).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift
    (cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B))
    (homotopic B (.up ℤ)) ℤ _

/-- The functor of the comparison equivalence commutes with the translations. -/
noncomputable instance homotopyCategoryEquivalence_functor_commShift :
    (homotopyCategoryEquivalence B).functor.CommShift ℤ :=
  inferInstanceAs ((homotopyCategoryComparisonFunctor B).CommShift ℤ)

/-- The quasi-inverse of the comparison equivalence commutes with the translations. -/
noncomputable instance homotopyCategoryEquivalence_inverse_commShift :
    (homotopyCategoryEquivalence B).inverse.CommShift ℤ :=
  (homotopyCategoryEquivalence B).commShiftInverse ℤ

/-- The comparison equivalence commutes with the translations: its unit and counit are
compatible with them. -/
instance homotopyCategoryEquivalence_commShift :
    (homotopyCategoryEquivalence B).CommShift ℤ :=
  (homotopyCategoryEquivalence B).commShift_of_functor ℤ

/-- The homotopy quotient followed by `CochainComplex.homotopyCategoryComparisonFunctor` is
isomorphic to `CochainComplex.cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B)`,
by `CategoryTheory.Quotient.lift.isLift`. -/
noncomputable def quotientCompComparisonIso :
    HomotopyCategory.quotient B (.up ℤ) ⋙ homotopyCategoryComparisonFunctor B ≅
      cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B) :=
  CategoryTheory.Quotient.lift.isLift (homotopic B (.up ℤ))
    (cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B)) _

/-- The isomorphism `CochainComplex.quotientCompComparisonIso B` commutes with the
translations. -/
instance quotientCompComparisonIso_natTrans_commShift :
    NatTrans.CommShift (quotientCompComparisonIso B).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (CategoryTheory.Quotient.lift.isLift
    (homotopic B (.up ℤ))
    (cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B)) _).hom ℤ)

end CochainComplex
