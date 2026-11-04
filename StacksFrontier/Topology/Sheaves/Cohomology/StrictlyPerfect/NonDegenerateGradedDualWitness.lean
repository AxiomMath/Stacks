module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.GradedDualOfTheStructureSheaf
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# A non-degenerate inhabitant of the hypotheses of the graded dual

`Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectStructureSheaf` instantiates the
hypotheses of the graded assembly of [Stacks, Tag 0FP9] at the complex `𝒪_X[0]`. On the ringed
space `Spec ℤ`, which has `1 ≠ 0` in its ring of global sections, the structure sheaf is not a
zero object, so the complex `𝒪[0]` is not zero in degree zero, and neither is its graded dual.

## Main results

* `Stacks.SheafOfModules.one_eq_zero_of_isZero_unit`: if the unit sheaf of modules over a sheaf
  of rings `R` is a zero object then `1 = 0` in every section ring of `R`.
* `Stacks.SheafOfModules.not_isZero_unit_of_one_ne_zero`: if some section ring of `R` has
  `1 ≠ 0`, then the unit sheaf of modules is not a zero object.
* `Stacks.SheafOfModules.OnSpace.specULiftIntRingedSpace`: the ringed space underlying
  `Spec ℤ`, at an arbitrary universe, via `ULift ℤ`.
* `Stacks.SheafOfModules.OnSpace.not_isZero_structureSheafComplex_X_zero_specULiftInt`: the
  degree-zero term of the witness complex on that ringed space is not a zero object.
* `Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectSpecULiftInt`: the graded dual
  pairing of [Stacks, Tag 0FP9] at that complex on that ringed space.
* `Stacks.SheafOfModules.OnSpace.isZero_left_of_exactPairing_of_isZero` and
  `isZero_X_of_isZero_dualGradedObject`: an object with a zero dual is zero, and its termwise
  form for the graded dual of a complex of `𝒪_X`-modules.
* `Stacks.SheafOfModules.OnSpace.not_isZero_dualGradedObject_zero_specULiftInt`: neither side of
  the pairing above is a zero object.

## Implementation notes

The ringed space is `(Spec (CommRingCat.of (ULift ℤ))).toRingedSpace`, so that
`AlgebraicGeometry.Scheme.ΓSpecIso` identifies its ring of global sections with `ULift ℤ`. The
`ULift` places the ring in the universe of `AlgebraicGeometry.RingedSpace.{u, u}`.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section

universe v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{max u v}}

/-- If the unit sheaf of modules over `R` is a zero object, then `1 = 0` in every section ring
of `R`. -/
theorem one_eq_zero_of_isZero_unit (h : IsZero (_root_.SheafOfModules.unit R)) (W : Cᵒᵖ) :
    (1 : R.obj.obj W) = 0 :=
  congrArg (fun f => ((_root_.SheafOfModules.unit R).unitHomEquiv f).val W)
    (h.eq_of_src (𝟙 (_root_.SheafOfModules.unit R)) 0)

/-- If `1 ≠ 0` in some section ring of `R`, then the unit sheaf of modules over `R` is not a
zero object. -/
theorem not_isZero_unit_of_one_ne_zero (W : Cᵒᵖ) (hW : (1 : R.obj.obj W) ≠ 0) :
    ¬ IsZero (_root_.SheafOfModules.unit R) :=
  fun h => hW (one_eq_zero_of_isZero_unit h W)

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- The ringed space underlying `Spec ℤ`, at universe `u`, via `ULift ℤ`. -/
def specULiftIntRingedSpace : AlgebraicGeometry.RingedSpace.{u, u} :=
  (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ))).toLocallyRingedSpace.toRingedSpace

/-- In the ring of global sections of the structure sheaf of `Spec ℤ`, `1 ≠ 0`. -/
theorem one_ne_zero_specULiftIntRingedSpace :
    (1 : (structureSheafRing (specULiftIntRingedSpace.{u})).obj.obj (op ⊤)) ≠ 0 := by
  intro h
  have e := (AlgebraicGeometry.Scheme.ΓSpecIso
    (CommRingCat.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv
  refine one_ne_zero (α := ULift.{u} ℤ) ?_
  rw [← map_one e, ← map_zero e]
  exact congrArg e h

/-- The structure sheaf of `Spec ℤ`, as a module over itself, is not a zero object. -/
theorem not_isZero_unit_specULiftInt :
    ¬ IsZero (_root_.SheafOfModules.unit (structureSheafRing (specULiftIntRingedSpace.{u}))) :=
  not_isZero_unit_of_one_ne_zero _ one_ne_zero_specULiftIntRingedSpace

/-- On `Spec ℤ`, the degree-zero term of the complex `𝒪[0]` is not a zero object. -/
theorem not_isZero_structureSheafComplex_X_zero_specULiftInt :
    ¬ IsZero ((structureSheafComplex (specULiftIntRingedSpace.{u})).X 0) :=
  fun h => not_isZero_unit_specULiftInt
    ((isZero_structureSheafComplex_X_zero_iff specULiftIntRingedSpace).mp h)

/-- The graded dual pairing of [Stacks, Tag 0FP9] between the complex `𝒪[0]` on `Spec ℤ` and
its graded dual. -/
def exactPairingDualGradedObjectSpecULiftInt :
    @ExactPairing _ _ (Strict.gradedMonoidalCategoryRingSheaf
        (specULiftIntRingedSpace.{u}).sheaf)
      ((structureSheafComplex (specULiftIntRingedSpace.{u})).X :
        GradedObject ℤ (Strict.Mod (specULiftIntRingedSpace.{u}).sheaf))
      (Strict.dualGradedObject (specULiftIntRingedSpace.{u}).sheaf
        (structureSheafComplex (specULiftIntRingedSpace.{u}))) :=
  exactPairingDualGradedObjectStructureSheaf specULiftIntRingedSpace

/-! ### The other side of the pairing -/

/-- In a preadditive monoidal category, if `B` is a dual of `A` and `B` is a zero object, then
`A` is a zero object. -/
theorem isZero_left_of_exactPairing_of_isZero {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [Preadditive D] [MonoidalPreadditive D] {A B : D}
    (q : ExactPairing A B) (hB : IsZero B) : IsZero A := by
  have htensor : IsZero (A ⊗ B) := (IsZero.iff_id_eq_zero _).2 <| by
    rw [← MonoidalCategory.whiskerLeft_id A B, hB.eq_of_src (𝟙 B) 0,
      MonoidalPreadditive.whiskerLeft_zero]
  let := q
  exact CategoryTheory.GradedObject.Monoidal.isZero_of_coevaluation_eq_zero
    (X := A) (Y := B) (htensor.eq_of_tgt _ 0)

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- Given a graded dual pairing between a complex `F` of `𝒪_X`-modules and its graded dual, if
the degree `-n` term of the graded dual is a zero object, then so is `F.X n`. -/
theorem isZero_X_of_isZero_dualGradedObject
    (F : CochainComplex (Strict.Mod X.sheaf) ℤ)
    (p : @ExactPairing _ _ (Strict.gradedMonoidalCategoryRingSheaf X.sheaf)
      (F.X : GradedObject ℤ (Strict.Mod X.sheaf)) (Strict.dualGradedObject X.sheaf F))
    (n : ℤ) (h : IsZero (Strict.dualGradedObject X.sheaf F (-n))) : IsZero (F.X n) := by
  let : MonoidalCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property
  let : MonoidalPreadditive (Strict.Mod X.sheaf) :=
    Strict.monoidalPreadditiveRingSheaf X.sheaf
  let : ∀ X₁ X₂ : GradedObject ℤ (Strict.Mod X.sheaf), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  let : ∀ X₁ : Strict.Mod X.sheaf, PreservesColimit (Functor.empty.{0} (Strict.Mod X.sheaf))
      ((curriedTensor (Strict.Mod X.sheaf)).obj X₁) := fun X₁ =>
    Strict.preservesColimit_tensorLeft X.sheaf _ X₁
  let : ∀ X₂ : Strict.Mod X.sheaf, PreservesColimit (Functor.empty.{0} (Strict.Mod X.sheaf))
      ((curriedTensor (Strict.Mod X.sheaf)).flip.obj X₂) := fun X₂ =>
    Strict.preservesColimit_tensorRight X.sheaf _ X₂
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Strict.Mod X.sheaf),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := Strict.hasGoodTensor₁₂Tensor X.sheaf
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Strict.Mod X.sheaf),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := Strict.hasGoodTensorTensor₂₃ X.sheaf
  let : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Strict.Mod X.sheaf),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := Strict.hasTensor₄ObjExt X.sheaf
  let := p
  exact isZero_left_of_exactPairing_of_isZero
    (CategoryTheory.GradedObject.Monoidal.exactPairingApply
      (F.X : GradedObject ℤ (Strict.Mod X.sheaf))
      (Strict.dualGradedObject X.sheaf F) n) h

/-- On `Spec ℤ`, the degree-zero term of the graded dual of the complex `𝒪[0]` is not a zero
object. -/
theorem not_isZero_dualGradedObject_zero_specULiftInt :
    ¬ IsZero (Strict.dualGradedObject (specULiftIntRingedSpace.{u}).sheaf
      (structureSheafComplex (specULiftIntRingedSpace.{u})) 0) := by
  intro h
  refine not_isZero_structureSheafComplex_X_zero_specULiftInt
    (isZero_X_of_isZero_dualGradedObject specULiftIntRingedSpace
      (structureSheafComplex specULiftIntRingedSpace)
      exactPairingDualGradedObjectSpecULiftInt 0 ?_)
  simpa using h

end Stacks.SheafOfModules.OnSpace

end

end
