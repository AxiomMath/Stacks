module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms

/-!
# The triangulated structure on `ShrinkHoms C`

Let `C` be a pretriangulated category whose morphism types are `w`-small. Then
`ShrinkHoms.{w} C`, the same objects with morphism types replaced by small models, carries a
pretriangulated structure for which the equivalence `ShrinkHoms.functor C : C ⥤ ShrinkHoms C`
commutes with the shift and is a triangulated functor; it is triangulated when `C` is. This is
what lets results stated for triangulated categories with morphisms in `Type w` and coproducts
indexed by `Type w` be applied to a category, such as a derived category of the standard model,
which is only locally small in `w`.

The structure is obtained by viewing `ShrinkHoms.functor C` as the localization of `C` at its
isomorphisms: the isomorphisms have a left calculus of fractions and are compatible with the
shift and with the triangulation, so the shift and the distinguished triangles descend.

## Main results

* `CategoryTheory.Pretriangulated.exists_triangulatedEquivalence_of_locallySmall`: a locally
  small pretriangulated category is equivalent, by an equivalence whose two halves are additive,
  commute with the shift and are triangulated, to a pretriangulated category with small morphism
  types, which is triangulated when the original one is.

The three properties of the isomorphisms that make the descent possible are
`CategoryTheory.Pretriangulated.isomorphisms_hasLeftCalculusOfFractions`,
`isomorphisms_isCompatibleWithShift` and `isomorphisms_isCompatibleWithTriangulation`.

## Implementation notes

The statement is existential rather than a family of instances on `ShrinkHoms C`: the category
instance of `ShrinkHoms C` is indexed by the universe of a `LocallySmall` instance, which is not
determined by the type `ShrinkHoms C`, so instances stated on it could select an unintended
universe (`LocallySmall.{v} C` always holds). The existential binds the category structure of
the model with its universe fixed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe w v u

namespace CategoryTheory.Pretriangulated

/-- **A locally small pretriangulated category has a triangulated model with small morphisms.**
If `C` is pretriangulated and `LocallySmall.{w}`, there is a pretriangulated category `D` with
morphisms in `Type w` and an equivalence `e : C ≌ D` both of whose halves are additive, commute
with the shift and are triangulated; `D` is triangulated when `C` is. The model is
`ShrinkHoms.{w} C`, with the structure descended along `ShrinkHoms.functor C`, the localization
of `C` at its isomorphisms. -/
theorem exists_triangulatedEquivalence_of_locallySmall
    (C : Type u) [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [LocallySmall.{w} C] :
    ∃ (D : Type u) (_ : Category.{w} D) (_ : Preadditive D) (_ : HasZeroObject D)
      (_ : HasShift D ℤ) (_ : ∀ n : ℤ, (shiftFunctor D n).Additive) (_ : Pretriangulated D)
      (e : C ≌ D) (_ : e.functor.Additive) (_ : e.inverse.Additive)
      (_ : e.functor.CommShift ℤ) (_ : e.inverse.CommShift ℤ)
      (_ : e.functor.IsTriangulated) (_ : e.inverse.IsTriangulated),
      IsTriangulated C → IsTriangulated D := by
  let : Category.{w} (ShrinkHoms C) := inferInstance
  let e := ShrinkHoms.equivalence.{w} C
  let W := MorphismProperty.isomorphisms C
  let := isomorphisms_hasLeftCalculusOfFractions C
  let := isomorphisms_isCompatibleWithShift C
  let := isomorphisms_isCompatibleWithTriangulation C
  let := Functor.IsLocalization.of_isEquivalence e.functor W le_rfl
  let := HasShift.localized e.functor W ℤ
  let := Functor.CommShift.localized e.functor W ℤ
  let : e.functor.Additive := ShrinkHoms.instAdditiveFunctor C
  let : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
  let : HasZeroObject (ShrinkHoms C) :=
    ⟨⟨e.functor.obj 0, Functor.map_isZero e.functor (isZero_zero C)⟩⟩
  have hshift : ∀ n : ℤ, (shiftFunctor (ShrinkHoms C) n).Additive := fun n => by
    rw [Localization.functor_additive_iff e.functor W]
    exact Functor.additive_of_iso (e.functor.commShiftIso n)
  let := Triangulated.Localization.pretriangulated e.functor W
  let : e.functor.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor e.functor W
  let := e.commShiftInverse ℤ
  let := e.commShift_of_functor ℤ
  let : e.inverse.IsTriangulated := e.toAdjunction.isTriangulated_rightAdjoint
  exact ⟨ShrinkHoms C, inferInstance, inferInstance, inferInstance, inferInstance, hshift,
    inferInstance, e, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, fun _ => Triangulated.Localization.isTriangulated e.functor W⟩

end CategoryTheory.Pretriangulated

end
