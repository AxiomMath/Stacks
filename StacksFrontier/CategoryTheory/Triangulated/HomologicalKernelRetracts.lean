module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of a homological functor is closed under retracts

Mathlib registers the kernel `F.homologicalKernel` of a homological functor as a triangulated
subcategory closed under isomorphisms, but not as a subcategory closed under retracts, and the
same two instances and the same omission hold for its instance
`CategoryTheory.HomotopyCategory.subcategoryAcyclic`, the acyclic objects of the homotopy
category of an abelian category. Closure under retracts is the third of the three conditions that
make a subcategory *thick*, and it is what
`DGCategory.RightModule.yonedaInverseImage_eq_of_isTriangulated` asks of the subcategory it
identifies — see
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/YonedaKernelAcyclicCompact.lean`.

This file supplies it. The argument is one line of diagram chasing and uses nothing about `F`
beyond functoriality: a retract `X` of `Y` is carried by `(-)⟦n⟧ ⋙ F` to a retract of
`F(Y⟦n⟧)`, which is zero, so the identity of `F(X⟦n⟧)` factors through a zero object and is
therefore itself zero.

In particular no homologicality of `F` is needed, and the acyclic objects of an abelian category
are closed under retracts with no hypothesis on the category beyond abelianness, which is what
[Stacks, Tag 09LJ] assumes of its abelian category.

## Main results

* `CategoryTheory.Functor.homologicalKernel_isStableUnderRetracts`: the kernel of a functor out
  of a category with a translation is closed under retracts.
* `CategoryTheory.HomotopyCategory.subcategoryAcyclic_isStableUnderRetracts`: hence so are the
  acyclic objects of the homotopy category of an abelian category.

## References

* [Stacks Project, Tag 09LJ](https://stacks.math.columbia.edu/tag/09LJ)
* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] {A : Type u'} [Category.{v'} A]
  [HasZeroMorphisms A]

/-- **The kernel of a homological functor is closed under retracts.** If `X` is a retract of `Y`
in `C` and `F(Y⟦n⟧)` is zero for every `n`, then `F(X⟦n⟧)` is zero for every `n`: applying
`(-)⟦n⟧ ⋙ F` to the retract data makes the identity of `F(X⟦n⟧)` a composite through the zero
object `F(Y⟦n⟧)`, hence zero, and an object with zero identity is a zero object.

Together with Mathlib's `CategoryTheory.ObjectProperty.IsTriangulated` and
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` instances on
`CategoryTheory.Functor.homologicalKernel` this makes that subcategory thick. -/
instance Functor.homologicalKernel_isStableUnderRetracts (F : C ⥤ A) :
    F.homologicalKernel.IsStableUnderRetracts where
  of_retract {X Y} hr hY n := by
    have h := (hr.map (CategoryTheory.shiftFunctor C n)).map F
    rw [IsZero.iff_id_eq_zero, ← h.retract, (hY n).eq_of_tgt h.i 0, zero_comp]

/-- **The acyclic objects of the homotopy category of an abelian category are closed under
retracts.** `CategoryTheory.HomotopyCategory.subcategoryAcyclic` is the kernel of the degree-zero
homology functor, so this is
`CategoryTheory.Functor.homologicalKernel_isStableUnderRetracts`; it is stated as a separate
instance because the kernel is hidden behind a definition that instance resolution does not
unfold.

With Mathlib's two instances on the same subcategory, the acyclic objects are thick for any
abelian category. -/
@[sga "4½ Etat_0 2.4.1" "special case"]
instance HomotopyCategory.subcategoryAcyclic_isStableUnderRetracts (B : Type u) [Category.{v} B]
    [Abelian B] : (HomotopyCategory.subcategoryAcyclic B).IsStableUnderRetracts := by
  dsimp only [HomotopyCategory.subcategoryAcyclic]
  infer_instance

end CategoryTheory

end
