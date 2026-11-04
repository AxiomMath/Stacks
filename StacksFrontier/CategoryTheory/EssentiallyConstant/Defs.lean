module

import StacksFrontier.CategoryTheory.EssentiallyConstant.Operations
public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import StacksCore.Tactic.EgaSgaAttribute


/-!
# Essentially constant systems

Let `𝒞` be a category and let `I` be a directed set, viewed as a category in the standard way
(`CategoryTheory.Preorder.smallCategory`), so that a *directed system* `(M_i, f_ii')` is a
functor `M : I ⥤ 𝒞` and a *directed inverse system* is a functor `M : Iᵒᵖ ⥤ 𝒞`. Such a system is
*essentially constant* when the underlying diagram is essentially constant, i.e.
`IsEssentiallyConstantInd` holds for `M`, respectively for `Mᵒᵖ`.

## Main definitions

* `CategoryTheory.IsEssentiallyConstantSystem`: essential constancy of a directed system;
* `CategoryTheory.IsEssentiallyConstantInverseSystem`: essential constancy of a directed inverse
  system.

## Main results

* `CategoryTheory.isEssentiallyConstantInd_of_isEventuallyConstantFrom` and
  `CategoryTheory.isEssentiallyConstantInd_op_of_isEventuallyConstantTo`: Mathlib's
  `CategoryTheory.Functor.IsEventuallyConstantFrom` and
  `CategoryTheory.Functor.IsEventuallyConstantTo` imply essential constancy, together with the
  two corollaries `CategoryTheory.isEssentiallyConstantSystem_of_isEventuallyConstantFrom` and
  `CategoryTheory.isEssentiallyConstantInverseSystem_of_isEventuallyConstantTo` for systems;
* `CategoryTheory.IsEssentiallyConstantSystem.hasColimit` and
  `CategoryTheory.IsEssentiallyConstantInverseSystem.hasLimit`: an essentially constant system
  has a colimit and an essentially constant inverse system has a limit.

## References

* [Stacks Project, Tag 05PV](https://stacks.math.columbia.edu/tag/05PV)
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite EssentiallyConstantInd

universe v u v' u'

section Diagram

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]

/-- A diagram over a filtered category which is eventually constant from `i₀` (all transition
morphisms out of `i₀` are isomorphisms) is an essentially constant diagram. -/
theorem isEssentiallyConstantInd_of_isEventuallyConstantFrom [IsFiltered J] {M : J ⥤ C} {i₀ : J}
    (h : M.IsEventuallyConstantFrom i₀) : IsEssentiallyConstantInd M :=
  ⟨Cocone.mk (M.obj i₀) h.cocone.ι, i₀, 𝟙 _, by simp, fun j =>
    ⟨IsFiltered.max i₀ j, IsFiltered.leftToMax i₀ j, IsFiltered.rightToMax i₀ j, by
      simp [Functor.IsEventuallyConstantFrom.coconeιApp]⟩⟩

/-- A diagram over a cofiltered category which is eventually constant to `i₀` is essentially
constant as a pro-object, i.e. its opposite diagram is an essentially constant diagram. -/
theorem isEssentiallyConstantInd_op_of_isEventuallyConstantTo [IsCofiltered J] {M : J ⥤ C} {i₀ : J}
    (h : M.IsEventuallyConstantTo i₀) : IsEssentiallyConstantInd M.op :=
  isEssentiallyConstantInd_of_isEventuallyConstantFrom (i₀ := op i₀) fun {_} f =>
    have := h f.unop
    inferInstanceAs (IsIso (M.map f.unop).op)

end Diagram

section System

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I] {C : Type u'} [Category.{v'} C]

/-- A directed system `(M_i, f_ii')`, i.e. a functor `M : I ⥤ 𝒞` on a directed set, is an
*essentially constant system* when the diagram `M` is essentially constant. -/
@[stacks 05PV "directed system"]
def IsEssentiallyConstantSystem (M : I ⥤ C) : Prop :=
  IsEssentiallyConstantInd M

/-- A directed inverse system `(M_i, f_ii')`, i.e. a functor `M : Iᵒᵖ ⥤ 𝒞` on the opposite of a
directed set, is an *essentially constant inverse system* when the diagram `M` is essentially
constant as a pro-object, i.e. when the opposite diagram `Mᵒᵖ` is an essentially constant
diagram. -/
@[stacks 05PV "directed inverse system"]
def IsEssentiallyConstantInverseSystem (M : Iᵒᵖ ⥤ C) : Prop :=
  IsEssentiallyConstantInd M.op

/-- A directed system whose transition morphisms out of some index are all isomorphisms is an
essentially constant system. -/
theorem isEssentiallyConstantSystem_of_isEventuallyConstantFrom {M : I ⥤ C} {i₀ : I}
    (h : M.IsEventuallyConstantFrom i₀) : IsEssentiallyConstantSystem M :=
  isEssentiallyConstantInd_of_isEventuallyConstantFrom h

/-- A directed inverse system whose transition morphisms into some index are all isomorphisms is
an essentially constant inverse system. -/
theorem isEssentiallyConstantInverseSystem_of_isEventuallyConstantTo {M : Iᵒᵖ ⥤ C} {i₀ : Iᵒᵖ}
    (h : M.IsEventuallyConstantTo i₀) : IsEssentiallyConstantInverseSystem M :=
  isEssentiallyConstantInd_op_of_isEventuallyConstantTo h

omit [IsDirectedOrder I] [Nonempty I] in
/-- An essentially constant system indexed by a preorder, not necessarily directed, has a
colimit. -/
theorem IsEssentiallyConstantSystem.hasColimit {M : I ⥤ C} (h : IsEssentiallyConstantSystem M) :
    HasColimit M :=
  IsEssentiallyConstantInd.hasColimit h

omit [IsDirectedOrder I] [Nonempty I] in
/-- An essentially constant inverse system indexed by the opposite of a preorder, not
necessarily directed, has a limit. -/
@[sga "5 V 4.1.4" "Existence"]
theorem IsEssentiallyConstantInverseSystem.hasLimit {M : Iᵒᵖ ⥤ C}
    (h : IsEssentiallyConstantInverseSystem M) : HasLimit M :=
  IsEssentiallyConstantInd.hasLimit_of_op h

end System

end CategoryTheory
