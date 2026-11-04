module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Colimit.Ring
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
import all StacksFrontier.RingTheory.SpreadingOut.ColimitSystem
public import StacksFrontier.RingTheory.SpreadingOut.ColimitSystem

/-!
# The abelian colimit criterion with independent universes

This module carries the declarations that extend
`StacksFrontier.RingTheory.SpreadingOut.ColimitSystem`,
which is the base text, unchanged.
-/

@[expose] public section

universe u

namespace Stacks.SpreadingOut.LocalModuleSystem

open CategoryTheory Limits
open scoped TensorProduct

attribute [local instance] tailFunctor_full tailFunctor_faithful

attribute [local instance] tailFunctor_final

/-- **A criterion for a cocone of abelian groups over a filtered index to be a colimit,
with independent index and coefficient universes:**
its legs are jointly surjective, and an element killed by a leg already dies at a later
stage. Mathlib has the two consequences — `CategoryTheory.Limits.Concrete.colimit_exists_rep`
and `CategoryTheory.Limits.IsColimit.eq_iff` — but not this converse.

The index universe and the coefficient universe are independent, subject to `UnivLE`: that is
what makes the colimit of `F` exist in `AddCommGrpCat.{w₂}` and makes the forgetful functor
preserve it, which is what the proof compares the given cocone against. With the two universes
equal the condition is `UnivLE.self` and so invisible. -/
public noncomputable def isColimitAddCommGrpCatOfUnivLE.{w₁, w₂} {J : Type w₁} [SmallCategory J]
    [IsFiltered J] [UnivLE.{w₁, w₂}]
    (F : J ⥤ AddCommGrpCat.{w₂}) (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ (j : J) (y : F.obj j), (c.ι.app j) y = x)
    (hzero : ∀ (j : J) (y : F.obj j), (c.ι.app j) y = 0 →
      ∃ (k : J) (f : j ⟶ k), (F.map f) y = 0) :
    IsColimit c := by
  letI : PreservesFilteredColimitsOfSize.{w₁, w₁} (forget AddCommGrpCat.{w₂}) :=
    preservesFilteredColimitsOfSize_of_univLE _
  have hc := colimit.isColimit F
  have hfac : ∀ (j : J) (y : F.obj j), (hc.desc c) ((colimit.ι F j) y) = (c.ι.app j) y :=
    fun j y => congrArg (fun g : F.obj j ⟶ c.pt => g y) (hc.fac c j)
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : F.obj j),
      (colimit.ι F k) ((F.map f) y) = (colimit.ι F j) y :=
    fun {j k} f y => congrArg (fun t : F.obj j ⟶ colimit F => t y) (colimit.w F f)
  have hcw : ∀ {j k : J} (f : j ⟶ k) (y : F.obj j),
      (c.ι.app k) ((F.map f) y) = (c.ι.app j) y :=
    fun {j k} f y => congrArg (fun t : F.obj j ⟶ c.pt => t y) (c.w f)
  haveI : IsIso (hc.desc c) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun z z' hzz' => ?_, fun x => ?_⟩
    · obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep F z
      obtain ⟨j', y', rfl⟩ := Concrete.colimit_exists_rep F z'
      rw [hfac, hfac] at hzz'
      have hk : (c.ι.app (IsFiltered.max j j'))
          ((F.map (IsFiltered.leftToMax j j')) y
            - (F.map (IsFiltered.rightToMax j j')) y') = 0 := by
        rw [map_sub, hcw, hcw, hzz', sub_self]
      obtain ⟨m, t, ht⟩ := hzero _ _ hk
      rw [map_sub, sub_eq_zero] at ht
      rw [← hw (IsFiltered.leftToMax j j' ≫ t) y, ← hw (IsFiltered.rightToMax j j' ≫ t) y',
        F.map_comp, F.map_comp]
      exact congrArg _ ht
    · obtain ⟨j, y, rfl⟩ := hsurj x
      exact ⟨(colimit.ι F j) y, hfac j y⟩
  exact hc.ofPointIso

end Stacks.SpreadingOut.LocalModuleSystem

end
