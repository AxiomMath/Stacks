module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBase

/-!
# A quasi-separated algebraic stack is decent (Stacks 0GW2, the quasi-separated case)

An algebraic stack over `S` is *decent* (Stacks 0GW1) when every one of its points has a
field-valued representative whose 1-morphism `Spec k → 𝒳` is quasi-compact. This file proves that
an algebraic stack which is quasi-separated in the absolute sense of Stacks 050D part (8) is
decent: the quasi-separated case of Stacks 0GW2.

## Main results

* `AlgebraicGeometry.Stack.isDecent_of_isQuasiSeparated`: an algebraic stack which is
  quasi-separated in the absolute sense is decent.

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW2](https://stacks.math.columbia.edu/tag/0GW2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A quasi-separated algebraic stack is decent.** If `𝒳` is quasi-separated in the absolute
sense, then every point of `𝒳` has a field-valued representative which is quasi-compact. -/
@[stacks 0GW2 "quasi-separated case"]
theorem isDecent_of_isQuasiSeparated (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳) :
    IsDecent B S hS 𝒳.val := by
  intro x
  obtain ⟨p, rfl⟩ := Quotient.exists_rep x
  refine ⟨p, rfl,
    (isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒳 p).2 ?_⟩
  have hcomp : IsQuasiCompactMorphism B S hS
      (fieldValuedPointStackMorphism B S hS 𝒳 p ≫ structureMorphism B S hS 𝒳) := by
    rw [comp_structureMorphism B S hS (fieldValuedPointStackMorphism B S hS 𝒳 p)]
    exact isQuasiCompactMorphism_structureMorphism_fieldValuedPointBase B S hS p
  exact isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS _ _ hcomp
    (AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ 𝒳 h𝒳)

end AlgebraicGeometry.Stack

end
