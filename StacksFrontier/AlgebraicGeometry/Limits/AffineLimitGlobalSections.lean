module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Global sections of a limit of affine schemes over a directed poset

Let `α` be a nonempty directed preorder and let `E : αᵒᵖ ⥤ Scheme` be an inverse system of affine
schemes with limit cone `c`.  Global sections turn `c` into a filtered colimit of rings: every
global section of `c.pt` is the image of a global section at some stage, and a global section at
a stage which dies in the limit already dies at a later stage.

## Main results

* `AlgebraicGeometry.exists_appTop_eq_of_isAffine_of_isLimit_of_directed`: every global section
  of the limit comes from a stage.
* `AlgebraicGeometry.exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed`: a stage
  section with vanishing image in the limit vanishes at a later stage.

## Implementation notes

These are the two halves of Mathlib's description of the global sections of such a limit,
`AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit` and
`AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit`, transported from an
arbitrary cofiltered index category to the opposite of a directed preorder, where the transition
morphisms are indexed by inequalities.  This is the form in which filtered-colimit arguments on
the rings of global sections consume them.

The index poset lives in the same universe as the schemes.  This is not a convenience: with an
index in a strictly larger universe and no smallness hypothesis the statements are false, even
with every stage affine and nonempty — see
`StacksFrontier.AlgebraicGeometry.SmallnessNecessary.Basic`, where an inverse system of spectra of
fields indexed by `Ordinal` has empty limit, so that the unit at any stage dies in the limit and
at no later stage.

## References

* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α]
  (E : αᵒᵖ ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c) [∀ a, IsAffine (E.obj a)]

include hc

/-- **Every global section of a limit of affine schemes comes from a stage.**  For an inverse
system of affine schemes indexed by the opposite of a nonempty directed preorder, a global
section of the limit is the image of a global section at some stage. -/
theorem exists_appTop_eq_of_isAffine_of_isLimit_of_directed (r : Γ(c.pt, ⊤)) :
    ∃ (a : α) (x : Γ(E.obj (op a), ⊤)), (c.π.app (op a)).appTop.hom x = r := by
  have : IsCofiltered αᵒᵖ := inferInstance
  obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit E c hc r
  exact ⟨j.unop, t, ht⟩

/-- **A global section dying in a limit of affine schemes dies at a later stage.**  For an
inverse system of affine schemes indexed by the opposite of a nonempty directed preorder, a
global section at a stage whose image in the limit is zero is already carried to zero by a
transition morphism. -/
theorem exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed (a : α)
    (x : Γ(E.obj (op a), ⊤)) (hx : (c.π.app (op a)).appTop.hom x = 0) :
    ∃ (b : α) (h : a ≤ b), (E.map (homOfLE h).op).appTop.hom x = 0 := by
  have : IsCofiltered αᵒᵖ := inferInstance
  obtain ⟨j, g, hg⟩ := exists_appTop_map_eq_zero_of_isAffine_of_isLimit E c hc (op a) x hx
  refine ⟨j.unop, leOfHom g.unop, ?_⟩
  rwa [show (homOfLE (leOfHom g.unop)).op = g from Subsingleton.elim _ _]

end AlgebraicGeometry

end
