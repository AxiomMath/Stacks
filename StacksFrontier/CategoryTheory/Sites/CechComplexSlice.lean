module

public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# The Čech intersections of a family in a slice category over a poset

Mathlib's Čech complex of a family `U : ι → C` is built from the products `inter U x` of the
objects selected by a tuple `x`, and `StacksFrontier/CategoryTheory/Sites/CechComplex.lean`
identifies those products with infima when `C` is a complete lattice. The Čech complex of a
*covering of an open subset* is formed instead in the slice category `Over V`, where `V` is the
covered open: that is the convention of Stacks 01EP, because the sections over the members of the
covering are then sections of a presheaf on `Over V`.

This file identifies the Čech intersections of a family in `Over V`, for `V` an element of a
complete lattice, with the infima taken in the lattice itself. The slice category over an object
of a partial order is *thin* — any two parallel morphisms agree — so the candidate infimum is a
product for trivial reasons, and the comparison with the chosen product is then an isomorphism
between two objects of a thin category, whence an equality of the underlying elements.

The hypothesis that the tuple is nonempty is necessary and not a convenience: the empty product
in `Over V` is the terminal object `V`, while the empty infimum is `⊤`. Čech complexes only use
tuples of length `n + 1`, so this costs a client nothing.

## Main results

* `Stacks.CategoryTheory.CechComplex.subsingleton_over_hom` — the slice category over an element
  of a partial order is thin.
* `Stacks.CategoryTheory.CechComplex.interOver_left_eq_iInf` — **the Čech intersection of a
  family in `Over V` has the infimum of the family as its underlying element.**

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace Stacks.CategoryTheory.CechComplex

section Thin

variable {L : Type u} [PartialOrder L] {V : L}

/-- **The slice category over an element of a partial order is thin.** A morphism of `Over V` is
a morphism of `L` together with a commutation property, and parallel morphisms of a partial
order are equal. -/
theorem subsingleton_over_hom (A B : Over V) : Subsingleton (A ⟶ B) :=
  ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

end Thin

section Lattice

variable {L : Type u} [CompleteLattice L] {V : L} [HasFiniteProducts (Over V)]
  {ι : Type w} (U : ι → L) (hU : ∀ i, U i ≤ V)

include hU

/-- **The Čech intersection of a family in a slice category is the infimum.** For a family
`U : ι → L` of elements below `V` in a complete lattice and a nonempty tuple `x`, the product in
`Over V` of the objects selected by `x` has `⨅ a, U (x a)` as its underlying element.

The candidate is a product for thinness reasons — a cone over the fan is a family of
inequalities `T ≤ U (x a)`, which is an inequality `T ≤ ⨅ a, U (x a)`, and the lift is unique
because there is at most one morphism — and two products of the same family are isomorphic,
hence equal in a partial order. -/
theorem interOver_left_eq_iInf {m : ℕ} (x : Fin (m + 1) → ι) :
    (inter (fun i => Over.mk (homOfLE (hU i))) x).left = ⨅ a, U (x a) := by
  have hWV : (⨅ a, U (x a)) ≤ V := le_trans (iInf_le (fun a => U (x a)) 0) (hU (x 0))
  have hlim : IsLimit (Fan.mk (Over.mk (homOfLE hWV) : Over V)
      (fun a => Over.homMk (homOfLE (iInf_le _ a)) :
        ∀ a, (Over.mk (homOfLE hWV) : Over V) ⟶ Over.mk (homOfLE (hU (x a))))) :=
    ⟨fun c => Over.homMk (homOfLE (le_iInf fun a => leOfHom (c.π.app ⟨a⟩).left)),
      fun _ _ => (subsingleton_over_hom _ _).elim _ _,
      fun _ _ _ => (subsingleton_over_hom _ _).elim _ _⟩
  have e := IsLimit.conePointUniqueUpToIso
    (isLimitInterFan (fun i => Over.mk (homOfLE (hU i))) x) hlim
  exact le_antisymm (leOfHom e.hom.left) (leOfHom e.inv.left)

end Lattice

end Stacks.CategoryTheory.CechComplex

end
