module

public import StacksFrontier.CategoryTheory.Filtered.SpanCocones

/-!
# Connected components inherit span cocones (Stacks 09WS)

Stacks 09WS says that a category `J` in which every span `y ← x → z` can be completed to a
commutative square is either empty, or a nonempty disjoint union of connected categories
each of which again has that property.

Two of the three assertions are already Mathlib's, for an arbitrary category `J`:

* the decomposition into connected components is `CategoryTheory.decomposedTo`, an
  equivalence `(Σ j : ConnectedComponents J, j.Component) ≌ J`, and
* each piece is connected — `CategoryTheory.instIsConnectedComponent` — and in particular
  nonempty, by `CategoryTheory.instNonemptyComponent`.

Note that these hold unconditionally, so the empty-versus-nonempty case split of the source
statement carries no mathematical content: when `J` is empty, `ConnectedComponents J` is
empty too and there is nothing to check. What is specific to 09WS is therefore the
inheritance of the span-cocone property, `hasSpanCocone_component` below: a span in
`j.Component` is a span in `J`, and the completing object supplied by the hypothesis on `J`
lies in the component `j` because it receives a morphism from an object of `j`.

The predicate `CategoryTheory.HasSpanCocone` is the one introduced for Stacks 002X, whose
first hypothesis it is; see `StacksFrontier.CategoryTheory.Filtered.SpanCocones`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v u

/-- **Stacks 09WS.** Each connected component of a category with span cocones again has
span cocones. Together with `CategoryTheory.instIsConnectedComponent` and
`CategoryTheory.decomposedTo` this exhibits such a category as a disjoint union of
connected categories with span cocones. -/
@[stacks 09WS]
theorem hasSpanCocone_component {J : Type u} [Category.{v} J] (h : HasSpanCocone J)
    (j : ConnectedComponents J) : HasSpanCocone j.Component := by
  intro x y z f g
  obtain ⟨w, a, b, hab⟩ := h f.hom g.hom
  have hw : ConnectedComponents.mk w = j :=
    (ConnectedComponents.mk_eq_mk_of_hom a).symm.trans y.property
  exact ⟨⟨w, hw⟩, ⟨a⟩, ⟨b⟩, InducedCategory.Hom.ext hab⟩

end CategoryTheory
