module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Homology

/-!
# Finite filtered objects, filtered injectives, filtered quasi-isomorphisms and acyclicity

For an abelian category `𝒜`, the category `Filᶠ(𝒜)` of *finite filtered objects* is the full
subcategory of filtered objects whose filtration is finite. A finite filtered object is
*filtered injective* when each of its graded pieces is an injective object, a morphism of
filtered complexes is a *filtered quasi-isomorphism* when its map on each graded piece is a
quasi-isomorphism, and a complex of finite filtered objects is *filtered acyclic* when each of
its graded-piece complexes is acyclic.

The first three notions already exist. `CategoryTheory.FiniteFilteredObject` is exactly the
full subcategory the source describes; its defining predicate
`CategoryTheory.Filtration.IsFinite` asks for a step equal to the ambient object and a zero
step, and the construction needs no abelian hypothesis.
`CategoryTheory.FilteredObject.IsFilteredInjective` records both finiteness of the filtration
and injectivity of every graded piece, for a category with zero morphisms and cokernels, hence
in particular for an abelian one. `CochainComplex.filteredQuasiIso` models a complex of
filtered objects equivalently as a cochain complex with a decreasing filtration by
subcomplexes.

Filtered acyclicity is introduced below, kept on complexes of finite filtered objects rather
than transported along that equivalence to filtered complexes: the graded-piece complex at `p`
is obtained by applying `CategoryTheory.FiniteFilteredObject.grP p` degreewise. It is an
abbreviation, so the graded-piece acyclicity condition is available directly.

## Main definitions

* `CategoryTheory.FiniteFilteredObject.filteredAcyclic`: graded-piece acyclicity of a complex
  of finite filtered objects.

## References

* [Stacks Project, Tag 028A](https://stacks.math.columbia.edu/tag/028A)
* [Stacks Project, Tag 028B](https://stacks.math.columbia.edu/tag/028B)
* [Stacks Project, Tag 028D](https://stacks.math.columbia.edu/tag/028D)
* [Stacks Project, Tag 028E](https://stacks.math.columbia.edu/tag/028E)
-/

@[expose] public section

add_to_stacks 028A CategoryTheory.FilteredObject.IsFilteredInjective
add_to_stacks 028B CategoryTheory.FiniteFilteredObject
add_to_stacks 028D CochainComplex.filteredQuasiIso

namespace CategoryTheory.FiniteFilteredObject

universe v u

/-- A complex of finite filtered objects is filtered acyclic when every graded-piece complex
is acyclic. -/
@[stacks 028E]
abbrev filteredAcyclic (A : Type u) [Category.{v} A] [Abelian A]
    (K : CochainComplex (FiniteFilteredObject A) ℤ) : Prop :=
  ∀ p : ℤ, (((FiniteFilteredObject.grP p).mapHomologicalComplex (.up ℤ)).obj K).Acyclic

end CategoryTheory.FiniteFilteredObject

end
