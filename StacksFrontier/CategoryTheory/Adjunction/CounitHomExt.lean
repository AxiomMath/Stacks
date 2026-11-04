module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Comparing two morphisms into a right adjoint through their adjoint transposes

Let `L ⊣ R` be an adjunction.  A morphism `g : X ⟶ R.obj Y` is determined by its adjoint
transpose `L.map g ≫ adj.counit.app Y`, since that transpose is the image of `g` under the
bijection `(adj.homEquiv X Y).symm`.  So an equality of two morphisms `X ⟶ R.obj Y` can always be
proved by proving the corresponding equality of transposes — an equality of morphisms of the other
category, in which the right adjoint does not occur at all.

## Main results

* `Stacks.Adjunction.hom_ext_of_map_comp_counit`: the extensionality principle just described.

## Implementation notes

The principle is used by hand in many places in this repository, as
`(adj.homEquiv _ _).symm.injective` followed by a rewrite along
`CategoryTheory.Adjunction.homEquiv_counit`.  Packaging it lets a proof whose goal is an equality
of morphisms into a right adjoint open with a single `apply` and then work with transposes only;
that is how the coherence properties of the cup product of an adjunction
(`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct`) are proved, since the
transpose of that cup product is the comparison of the two bifunctors followed by the counit in
each tensor factor.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- Two morphisms into `R.obj Y` are equal as soon as their adjoint transposes are: the transpose
of `g : X ⟶ R.obj Y` under an adjunction `adj : L ⊣ R` is `L.map g` followed by the component of
the counit at `Y`. -/
theorem hom_ext_of_map_comp_counit (adj : L ⊣ R) {X : C} {Y : D} {g g' : X ⟶ R.obj Y}
    (h : L.map g ≫ adj.counit.app Y = L.map g' ≫ adj.counit.app Y) : g = g' :=
  (adj.homEquiv X Y).symm.injective
    (by rwa [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit])

end Stacks.Adjunction
