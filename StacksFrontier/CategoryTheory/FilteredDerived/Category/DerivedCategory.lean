module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.FilteredDerivedCategory.Basic

/-!
# The filtered derived category

Let `A` be an abelian category. Starting from the category `Comp(Fil^f(A))` of integer-indexed
cochain complexes of finite filtered objects, one passes to the homotopy category
`K(Fil^f(A))` and localizes at the filtered quasi-isomorphisms — the morphisms whose map on
every graded piece is a quasi-isomorphism — to obtain the filtered derived category `DF(A)`.
Restricting throughout to complexes bounded below gives `Comp⁺(Fil^f(A))`, `K⁺(Fil^f(A))` and
the bounded below filtered derived category `DF⁺(A)`.

## Main definitions

* `CochainComplex (CategoryTheory.FiniteFilteredObject A) ℤ` is `Comp(Fil^f(A))`, and
  `CochainComplex.Plus (CategoryTheory.FiniteFilteredObject A)` is `Comp⁺(Fil^f(A))`.
* `HomotopyCategory (CategoryTheory.FiniteFilteredObject A) (.up ℤ)` is `K(Fil^f(A))`, and
  `HomotopyCategory.Plus (CategoryTheory.FiniteFilteredObject A)` is `K⁺(Fil^f(A))`.
* `CochainComplex.filteredQuasiIsoC` is the morphism property of filtered
  quasi-isomorphisms of complexes of finite filtered objects.
* `CochainComplex.FilteredDerivedCategory` is `DF(A)` and
  `CochainComplex.FilteredDerivedCategory.Qh` is the localization functor from
  `K(Fil^f(A))`.
* `CategoryTheory.FilteredDerived.filteredDerivedPlus` is `DF⁺(A)`.

## Implementation notes

A complex of finite filtered objects carries a finite filtration separately in each
cohomological degree; it is not the same thing as a filtered cochain complex, and the former
is what is used here. The `p`-th graded map of a morphism of such complexes is obtained by
applying `CategoryTheory.FiniteFilteredObject.grP p` degreewise, which is how
`CochainComplex.filteredQuasiIsoC` is defined.

`CochainComplex.FilteredDerivedCategory` is modelled by filtered complexes whose filtration
is finite in each degree, and `CochainComplex.FilteredDerivedCategory.Qh` identifies that
model as the localization of `K(Fil^f(A))` at the filtered quasi-isomorphisms by way of its
`CategoryTheory.Functor.IsLocalization` instance. For the bounded below category the class
inverted is the inverse image of the filtered quasi-isomorphisms of `K(Fil^f(A))` along the
full inclusion of `K⁺(Fil^f(A))`, which is the localization literally prescribed by the
source rather than the equivalent full-subcategory model of `DF(A)`. In each case the
existing construction is used rather than renamed, so that clients work with the existing
cochain complex, homotopy category and localization APIs without unfolding a new name.

## References

* [Stacks Project, Tag 03TA](https://stacks.math.columbia.edu/tag/03TA)
* [Stacks Project, Tag 013H](https://stacks.math.columbia.edu/tag/013H)
-/

add_to_stacks 03TA "filtered_complexes" CochainComplex
add_to_stacks 03TA "filtered_complexes" CochainComplex.Plus
add_to_sga "2 VIII 1.4" CochainComplex.Plus
add_to_sga "4 Vbis 2.5.1" "partial" CochainComplex.Plus
add_to_stacks 03TA "filtered_homotopy" HomotopyCategory
add_to_sga "4 Vbis 2.5.1" HomotopyCategory
add_to_sga "4 XVII 2.2.8" "absolute case of K(A/B)" HomotopyCategory
add_to_sga "4½ Etat_0 1.2.2" HomotopyCategory
add_to_sga "4½ Rapport 4.3" "arrows of K_parf(Λ)" HomotopyCategory
add_to_sga "6 I 1.1.5" "partial" HomotopyCategory
add_to_ega "0 20.6.26" HomotopyCategory
add_to_stacks 03TA "filtered_homotopy" HomotopyCategory.Plus
add_to_sga "4 Vbis 2.3.3" "(A)" HomotopyCategory.Plus
add_to_sga "4 Vbis 2.5.1" "K⁺(F(A))" HomotopyCategory.Plus
add_to_sga "4 XVII 2.2.10" "special case" HomotopyCategory.Plus
add_to_sga "4½ Etat_0 1.2.3" HomotopyCategory.Plus
add_to_sga "6 I 1.1.5" "the fiber K⁺(C_X)" HomotopyCategory.Plus
add_to_stacks 03TA "filtered_quasi_isomorphism" CochainComplex.filteredQuasiIsoC
add_to_stacks 03TA "filtered_derived" CochainComplex.FilteredDerivedCategory
add_to_stacks 03TA "filtered_derived" CochainComplex.FilteredDerivedCategory.Qh

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredDerived

/-- The localisation of `K⁺(Fil^f(A))` at filtered quasi-isomorphisms. -/
@[stacks 03TA "filtered_derived_plus", sga "4 Vbis 2.5.1" "D^+F(A)"]
abbrev filteredDerivedPlus (A : Type u) [Category.{v} A] [Abelian A] :=
  ((HomotopyCategory.filteredQuasiIso A).inverseImage
    (HomotopyCategory.Plus.ι (FiniteFilteredObject A))).Localization

end CategoryTheory.FilteredDerived

end
