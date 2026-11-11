module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import StacksCore.Tactic.StacksAttribute

/-!
# Bounded above cochain complexes

Let `C` be a category with zero morphisms. A `ℤ`-indexed cochain complex `K` over `C`
is *bounded above* when `Kⁿ = 0` for all `n ≫ 0`, that is, when there is an integer `n`
with `K.IsStrictlyLE n`. This file introduces that property of objects,
`CochainComplex.minus`, as the mirror image of `CochainComplex.plus` (bounded below).

Writing `Comp(C) = CochainComplex C ℤ` for the category of cochain complexes and
`K(C) = HomotopyCategory C (ComplexShape.up ℤ)` for the category with the same objects and
homotopy classes of maps of complexes as morphisms, the bounded variants are expressed as follows:

* `Comp⁺(C)`, `Comp⁻(C)` and `Compᵇ(C)` are the full subcategories of `Comp(C)` cut out
  by `CochainComplex.plus C`, `CochainComplex.minus C` and `CochainComplex.bounded C`
  (the last in `StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated`); they are
  `CochainComplex.Plus C`, `CochainComplex.Minus C` and `CochainComplex.Bounded C`.
* `K⁺(C)`, `K⁻(C)` and `Kᵇ(C)` are the full subcategories of `K(C)` cut out by the strict
  images of those three properties along `HomotopyCategory.quotient C (ComplexShape.up ℤ)`;
  these are `HomotopyCategory.plus C`, `HomotopyCategory.minus C` and
  `HomotopyCategory.bounded C`, with full subcategories `HomotopyCategory.Plus C`,
  `HomotopyCategory.Minus C` and `HomotopyCategory.Bounded C`.

## Main definitions

* `CochainComplex.minus`: the property of a `ℤ`-indexed cochain complex of being bounded
  above.
* `CochainComplex.Minus`: the full subcategory `Comp⁻(C)` of bounded above complexes.

## References

* [Stacks, Tag 013H]
-/

open CategoryTheory Limits

@[expose] public section

namespace CochainComplex

variable (C : Type*) [Category C] [HasZeroMorphisms C]

/-- The property of cochain complexes that are bounded above. -/
@[stacks 013H "(3) bounded above complexes", ega "0 11.2.1" "bounded above",
  sga "4½ Etat_0 1.2.3" "bounded-above complexes"]
public def minus : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyLE n

variable {C} in
/-- Unfolding lemma for `CochainComplex.minus`. -/
lemma minus_iff (K : CochainComplex C ℤ) :
    CochainComplex.minus C K ↔ ∃ (n : ℤ), K.IsStrictlyLE n :=
  Iff.rfl

/-- `Comp⁻(C)`: the full subcategory of `CochainComplex C ℤ` consisting of the bounded above
complexes. -/
@[stacks 013H "(5) Comp⁻(A), the full subcategory of bounded above complexes"]
abbrev Minus := (CochainComplex.minus C).FullSubcategory

end CochainComplex

end
