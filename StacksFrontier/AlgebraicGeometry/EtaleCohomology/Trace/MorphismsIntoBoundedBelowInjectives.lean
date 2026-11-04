module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms into a bounded below complex of injectives

Let `A` be an abelian category and let `I` be a bounded below cochain complex of injective
objects of `A`. Morphisms into `I` are unchanged by passage from the homotopy category to
the derived category: for every object `K` of the homotopy category the localization functor
induces a bijection
`Hom_{K(A)}(K, I) → Hom_{D(A)}(K, I)`.

## Main results

* `CochainComplex.Qh_map_bijective_of_injective_of_plus`: the localization functor
  `DerivedCategory.Qh` is bijective on morphisms into a bounded below complex of
  injectives.

## Implementation notes

The equality of Hom-sets in the source is expressed as bijectivity of the canonical map
induced by `DerivedCategory.Qh`. Boundedness below is membership in `CochainComplex.plus`;
the source is allowed to be any object of the homotopy category, which includes the image of
every complex. The proof extracts a strict lower bound from the boundedness hypothesis,
whence `I` is K-injective by `CochainComplex.isKInjective_of_injective`, and then applies
`CochainComplex.IsKInjective.Qh_map_bijective`.

## References

* [Stacks Project, Tag 03T6](https://stacks.math.columbia.edu/tag/03T6)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Stacks 03T6, part (1).** A bounded below complex of injective objects computes
morphisms into it in the derived category already in the homotopy category. -/
@[stacks 03T6 "injective_hom"]
theorem Qh_map_bijective_of_injective_of_plus [HasDerivedCategory.{w} A]
    (K : HomotopyCategory A (ComplexShape.up ℤ)) (I : CochainComplex A ℤ)
    (hI : CochainComplex.plus A I) [∀ n, Injective (I.X n)] :
    Function.Bijective (DerivedCategory.Qh.map :
      (K ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) → _) := by
  obtain ⟨n, hn⟩ := hI
  let : I.IsStrictlyGE n := hn
  let := CochainComplex.isKInjective_of_injective I n
  exact CochainComplex.IsKInjective.Qh_map_bijective K I

end CochainComplex
