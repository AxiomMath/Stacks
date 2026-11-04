module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a bounded above complex of projectives

Let `A` be an abelian category and let `P` be a bounded above cochain complex of projective
objects of `A`. Morphisms out of `P` are unchanged by passage from the homotopy category to
the derived category: for every object `K` of the homotopy category the localization functor
induces a bijection
`Hom_{K(A)}(P, K) → Hom_{D(A)}(P, K)`.

## Main results

* `CochainComplex.Qh_map_bijective_of_projective_of_minus`: the localization functor
  `DerivedCategory.Qh` is bijective on morphisms out of a bounded above complex of
  projectives.

## Implementation notes

The equality of Hom-sets in the source is expressed as bijectivity of the canonical map
induced by `DerivedCategory.Qh`. Boundedness above is membership in `CochainComplex.minus`;
the target is allowed to be any object of the homotopy category, which includes the image of
every complex. The proof extracts a strict upper bound from the boundedness hypothesis,
whence `P` is K-projective by `CochainComplex.isKProjective_of_projective`, and then applies
`CochainComplex.IsKProjective.Qh_map_bijective`.

## References

* [Stacks Project, Tag 03T6](https://stacks.math.columbia.edu/tag/03T6)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Stacks 03T6, part (2).** A bounded above complex of projective objects computes
morphisms from it in the derived category already in the homotopy category. -/
@[stacks 03T6 "projective_hom", sga "4½ Etat_0 3.2.3" "(4) proj. analogue"]
theorem Qh_map_bijective_of_projective_of_minus [HasDerivedCategory.{w} A]
    (P : CochainComplex A ℤ) (K : HomotopyCategory A (ComplexShape.up ℤ))
    (hP : CochainComplex.minus A P) [∀ n, Projective (P.X n)] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶ K) → _) := by
  obtain ⟨n, hn⟩ := hP
  let : P.IsStrictlyLE n := hn
  let := CochainComplex.isKProjective_of_projective P n
  exact CochainComplex.IsKProjective.Qh_map_bijective P K

end CochainComplex
