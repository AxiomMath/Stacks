module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic

/-!
# The tower of canonical truncations from below

Let `A` be an abelian category with a derived category and let `E` be an object of `D(A)`. The
canonical truncations `τ_{≥ -n} E` form an inverse system indexed by `ℕ`: the map
`τ_{≥ -(n+1)} E ⟶ τ_{≥ -n} E` is the canonical comparison attached to `-(n+1) ≤ -n`. This file
records that inverse system as a functor `ℕᵒᵖ ⥤ D(A)`.

## Main definitions

* `Stacks.DerivedLimit.truncGETower`: the inverse system `n ↦ τ_{≥ -n} E` in `D(A)`.

## Implementation notes

The system is built by `CategoryTheory.Functor.ofOpSequence` from its objects and its successive
transition maps, so the transition map attached to `homOfLE (Nat.le_succ n)` is definitionally
the chosen comparison map; this is `Stacks.DerivedLimit.truncGETower_map_homOfLE_succ`.

The truncation functors and their comparison maps are those of the canonical t-structure
`DerivedCategory.TStructure.t` on `D(A)`. The universe of the derived category is left free rather
than fixed to `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0D62](https://stacks.math.columbia.edu/tag/0D62)
* [Stacks Project, Tag 0H72](https://stacks.math.columbia.edu/tag/0H72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.DerivedLimit

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The inverse system `n ↦ τ_{≥ -n} E` of canonical truncations from below of an object `E` of
a derived category, with the canonical comparison maps `τ_{≥ -(n+1)} E ⟶ τ_{≥ -n} E` as its
transition maps. -/
def truncGETower (E : DerivedCategory A) : ℕᵒᵖ ⥤ DerivedCategory A :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) fun n ↦
    (DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E

/-- The `n`-th term of the truncation tower is the truncation `τ_{≥ -n} E`. -/
@[simp]
theorem truncGETower_obj (E : DerivedCategory A) (n : ℕ) :
    (truncGETower A E).obj ⟨n⟩ = (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E :=
  rfl

/-- The transition map of the truncation tower is the canonical comparison map between two
truncations from below. -/
@[simp]
theorem truncGETower_map_homOfLE_succ (E : DerivedCategory A) (n : ℕ) :
    (truncGETower A E).map (homOfLE (Nat.le_succ n)).op =
      (DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

end Stacks.DerivedLimit

end
