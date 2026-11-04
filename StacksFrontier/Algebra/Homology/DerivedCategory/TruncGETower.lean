module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic

/-!
# The tower of truncations from below of an object of a derived category

For an object `E` of the derived category of an abelian category, this file defines the inverse
system `n ↦ τ_{≥ -n} E` indexed by `ℕᵒᵖ`, whose transition maps are the canonical morphisms
`τ_{≥ -(n+1)} E ⟶ τ_{≥ -n} E`.  Its derived limit is what the convergence statements of Stacks
0D62 (for a ringed space) and Stacks 0D6M (for a ringed site) compare with `E`.

The definition is deliberately stated for a bare abelian category with a chosen derived
category, with no sheaf-theoretic input, so that the ringed-space and ringed-site statements
speak about the *same* tower.

## Main definitions

* `truncGETower`: the inverse system `n ↦ τ_{≥ -n} E`.

## Implementation notes

The system is built with `CategoryTheory.Functor.ofOpSequence`, so only the successor transition
maps have to be supplied, and the transition map for `n ≤ m` is the composite of those.  The
truncation functors and the comparison natural transformations are Mathlib's
`CategoryTheory.Triangulated.TStructure.truncGE` and `natTransTruncGEOfLE` for the standard
t-structure on the derived category.

## References

* [Stacks Project, Tag 0D62](https://stacks.math.columbia.edu/tag/0D62)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

/-- **The tower of truncations from below.**  The inverse system `n ↦ τ_{≥ -n} E` indexed by
`ℕᵒᵖ`, whose transition map `τ_{≥ -(n+1)} E ⟶ τ_{≥ -n} E` is the canonical comparison of
truncations.  This is the system whose derived limit Stacks 0D62 and Stacks 0D6M compare with
`E`. -/
def truncGETower (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (E : DerivedCategory A) : Functor ℕᵒᵖ (DerivedCategory A) :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) fun n ↦
    (DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E

/-- The `n`-th term of the truncation tower is `τ_{≥ -n} E`. -/
@[simp]
theorem truncGETower_obj (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (E : DerivedCategory A) (n : ℕ) :
    (truncGETower A E).obj ⟨n⟩ = (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E :=
  rfl

/-- The successor transition map of the truncation tower is the canonical comparison of
truncations. -/
@[simp]
theorem truncGETower_map_succ (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (E : DerivedCategory A) (n : ℕ) :
    (truncGETower A E).map (homOfLE (Nat.le_succ n)).op =
      (DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

end
