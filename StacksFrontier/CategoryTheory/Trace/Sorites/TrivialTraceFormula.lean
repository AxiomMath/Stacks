module

public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import StacksFrontier.CategoryTheory.Trace.Sorites.Coinvariants
public import StacksCore.Tactic.StacksAttribute

/-!
# The trivial trace formula for a finite group

Let `G` be a finite group, the kernel of a monoid extension `Γ → ℕ`, and let `Λ` be a field
in which the order of `G` is invertible.  The homology of `G` with coefficients in the trivial
module `Λ` is then concentrated in degree zero, where it is `Λ`.  Correspondingly, the sum of
the reciprocals of the orders of the centralizers `Z_γ`, taken over the `G`-conjugacy classes
of the degree-one elements `γ` of `Γ`, equals `1`.

## Main results

* `isZero_groupHomology_trivial_succ`: the homology of `G` with trivial coefficients in a
  field whose characteristic does not divide the order of `G` vanishes in positive degrees.
* `sum_inv_card_centralizer_degreeOne`: the sum of `1 / # Z_γ` over the `G`-conjugacy classes
  of degree-one elements of `Γ` equals `1`.

## Implementation notes

The homological statement is obtained from the computation of group homology as a derived
functor, together with the projectivity of every representation of a finite group over a field
in which its order is invertible.  The degree-zero statement holds for arbitrary trivial
coefficients and is `groupHomology.H0IsoOfIsTrivial`.

The sum over conjugacy classes is expressed, as elsewhere for this extension, through an
arbitrary finite set of representatives of the `G`-conjugacy classes of degree-one elements;
the asserted identity is therefore independent of that choice.  Its proof is the orbit
decomposition of the degree-one elements, which form a single `G`-coset: the class of `γ` has
the index of `Z_γ` many elements, so those indices add up to the order of `G`.

## References

* [Stacks Project, Tag 03UE](https://stacks.math.columbia.edu/tag/03UE)
-/

@[expose] public section

open scoped MonoidAlgebra

open CategoryTheory

universe u v w

namespace Stacks.Trace

/-- The homology of a finite group with coefficients in the trivial module given by a field
in which the order of the group is invertible vanishes in positive degrees. -/
@[stacks 03UE "the vanishing of the homology of `G` in positive degrees"]
theorem isZero_groupHomology_trivial_succ (Λ : Type u) (G : Type u) [Field Λ] [Group G]
    [Finite G] [NeZero (Nat.card G : Λ)] (n : ℕ) :
    Limits.IsZero (groupHomology (Rep.trivial Λ G Λ) (n + 1)) := by
  classical
  exact (Rep.isZero_Tor_succ_of_projective (Rep.trivial Λ G Λ) (Rep.trivial Λ G Λ) n).of_iso
    (groupHomologyIsoTor _ _)

add_to_stacks 03UE "the homology in degree zero" groupHomology.H0IsoOfIsTrivial

/-- The reciprocals of the orders of the centralizers of the degree-one elements of the
extension monoid, summed over their `G`-conjugacy classes, add up to `1` in any field in which
the order of `G` is invertible. -/
@[stacks 03UE "the trivial trace formula"]
theorem sum_inv_card_centralizer_degreeOne {Λ : Type u} {G : Type v} {Γ : Type w} [Field Λ]
    [Group G] [Finite G] [Monoid Γ] [NeZero (Nat.card G : Λ)] (E : MonoidExtensionByNat G Γ)
    (S : Finset Γ) (hS : IsConjugacyClassRepresentatives E (.ofAdd 1) S) :
    ∑ γ ∈ S, (Nat.card (centralizer E.inclusion γ) : Λ)⁻¹ = 1 := by
  classical
  have hG : (Nat.card G : Λ) ≠ 0 := NeZero.ne _
  have hcoset (γ : Γ) : Nat.card (Quotient (QuotientGroup.rightRel
      (centralizer E.inclusion γ))) =
        (centralizer E.inclusion γ).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)
  have hcard : ∑ γ ∈ S, (centralizer E.inclusion γ).index = Nat.card G := by
    rw [← sum_card_centralizer_cosets_degreeOne E S hS]
    exact (Finset.sum_congr rfl fun γ _ => hcoset γ).symm
  have hterm (γ : Γ) : (Nat.card (centralizer E.inclusion γ) : Λ)⁻¹ =
      ((centralizer E.inclusion γ).index : Λ) * (Nat.card G : Λ)⁻¹ := by
    have hmul : ((centralizer E.inclusion γ).index : Λ) *
        (Nat.card (centralizer E.inclusion γ) : Λ) = (Nat.card G : Λ) := by
      rw [← Nat.cast_mul, (centralizer E.inclusion γ).index_mul_card]
    have hi : ((centralizer E.inclusion γ).index : Λ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      exact hG hmul.symm
    rw [← hmul, mul_inv, ← mul_assoc, mul_inv_cancel₀ hi, one_mul]
  rw [Finset.sum_congr rfl fun γ _ => hterm γ, ← Finset.sum_mul, ← Nat.cast_sum, hcard]
  exact mul_inv_cancel₀ hG

end Stacks.Trace
