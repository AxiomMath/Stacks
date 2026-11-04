module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Wedges of local rings

A local ring is a wedge of a nonempty finite family of local rings when, after identifying
their residue fields, it is isomorphic to the subring of the product whose entries have the
same residue.

## Main definitions

* `IsLocalRing.wedgeSubring`: the subring of tuples having a common residue.
* `IsLocalRing.IsWedge`: a local ring is isomorphic to such a subring.

## Main results

* `IsLocalRing.mem_wedgeSubring`: membership in the common-residue subring.

## References

* [Stacks Project, Tag 0C41](https://stacks.math.columbia.edu/tag/0C41)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace IsLocalRing

/-- The subring of a finite product of local rings consisting of tuples whose residues agree,
after chosen identifications of the residue fields with that of the last factor. -/
public def wedgeSubring {n : ℕ} (B : Fin (n + 1) → Type v)
    [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    (e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+* ResidueField (B (Fin.last n))) :
    Subring (∀ i, B i) where
  carrier := {a | ∀ i : Fin n,
    e i (residue (B i.castSucc) (a i.castSucc)) = residue (B (Fin.last n)) (a (Fin.last n))}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by intro a b ha hb i; simp only [Pi.add_apply, map_add, ha i, hb i]
  mul_mem' := by intro a b ha hb i; simp only [Pi.mul_apply, map_mul, ha i, hb i]
  neg_mem' := by intro a ha i; simp only [Pi.neg_apply, map_neg, ha i]

/-- Membership in `wedgeSubring` means precisely that all components have the same residue. -/
@[simp]
public theorem mem_wedgeSubring {n : ℕ} (B : Fin (n + 1) → Type v)
    [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    (e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+* ResidueField (B (Fin.last n)))
    (a : ∀ i, B i) :
    a ∈ wedgeSubring B e ↔
      ∀ i : Fin n,
        e i (residue (B i.castSucc) (a i.castSucc)) =
          residue (B (Fin.last n)) (a (Fin.last n)) :=
  Iff.rfl

/-- A local ring `A` is a wedge of the nonempty finite family
`B` if their residue fields can be identified and `A` is isomorphic to the subring of the
product consisting of tuples with a common residue. -/
@[stacks 0C41]
public def IsWedge (A : Type u) {n : ℕ} (B : Fin (n + 1) → Type v)
    [CommRing A] [IsLocalRing A] [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] : Prop :=
  ∃ e : ∀ i : Fin n, ResidueField (B i.castSucc) ≃+* ResidueField (B (Fin.last n)),
    Nonempty (A ≃+* wedgeSubring B e)

end IsLocalRing
