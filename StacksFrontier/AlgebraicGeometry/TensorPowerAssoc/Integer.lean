module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The integer addition law is the nonnegative one, in nonnegative degree

`Stacks.TensorPowers.intTensorPow` is the integer tensor power of an object with a two-sided
tensor inverse, and `Stacks.TensorPowers.TensorInverse.addIso` is its addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, built by a recursion which crosses zero through the inverse
isomorphisms. In nonnegative degree the objects agree with those of
`Stacks.TensorPowers.natTensorPow` by `rfl` — that is
`Stacks.TensorPowers.intTensorPow_natCast` — but the *morphisms* do not: `addIso` carries the
successor comparisons and the degree transports of the integer recursion, each of which is an
identity only after `Category.comp_id`.

This file proves that they do agree, and so transports the coherence of
`Stacks.GradedSections.powAddIso` to the integer-indexed family in nonnegative degree. In a
degree where either exponent is negative, `addIso` genuinely uses
`Stacks.TensorPowers.TensorInverse.predIso` and the inverse isomorphisms, and the coherence of
`powAddIso` says nothing about it.

## Main results

* `Stacks.TensorPowers.TensorInverse.succIso_natCast`: in nonnegative degree the successor
  comparison of the integer powers is the identity, `L ^⊗ (n + 1)` and `L ^⊗ n ⊗ L` being the
  same object.
* `Stacks.TensorPowers.TensorInverse.addNatIso_natCast` and
  `Stacks.TensorPowers.TensorInverse.addIso_natCast`: **the comparison.** In nonnegative degree
  the integer addition law is `Stacks.GradedSections.powAddIso`.
* `Stacks.TensorPowers.TensorInverse.addIso_assoc_natCast`: **the associativity constraint for
  the integer addition law**, in nonnegative degree.
* `Stacks.TensorPowers.TensorInverse.addIso_zero_right_natCast`,
  `Stacks.TensorPowers.TensorInverse.addIso_zero_left_natCast` and
  `Stacks.TensorPowers.TensorInverse.addIso_one_right_natCast`: the two unit constraints and the
  degree-one normalisation, likewise.
* `Stacks.TensorPowers.TensorInverse.addIso_comm_natCast`: the commutativity constraint, under
  `Stacks.GradedSections.HasTrivialSelfBraiding`.

## Implementation notes

**Why `change` and not `simp`.** Every obstruction here is a spelling, not a mathematical step:
`intTensorPow L L' (n : ℤ)` and `natTensorPow L n` are the same term up to unfolding `Nat.cast`
and `Int.add`, and `simp` matches at instances transparency and so sees two different objects.
The inductive step therefore opens with a `change` that rewrites the whole goal — legitimately,
since the two sides are definitionally equal — into the spelling in which the identity morphisms
of the integer recursion are at the objects that `Category.comp_id` needs.

**Indices are written as casts of natural numbers.** The corollaries state degrees as
`((a + b : ℕ) : ℤ)` rather than `(a : ℤ) + (b : ℤ)`, which are the same integer by `rfl` but not
the same term; written the first way, `addIso_natCast` rewrites, and written the second it does
not. This is a statement-level choice made for the benefit of the proofs and of consumers
rewriting in the same direction.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory Stacks.GradedSections

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TensorPowers.intTensorPow

/-- In nonnegative degree the successor comparison of the integer tensor powers is the identity:
`L ^⊗ (n + 1)` and `L ^⊗ n ⊗ L` are then the same object. -/
theorem succIso_natCast {L : C} (h : TensorInverse L) (k : ℕ) :
    h.succIso (k : ℤ) = Iso.refl (natTensorPow L (k + 1)) := rfl

/-- **In nonnegative degree the integer addition law is the nonnegative one.** The two
isomorphisms have definitionally equal types but are not definitionally equal morphisms: the
integer recursion inserts its successor comparisons and degree transports, which are identities
only up to the unit laws of the category. -/
theorem addNatIso_natCast {L : C} (h : TensorInverse L) (a : ℕ) : ∀ k : ℕ,
    h.addNatIso (a : ℤ) k = powAddIso L a k
  | 0 => by
      rw [show h.addNatIso (a : ℤ) 0 = ρ_ (natTensorPow L a) ≪≫ Iso.refl _ from rfl,
        Iso.trans_refl]
      exact (powAddIso_zero_right L a).symm
  | k + 1 => by
      refine Iso.ext ?_
      change (natTensorPow L a ◁ 𝟙 (natTensorPow L (k + 1))) ≫
          (α_ (natTensorPow L a) (natTensorPow L k) L).inv ≫
            ((h.addNatIso (a : ℤ) k).hom ▷ L) ≫
              𝟙 (intTensorPow L h.inv ((a : ℤ) + (k : ℤ)) ⊗ L) ≫
                𝟙 (intTensorPow L h.inv ((a : ℤ) + (k : ℤ)) ⊗ L) =
        (α_ (natTensorPow L a) (natTensorPow L k) L).inv ≫ ((powAddIso L a k).hom ▷ L)
      rw [whiskerLeft_id, Category.id_comp, Category.comp_id, Category.comp_id,
        addNatIso_natCast h a k]

/-- **The comparison, for `Stacks.TensorPowers.TensorInverse.addIso` itself.** In nonnegative
degree the integer addition law is `Stacks.GradedSections.powAddIso`, so every coherence law
proved for the latter is a coherence law for the former. -/
theorem addIso_natCast {L : C} (h : TensorInverse L) (a k : ℕ) :
    h.addIso (a : ℤ) (k : ℤ) = powAddIso L a k := addNatIso_natCast h a k

/-- The right unit constraint for the integer addition law, in nonnegative degree. -/
theorem addIso_zero_right_natCast {L : C} (h : TensorInverse L) (a : ℕ) :
    h.addIso (a : ℤ) ((0 : ℕ) : ℤ) = ρ_ (natTensorPow L a) := by
  rw [addIso_natCast, powAddIso_zero_right]

/-- The left unit constraint for the integer addition law, in nonnegative degree. -/
theorem addIso_zero_left_natCast {L : C} (h : TensorInverse L) (k : ℕ) :
    h.addIso ((0 : ℕ) : ℤ) (k : ℤ) ≪≫ powCongrIso L (Nat.zero_add k) =
      λ_ (natTensorPow L k) := by
  rw [addIso_natCast, powAddIso_zero_left]

/-- **The degree-one normalisation for the integer addition law.** Multiplication by the first
power is the identification `L ^⊗ 1 ≅ L` whiskered into `L ^⊗ n`, followed by the successor step
of the iteration, which in nonnegative degree is the identity. -/
theorem addIso_one_right_natCast {L : C} (h : TensorInverse L) (a : ℕ) :
    h.addIso (a : ℤ) ((1 : ℕ) : ℤ) = whiskerLeftIso (natTensorPow L a) (λ_ L) := by
  rw [addIso_natCast, powAddIso_one_right]

/-- **The associativity constraint for the integer addition law**, in nonnegative degree. This
is the constraint Stacks Tag 01CU asserts for the canonical multiplication with its formulation
omitted, for the integer-indexed family and against the associator of `C`. -/
@[sga "5 VI 1.3.4" "partial"]
theorem addIso_assoc_natCast {L : C} (h : TensorInverse L) (a b c : ℕ) :
    whiskerRightIso (h.addIso (a : ℤ) (b : ℤ)) (natTensorPow L c) ≪≫
        h.addIso ((a + b : ℕ) : ℤ) (c : ℤ) =
      α_ (natTensorPow L a) (natTensorPow L b) (natTensorPow L c) ≪≫
        whiskerLeftIso (natTensorPow L a) (h.addIso (b : ℤ) (c : ℤ)) ≪≫
          h.addIso (a : ℤ) ((b + c : ℕ) : ℤ) ≪≫ powCongrIso L (Nat.add_assoc a b c).symm := by
  rw [addIso_natCast, addIso_natCast, addIso_natCast, addIso_natCast]
  exact powAddIso_assoc L a b c

/-- **The commutativity constraint for the integer addition law**, in nonnegative degree, under
the hypothesis that the self-braiding of `L` is trivial. -/
theorem addIso_comm_natCast [BraidedCategory C] {L : C} (h : TensorInverse L)
    [HasTrivialSelfBraiding L] (a b : ℕ) :
    β_ (natTensorPow L a) (natTensorPow L b) ≪≫ h.addIso (b : ℤ) (a : ℤ) =
      h.addIso (a : ℤ) (b : ℤ) ≪≫ powCongrIso L (Nat.add_comm a b) := by
  rw [addIso_natCast, addIso_natCast]
  exact powAddIso_comm L a b

end Stacks.TensorPowers.TensorInverse

end
