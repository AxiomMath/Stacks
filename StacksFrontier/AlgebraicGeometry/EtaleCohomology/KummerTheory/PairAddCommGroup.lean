module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairAssociativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairCommutativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairInverse

/-!
# The abelian group of isomorphism classes of pairs

The isomorphism classes of pairs `(L, α)` — an invertible sheaf together with a trivialization
of its `n`-th tensor power — form an abelian group: the addition is the tensor product of pairs,
the zero is the pair given by the structure sheaf with its canonical trivialization, and the
negation is the inverse pair.

## Main results

* `AlgebraicGeometry.instAddCommGroupPairClasses`: the isomorphism classes of pairs on a scheme
  form an abelian group under the tensor product of pairs.
* `AlgebraicGeometry.pairClass_add`, `AlgebraicGeometry.pairClasses_zero` and
  `AlgebraicGeometry.neg_pairClass`: addition of classes of pairs is the tensor product, zero is
  the unit pair at the unit `1`, and negation is the inverse pair.

## References

* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry

/-- **The unit pair at the unit `1` is a unit for the tensor product of isomorphism classes of
pairs.** -/
theorem tensorPairClass_unitPair (S : Scheme.{u}) (n : ℕ) (x : PairClasses S n) :
    tensorPairClass S n x (pairClass (unitPair S n 1)) = x :=
  Quotient.inductionOn x fun P ↦ (pairClass_eq_iff _ _).2 ⟨pairIsoTensorPairUnit P⟩

/-- Addition of isomorphism classes of pairs: the tensor product of the pairs. -/
instance instAddPairClasses (S : Scheme.{u}) (n : ℕ) : Add (PairClasses S n) :=
  ⟨tensorPairClass S n⟩

/-- The zero isomorphism class of pairs: the structure sheaf with its canonical
trivialization. -/
instance instZeroPairClasses (S : Scheme.{u}) (n : ℕ) : Zero (PairClasses S n) :=
  ⟨pairClass (unitPair S n 1)⟩

/-- Negation of isomorphism classes of pairs: the class inverse to a given class under the
tensor product of pairs. -/
instance instNegPairClasses (S : Scheme.{u}) (n : ℕ) : Neg (PairClasses S n) :=
  ⟨fun x ↦ (exists_tensorPairClass_eq_unitPair S n x).choose⟩

/-- **Addition of isomorphism classes of pairs is the tensor product of the pairs.** -/
theorem pairClass_add (S : Scheme.{u}) (n : ℕ) (P Q : TrivializedPower S n) :
    pairClass P + pairClass Q = pairClass (tensorPair S n P Q) := rfl

/-- **The zero of the isomorphism classes of pairs is the unit pair at the unit `1`.** -/
theorem pairClasses_zero (S : Scheme.{u}) (n : ℕ) :
    (0 : PairClasses S n) = pairClass (unitPair S n 1) := rfl

/-- **The isomorphism classes of pairs form an abelian group.** The
addition is the tensor product of pairs, the zero is the structure sheaf with its canonical
trivialization, and the negation is the inverse pair. -/
@[stacks 040Q "the abelian-group structure on the isomorphism classes of pairs (L, alpha), with \
addition the tensor product of pairs, zero the structure sheaf with its canonical \
trivialization, and negation the inverse pair; this is the group the tag identifies with H^1 of \
the roots of unity, but the identification itself is not stated here"]
instance instAddCommGroupPairClasses (S : Scheme.{u}) (n : ℕ) :
    AddCommGroup (PairClasses S n) :=
  { AddGroup.ofLeftAxioms (tensorPairClass_assoc S n)
      (fun x ↦ (tensorPairClass_comm S n _ x).trans (tensorPairClass_unitPair S n x))
      (fun x ↦ (exists_tensorPairClass_eq_unitPair S n x).choose_spec) with
    add_comm := tensorPairClass_comm S n }

/-- **The negation of the class of a pair is the class of its inverse pair.** -/
theorem neg_pairClass (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n) :
    -(pairClass P) = pairClass (inversePair S n P) :=
  neg_eq_of_add_eq_zero_left ((pairClass_eq_iff _ _).2 ⟨pairIsoTensorPairInverse P⟩)

end AlgebraicGeometry

end
