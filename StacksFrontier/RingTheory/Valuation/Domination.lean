module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Domination, valuation rings, and centering

The three definitions of Stacks tag 00I9, in terms of the Mathlib API for local subrings
of a field.

* **(1) Domination.** For two local subrings `A`, `B` of a field `K`, `B` dominates `A`
  when `A ⊆ B` and `𝔪_A = A ∩ 𝔪_B`. In Mathlib this is exactly the partial order
  `A ≤ B` on `LocalSubring K`, the inclusion `A → B` being a local ring homomorphism.
  `dominates_iff` unfolds that order to the explicit maximal-ideal condition.
* **(2) Valuation ring.** A local domain `A` is a valuation ring when it is maximal for
  the domination order among the local subrings of its fraction field. This is `IsMax`
  of the image of `A` inside `FractionRing A`, recorded as `IsValuationRing`.
* **(3) Centered.** A valuation ring `A` with fraction field `K` is centered on a
  subring `R ⊆ K` when `R ⊆ A`, recorded as `IsCenteredOn`.

Mathlib already attaches `@[stacks 00I9]` to the domination `PartialOrder` instance on
`LocalSubring`; the content is restated here one enumerated item at a time.

Tag 00IA — every local subring of a field is dominated by a valuation subring of that
field — is Mathlib's `LocalSubring.exists_le_valuationSubring`, which already carries
`@[stacks 00IA]`; only its EGA cross-reference is recorded below.
-/

@[expose] public section

open IsLocalRing

variable {K : Type*} [Field K]

/-- Part (1). For local subrings `A`, `B` of a field `K`, the domination order
`A ≤ B` of `LocalSubring K` holds iff `A ⊆ B` (as subrings) and, for every
`a ∈ A`, the element `a` lies in the maximal ideal of `A` exactly when its image
in `B` lies in the maximal ideal of `B`. The latter is the literal Stacks
condition `𝔪_A = A ∩ 𝔪_B`. -/
@[stacks 00I9 "(1)", ega "I 8.1.1" "(i) ⇔ (ii)"]
theorem dominates_iff {A B : LocalSubring K} :
    A ≤ B ↔ ∃ h : A.toSubring ≤ B.toSubring,
      ∀ a : A.toSubring,
        a ∈ maximalIdeal A.toSubring ↔
          Subring.inclusion h a ∈ maximalIdeal B.toSubring := by
  rw [LocalSubring.le_def]
  refine exists_congr fun h => ⟨fun _ a => ?_, fun hcond => ⟨fun a hu => ?_⟩⟩
  · simpa only [mem_maximalIdeal, mem_nonunits_iff, not_iff_not] using
      (isUnit_map_iff (Subring.inclusion h) a).symm
  · simp only [mem_maximalIdeal, mem_nonunits_iff, not_iff_not] at hcond
    exact (hcond a).mpr hu

/-- Part (2). A local domain `A` is a *valuation ring* when, viewed inside its
fraction field, it is maximal for the domination order among the local subrings
of `FractionRing A`. -/
@[stacks 00I9 "(2)", ega "II 7.1.1" "definition"]
def IsValuationRing (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] : Prop :=
  IsMax (LocalSubring.range (algebraMap A (FractionRing A)))

/-- A valuation ring in Mathlib's sense is maximal for the domination order among the local
subrings of its fraction field, which is the Stacks predicate `IsValuationRing`. -/
@[ega "II 7.1.1" "partial"]
theorem isValuationRing_of_valuationRing (A : Type*) [CommRing A] [IsDomain A]
    [ValuationRing A] : IsValuationRing A := by
  change IsMax (LocalSubring.range (algebraMap A (FractionRing A)))
  let w := ValuationRing.valuation A (FractionRing A)
  apply (LocalSubring.isMax_iff).2
  refine ⟨w.valuationSubring, ?_⟩
  apply LocalSubring.toSubring_injective
  change w.valuationSubring.toSubring = (algebraMap A (FractionRing A)).range
  rw [← ValuationRing.range_algebraMap_eq A (FractionRing A)]
  rfl

/-- Part (3). A valuation ring `A` with fraction field `K`, represented as a
`ValuationSubring K`, is *centered* on a subring `R ⊆ K` when `R ⊆ A`. -/
@[stacks 00I9 "(3)"]
def IsCenteredOn (A : ValuationSubring K) (R : Subring K) : Prop :=
  R ≤ A.toSubring

end

@[expose] public section

-- The former @[stacks 00IA, ega] theorem is the Mathlib theorem, which Mathlib itself
-- tags with @[stacks 00IA]; only the EGA reference has to be recorded here.
add_to_ega "II 7.1.2" "existence"
  LocalSubring.exists_le_valuationSubring

end
