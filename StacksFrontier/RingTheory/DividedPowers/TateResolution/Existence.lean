module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology

/-! # Tate resolutions

A *Tate resolution* of a commutative `R`-algebra `S` along a surjection `φ` from a polynomial
ring is a divided power differential graded algebra `A` over `R` which is free over `R` in every
degree, whose degree-zero part is the given polynomial ring, which is a graded divided power
polynomial algebra over that polynomial ring, and whose augmentation to `S` is a
quasi-isomorphism when `S` carries the zero differential. This is the output of Tate's
construction as extended by Avramov and Halperin, recorded in Tag 09PN.

## Main definitions

* `DividedPowers.TateResolution.Resolution` — the data of a Tate resolution of `S` extending a
  prescribed surjection `φ : R[xᵢ] → S`.

## Implementation notes

The structure carries its own `Ring`, `Algebra`, `GradedAlgebra`, `IsStrictlyGradedComm`,
`IsDifferentialGradedAlgebra` and `IsCompatibleWithDifferential` data as fields rather than as
instance arguments, because the carrier is produced by the construction and cannot be named in
the statement of the existence theorem.

Quasi-isomorphy of the augmentation is unfolded into the three conditions a reader of Tag 09PN
checks: the augmentation kills the positive-degree part and all boundaries, its degree-zero part
is surjective with exactly the boundaries from degree one as kernel, and the complex is exact in
every positive degree. Freeness of each homogeneous piece is recorded explicitly, as it is what
Tag 09PQ uses to compute Tor.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

/-- A divided-power differential graded algebra resolving `S`, free over `R` in
every degree, whose degree-zero algebra is the specified polynomial presentation
`φ : R[xᵢ] → S`. -/
public structure Resolution
    (R : Type u) (S : Type v) (σ : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S) where
  /-- The carrier of the resolution. -/
  A : Type (max u v w)
  /-- Its ring structure. -/
  ring : Ring A
  /-- Its `R`-algebra structure. -/
  algebra : letI : Ring A := ring; Algebra R A
  /-- Its homogeneous pieces. -/
  grade : letI : Ring A := ring; letI : Algebra R A := algebra;
    ℕ → Submodule R A
  /-- The homogeneous pieces form a grading. -/
  graded : letI : Ring A := ring; letI : Algebra R A := algebra;
    GradedAlgebra grade
  /-- Each homogeneous piece is free over the base ring. -/
  free : letI : Ring A := ring; letI : Algebra R A := algebra;
    ∀ n : ℕ, Module.Free R (grade n)
  /-- The grading is strictly graded commutative. -/
  strict : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    IsStrictlyGradedComm grade
  /-- The divided powers on the positive even part. -/
  gamma : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    letI : IsStrictlyGradedComm grade := strict;
    DividedPowerStructure grade
  /-- The differential. -/
  differential : letI : Ring A := ring; letI : Algebra R A := algebra;
    A →ₗ[R] A
  /-- The differential makes the grading a differential graded algebra. -/
  dga : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    IsDifferentialGradedAlgebra grade differential
  /-- The divided powers are compatible with the differential. -/
  compatible : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    letI : IsStrictlyGradedComm grade := strict;
    IsCompatibleWithDifferential gamma differential
  /-- The prescribed degree-zero polynomial algebra. -/
  coefficient : letI : Ring A := ring; letI : Algebra R A := algebra;
    MvPolynomial σ R →ₐ[R] A
  /-- The augmentation to the resolved algebra. -/
  augmentation : letI : Ring A := ring; letI : Algebra R A := algebra;
    A →ₐ[R] S
  /-- The resolution is a graded divided power polynomial algebra over its degree-zero part. -/
  polynomial : letI : Ring A := ring; letI : Algebra R A := algebra;
    letI : GradedAlgebra grade := graded;
    letI : IsStrictlyGradedComm grade := strict;
    GradedDividedPowerPolynomial grade gamma coefficient
  /-- The augmentation is surjective. -/
  augmentation_surjective : Function.Surjective augmentation
  /-- The degree-zero part is exactly the prescribed polynomial algebra. -/
  degree_zero : ∀ a : A, a ∈ grade 0 ↔ ∃ p : MvPolynomial σ R, coefficient p = a
  /-- The augmentation extends the prescribed surjection. -/
  augmentation_coefficient : augmentation.comp coefficient = φ
  /-- The augmentation kills the positive-degree part. -/
  augmentation_positive : ∀ (n : ℕ) (a : A), 0 < n → a ∈ grade n →
    augmentation a = 0
  /-- The augmentation kills boundaries. -/
  augmentation_differential : ∀ a : A, augmentation (differential a) = 0
  /-- Degree-zero elements killed by the augmentation are boundaries. -/
  exact_zero : ∀ a : A, a ∈ grade 0 → augmentation a = 0 →
    ∃ b : A, b ∈ grade 1 ∧ differential b = a
  /-- The complex is exact in every positive degree. -/
  exact_positive : ∀ (n : ℕ) (a : A), 0 < n → a ∈ grade n →
    differential a = 0 → ∃ b : A, b ∈ grade (n + 1) ∧ differential b = a

end DividedPowers.TateResolution

end
