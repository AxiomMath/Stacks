module

public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.FiniteCohomologicalDimension

/-!
# The cohomological dimension of a finitely generated ideal

Let `I` be a finitely generated ideal of a commutative ring `A` and `Y = V(I)` its zero locus
in `X = Spec A`. The local cohomology `H^i_Y(A)` vanishes for `i` larger than the number of
generators of `I`, so the set of integers `d ≥ -1` above which it vanishes is a nonempty set of
integers bounded below by `-1`. Its least element is the *cohomological dimension* `cd(A, I)`
of `I` in `A`.

## Main definitions

* `Stacks.LocalCohomology.IsLocalCohomologyBound` — the property of an integer `d ≥ -1` that
  `H^i_Y(A) = 0` for every `i > d`.
* `Stacks.LocalCohomology.cohomologicalDimension` — the least such `d`.

## Main results

* `Stacks.LocalCohomology.exists_localCohomologyBound` — a vanishing bound exists, which is
  what makes the infimum defining the cohomological dimension an attained minimum.
* `Stacks.LocalCohomology.cohomologicalDimension_le`,
  `Stacks.LocalCohomology.isLocalCohomologyBound_cohomologicalDimension` and
  `Stacks.LocalCohomology.cohomologicalDimension_eq_iff` — the cohomological dimension is the
  least vanishing bound, and that property characterizes it.

## References

* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- A degree `d ≥ -1` above which the local cohomology of `A` supported on `V(I)` vanishes.
This is the first of the equivalent conditions of Stacks 0DX7. -/
abbrev IsLocalCohomologyBound
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) : Prop :=
  (-1 : ℤ) ≤ d ∧
    ∀ i : ℤ, d < i → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i)

/-- **Stacks Project, Tag 0DX8.** The cohomological dimension of a finitely generated ideal is
the least integer `d ≥ -1` above which its local cohomology vanishes. -/
@[stacks 0DX8 "the least integer"]
def cohomologicalDimension
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) : ℤ :=
  sInf {d : ℤ | IsLocalCohomologyBound A I hI d}

/-- Finite generation gives a finite upper bound on the degrees in which local cohomology is
nonzero; equivalently, the set defining the cohomological dimension is nonempty. -/
@[stacks 0DX8 "existence of a vanishing bound"]
theorem exists_localCohomologyBound
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    ∃ d : ℤ, IsLocalCohomologyBound A I hI d :=
  exists_isZero_homology_localCohomologyFunctor_singleFunctor.{u, u} I hI (ModuleCat.of A A)

/-- The cohomological dimension is at most any vanishing bound. -/
theorem cohomologicalDimension_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (d : ℤ) (hd : IsLocalCohomologyBound A I hI d) :
    cohomologicalDimension A I hI ≤ d :=
  csInf_le ⟨-1, fun _ he ↦ he.1⟩ hd

/-- The cohomological dimension itself is a vanishing bound. -/
theorem isLocalCohomologyBound_cohomologicalDimension
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    IsLocalCohomologyBound A I hI (cohomologicalDimension A I hI) :=
  Int.csInf_mem (exists_localCohomologyBound A I hI) ⟨-1, fun _ he ↦ he.1⟩

/-- A degree is the cohomological dimension precisely when it is a least vanishing bound. -/
theorem cohomologicalDimension_eq_iff
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) :
    cohomologicalDimension A I hI = d ↔
      IsLocalCohomologyBound A I hI d ∧
        ∀ e : ℤ, IsLocalCohomologyBound A I hI e → d ≤ e := by
  refine ⟨?_, fun h ↦ le_antisymm (cohomologicalDimension_le A I hI d h.1)
    (le_csInf (exists_localCohomologyBound A I hI) h.2)⟩
  rintro rfl
  exact ⟨isLocalCohomologyBound_cohomologicalDimension A I hI, cohomologicalDimension_le A I hI⟩

end Stacks.LocalCohomology
