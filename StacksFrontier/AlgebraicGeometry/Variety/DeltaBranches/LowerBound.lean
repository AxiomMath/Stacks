module

public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaBranches.LowerBoundStrictlyHenselian
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.BaseChangeDelta
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Henselization
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
import all StacksFrontier.RingTheory.Branches.Completion

/-!
# The delta invariant bounds the number of geometric branches

For a reduced one-dimensional Nagata local ring, the delta invariant is at least one less than
the number of geometric branches. Both invariants take values in `ℕ∞`, so the subtraction in the
bound is truncated subtraction in the extended natural numbers, and the geometric branch count is
the one defined using a strict henselization.

## Main results

* `Ring.deltaInvariant_ge_numberOfGeometricBranches_sub_one` gives the lower bound on the delta
  invariant in terms of the number of geometric branches.
* `Ring.numberOfGeometricBranchesOfLocalRing_eq_encard_minimalPrimes_of_strictlyHenselian`: for a
  strictly henselian local ring the number of geometric branches is the number of minimal primes.

## References

* [Stacks Project, Tag 0C43](https://stacks.math.columbia.edu/tag/0C43)
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace Ring

/-- For a strictly henselian local ring the number of geometric branches is the number of its
own minimal primes. -/
public theorem numberOfGeometricBranchesOfLocalRing_eq_encard_minimalPrimes_of_strictlyHenselian
    (S : Type u) [CommRing S] [StrictlyHenselianLocalRing S] :
    numberOfGeometricBranchesOfLocalRing S = (minimalPrimes S).encard := by
  let L := SeparableClosure (ResidueField S)
  let D := strictHenselizationData S
  let T := D.carrier
  let : CommRing T := D.commRing
  let : IsLocalRing T := D.isLocalRing
  let : Algebra S T := D.algebra
  let : IsHenselization S L T := D.isHenselization
  let : IsHenselization S (ResidueField S) S :=
    .of_ind_etale inferInstance
      ((CommAlgCat.etale S).le_ind _ (show Algebra.Etale S S from inferInstance))
      ⟨RingEquiv.refl _, fun _ ↦ rfl⟩
  let e : L ≃ₐ[ResidueField S] ResidueField S :=
    IsSepClosure.equiv (ResidueField S) L (ResidueField S)
  obtain ⟨f⟩ := exists_algEquiv_of_isHenselization S S T (ResidueField S) L e.symm
  change (minimalPrimes T).encard = (minimalPrimes S).encard
  exact (encard_minimalPrimes_eq_of_ringEquiv f.toRingEquiv).symm

/-- The delta invariant of a reduced one-dimensional Nagata local ring is at least the number
of its geometric branches minus one. -/
@[stacks 0C43]
public lemma deltaInvariant_ge_numberOfGeometricBranches_sub_one
    (A : Type*) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    Ring.deltaInvariant A ≥
      numberOfGeometricBranchesOfLocalRing A - 1 := by
  let D := strictHenselizationData A
  let Ash := D.carrier
  let : CommRing Ash := D.commRing
  let : IsLocalRing Ash := D.isLocalRing
  let : Algebra A Ash := D.algebra
  let : IsHenselization A (SeparableClosure (ResidueField A)) Ash := D.isHenselization
  let : IsReduced Ash :=
    strictHenselization_isReduced
      (A := A) (Ash := Ash) (SeparableClosure (ResidueField A))
  have hNagataAsh : IsNagataRing Ash :=
    strictHenselization_isNagataRing
      (A := A) (Ash := Ash) (SeparableClosure (ResidueField A)) hA
  have hdelta := Stacks.Curves.deltaInvariant_strictHenselization
    A Ash (SeparableClosure (ResidueField A)) hA hdim
  obtain ⟨e, _⟩ := D.isHenselization.exists_residueFieldEquiv
  let : IsSepClosed (SeparableClosure (ResidueField A)) :=
    IsSepClosure.sep_closed (ResidueField A)
  let : HenselianLocalRing Ash := D.isHenselization.henselian
  let : IsSepClosed (ResidueField Ash) := IsSepClosed.of_ringEquiv e.symm
  let : StrictlyHenselianLocalRing Ash := {}
  change Ring.deltaInvariant A ≥ (minimalPrimes Ash).encard - 1
  rw [← hdelta]
  simpa only [numberOfGeometricBranchesOfLocalRing_eq_encard_minimalPrimes_of_strictlyHenselian Ash]
    using deltaInvariant_ge_numberOfGeometricBranches_sub_one_of_strictlyHenselian
      Ash hNagataAsh

end Ring
