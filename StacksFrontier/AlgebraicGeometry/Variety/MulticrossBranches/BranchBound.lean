module

public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaBranches.LowerBound
public import StacksFrontier.RingTheory.Branches.Completion
import all StacksFrontier.RingTheory.Branches.Completion

/-!
# The delta invariant bounds the number of branches

Over a separably closed residue field the ordinary and the geometric branch counts agree, so the
lower bound for the delta invariant in terms of geometric branches becomes a lower bound in terms
of branches.

## Main results

* `numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed` identifies the two branch counts
  of a local ring with separably closed residue field.
* `Ring.deltaInvariant_ge_numberOfBranches_sub_one` is the resulting bound for a reduced
  one-dimensional Nagata local algebra over a separably closed field.

## Implementation notes

A local ring whose residue field is separably closed is its own separable closure, so a strict
henselization is a henselization; the uniqueness of the henselization then gives a ring
isomorphism between the two chosen representatives, and the minimal-prime count is invariant
under it.  Both of those inputs are reused from `StacksFrontier.RingTheory.Branches.Completion`,
where they are private, rather than reproved.

The hypothesis on the residue field of the algebra is given as a `k`-algebra equivalence with
the separably closed base field, from which separable closedness of the residue field is
transported along the underlying ring isomorphism.

## References

* [Stacks Project, Tag 0C1V](https://stacks.math.columbia.edu/tag/0C1V)
-/

@[expose] public section

open IsLocalRing

universe u v

/-- For a local ring with separably closed residue field the number of branches equals the
number of geometric branches: the strict henselization is a henselization. -/
theorem numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed
    (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] :
    numberOfBranchesOfLocalRing A = numberOfGeometricBranchesOfLocalRing A := by
  let D := henselizationData A
  let H := D.carrier
  let : CommRing H := (henselizationData A).commRing
  let : IsLocalRing H := (henselizationData A).isLocalRing
  let : Algebra A H := (henselizationData A).algebra
  let : IsHenselization A (ResidueField A) H :=
    (henselizationData A).isHenselization
  let Dsh := strictHenselizationData A
  let S := Dsh.carrier
  let : CommRing S := (strictHenselizationData A).commRing
  let : IsLocalRing S := (strictHenselizationData A).isLocalRing
  let : Algebra A S := (strictHenselizationData A).algebra
  let : IsHenselization A (SeparableClosure (ResidueField A)) S :=
    (strictHenselizationData A).isHenselization
  let : IsSepClosure (ResidueField A) (ResidueField A) := inferInstance
  let e : SeparableClosure (ResidueField A) ≃ₐ[ResidueField A] ResidueField A :=
    IsSepClosure.equiv (ResidueField A) (SeparableClosure (ResidueField A)) (ResidueField A)
  obtain ⟨f⟩ := exists_algEquiv_of_isHenselization A H S
    (ResidueField A) (SeparableClosure (ResidueField A)) e.symm
  change (minimalPrimes H).encard = (minimalPrimes S).encard
  exact encard_minimalPrimes_eq_of_ringEquiv f.toRingEquiv

namespace Ring

/-- **The delta invariant of a reduced one-dimensional Nagata local algebra over a separably
closed field is at least the number of branches minus one.** -/
@[stacks 0C1V "delta invariant bound"]
theorem deltaInvariant_ge_numberOfBranches_sub_one
    (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsReduced A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 1) (_hres : Nonempty (ResidueField A ≃ₐ[k] k)) :
    numberOfBranchesOfLocalRing A - 1 ≤ Ring.deltaInvariant A := by
  let : IsSepClosed (ResidueField A) :=
    IsSepClosed.of_ringEquiv (Classical.choice _hres).toRingEquiv
  rw [numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed A]
  exact Ring.deltaInvariant_ge_numberOfGeometricBranches_sub_one A hNagata hdim

end Ring

end
