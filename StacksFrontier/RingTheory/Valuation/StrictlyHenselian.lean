module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.Criteria

import StacksCore.Tactic.StacksAttribute

/-!
# Valuation rings with algebraically closed fraction field are strictly henselian

A valuation ring is a normal domain, so a valuation ring whose fraction field is separably
closed is strictly henselian. When the fraction field is in fact algebraically closed, the
residue field is algebraically closed as well: a monic polynomial over the residue field lifts
to a monic polynomial over the valuation ring, a root of the lift in the fraction field is
integral over the ring and therefore lies in it, and its residue is a root of the original
polynomial.

Combining this with the existence of a dominating valuation subring gives the ring-theoretic
input to the construction of specialization maps of fundamental groups out of a valuation ring:
every local subring of an algebraically closed field `K` is dominated by a valuation subring of
`K` which is strictly henselian and has algebraically closed residue field.

## Main results

* `IsLocalRing.isAlgClosed_residueField_of_isIntegrallyClosed` — a normal local domain whose
  fraction field is algebraically closed has algebraically closed residue field.
* `strictlyHenselianLocalRing_of_isIntegrallyClosed` — a normal local domain whose fraction
  field is separably closed is strictly henselian, in the form of the class
  `StrictlyHenselianLocalRing`.
* `LocalSubring.exists_le_valuationSubring_strictlyHenselian` — every local subring of an
  algebraically closed field is dominated by a strictly henselian valuation subring with
  algebraically closed residue field.
* `IsLocalRing.exists_factor_valuationRing_strictlyHenselian` — the same, in the form a
  homomorphism from a local ring to an algebraically closed field factors through such a
  valuation subring by a local homomorphism.

## Implementation notes

`IsLocalRing.isAlgClosed_residueField_of_normal` (Stacks 0BSP) proves the stronger statement
that a *separably* closed fraction field already forces the residue field at a nonzero prime to
be algebraically closed. It is not used here: it is stated for `Ideal.ResidueField` of a nonzero
prime rather than for `IsLocalRing.ResidueField`, and it excludes the case of a valuation ring
which is a field, so applying it would cost both a transport between the two residue fields and
a case split, where the hypothesis actually available in the specialization-map situation — an
algebraically closed fraction field — admits the three-line argument above.

The dominating valuation subring is Mathlib's `LocalSubring.exists_le_valuationSubring`
(Stacks 00IA), and normality of a valuation ring is Mathlib's `IsIntegrallyClosed` instance on
`ValuationSubring` (Stacks 00IC, recorded as `valuationRing_isIntegrallyClosed` in
`StacksFrontier.RingTheory.Valuation.Criteria`). Strict henselianity comes from
`normal_local_domain_sepClosed_fractionField_isStrictlyHenselian` (Stacks 0BSQ).

## References

* [Stacks Project, Tag 00IA](https://stacks.math.columbia.edu/tag/00IA)
* [Stacks Project, Tag 00IC](https://stacks.math.columbia.edu/tag/00IC)
* [Stacks Project, Tag 0BSQ](https://stacks.math.columbia.edu/tag/0BSQ)
-/

@[expose] public section

open IsLocalRing Polynomial

/-- A normal local domain whose fraction field is algebraically closed has algebraically closed
residue field: a monic polynomial over the residue field lifts to a monic polynomial over the
ring, which has a root in the fraction field; the root is integral over the ring, hence lies in
it, and its residue is a root of the original polynomial. -/
theorem IsLocalRing.isAlgClosed_residueField_of_isIntegrallyClosed
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K] :
    IsAlgClosed (ResidueField R) := by
  refine IsAlgClosed.of_exists_root _ fun p hp_monic hp_irr ↦ ?_
  obtain ⟨g₀, hg₀⟩ := Polynomial.map_surjective (residue R) residue_surjective p
  obtain ⟨g, hg_map, -, hg_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic ((Polynomial.mem_lifts p).mpr ⟨g₀, hg₀⟩)
      hp_monic
  have hdeg : (g.map (algebraMap R K)).degree ≠ 0 := by
    rw [hg_monic.degree_map (algebraMap R K), ← hg_monic.degree_map (residue R), hg_map]
    exact (degree_pos_of_irreducible hp_irr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (k := K) (g.map (algebraMap R K)) hdeg
  have hz' : Polynomial.aeval z g = 0 := by
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
  obtain ⟨c, hc⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral (⟨g, hg_monic, hz'⟩ : IsIntegral R z)
  have hgc : g.eval c = 0 := by
    apply IsFractionRing.injective R K
    rwa [map_zero, (Polynomial.eval₂_at_apply (algebraMap R K) c).symm, ← Polynomial.eval_map, hc]
  refine ⟨residue R c, ?_⟩
  rw [← hg_map, Polynomial.eval_map, Polynomial.eval₂_at_apply, hgc, map_zero]

/-- A normal local domain whose fraction field is separably closed is strictly henselian.
This is `normal_local_domain_sepClosed_fractionField_isStrictlyHenselian` (Stacks 0BSQ)
packaged as the class `StrictlyHenselianLocalRing` (Stacks 03QK). -/
theorem strictlyHenselianLocalRing_of_isIntegrallyClosed
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    StrictlyHenselianLocalRing R :=
  have h := normal_local_domain_sepClosed_fractionField_isStrictlyHenselian R K
  { __ := h.1, __ := h.2 }

/-- Every local subring of an algebraically closed field `K` is dominated by a valuation subring
of `K` which is strictly henselian and whose residue field is algebraically closed. The fraction
field of the valuation subring is `K` itself, by
`ValuationSubring.instIsFractionRingSubtypeMem`. -/
theorem LocalSubring.exists_le_valuationSubring_strictlyHenselian
    {K : Type*} [Field K] [IsAlgClosed K] (A : LocalSubring K) :
    ∃ B : ValuationSubring K, A ≤ B.toLocalSubring ∧ StrictlyHenselianLocalRing B ∧
      IsAlgClosed (IsLocalRing.ResidueField B) := by
  obtain ⟨B, hB⟩ := A.exists_le_valuationSubring
  exact ⟨B, hB, strictlyHenselianLocalRing_of_isIntegrallyClosed B K,
    IsLocalRing.isAlgClosed_residueField_of_isIntegrallyClosed B K⟩

/-- Every ring homomorphism from a local ring `R` to an algebraically closed field `K` factors
through a valuation subring `A` of `K` which is strictly henselian and has algebraically closed
residue field, by a *local* homomorphism `R → A`. This is
`IsLocalRing.exists_factor_valuationRing` (Stacks 00IA) with the two extra properties of `A`
supplied by `strictlyHenselianLocalRing_of_isIntegrallyClosed` and
`IsLocalRing.isAlgClosed_residueField_of_isIntegrallyClosed`. -/
theorem IsLocalRing.exists_factor_valuationRing_strictlyHenselian
    {R : Type*} [CommRing R] [IsLocalRing R] {K : Type*} [Field K] [IsAlgClosed K]
    (f : R →+* K) :
    ∃ (A : ValuationSubring K) (h : ∀ x, f x ∈ A.toSubring),
      IsLocalHom (f.codRestrict A.toSubring h) ∧ StrictlyHenselianLocalRing A ∧
        IsAlgClosed (IsLocalRing.ResidueField A) := by
  obtain ⟨A, h, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  exact ⟨A, h, hlocal, strictlyHenselianLocalRing_of_isIntegrallyClosed A K,
    IsLocalRing.isAlgClosed_residueField_of_isIntegrallyClosed A K⟩

end
