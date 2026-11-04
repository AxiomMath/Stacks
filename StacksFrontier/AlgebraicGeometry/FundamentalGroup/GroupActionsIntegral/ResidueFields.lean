module

public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Henselian.Criteria
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Residue fields of a normal domain with separably closed fraction field

Let `A` be a normal domain with separably closed fraction field. Then `A` is strictly henselian
whenever it is local, and the residue field at every nonzero prime ideal of `A` is algebraically
closed.

## Main results

* `IsLocalRing.isAlgClosed_residueField_of_normal`: the residue field at a nonzero prime of a
  normal domain with separably closed fraction field is algebraically closed.
* `normal_local_domain_sepClosed_fractionField_isStrictlyHenselian`: such a normal local domain
  is henselian and has separably closed residue field.

## Implementation notes

The fraction field is represented by an arbitrary field `K` satisfying `IsFractionRing A K`,
rather than by a fixed construction. Normality is expressed by `IsIntegrallyClosed` as in Stacks
Project Tag 0309. Strict henselianity is expressed as the conjunction of the henselian property
and separable closedness of the residue field.

## References

* [Stacks Project, Tag 0BSP](https://stacks.math.columbia.edu/tag/0BSP)
* [Stacks Project, Tag 0BSQ](https://stacks.math.columbia.edu/tag/0BSQ)
-/

@[expose] public section

add_to_stacks 0BSQ normal_local_domain_sepClosed_fractionField_isStrictlyHenselian

namespace IsLocalRing

open Polynomial

private lemma residueField_perfect
    (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    [IsIntegrallyClosed R]
    (hm : ∃ t : R, t ∈ IsLocalRing.maximalIdeal R ∧ t ≠ 0) :
    PerfectField (IsLocalRing.ResidueField R) := by
  let F := IsLocalRing.ResidueField R
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let : ExpChar F q := hq
  rcases expChar_is_prime_or_one F q with hprime | rfl
  · let : Fact q.Prime := ⟨hprime⟩
    let : PerfectRing F q := PerfectRing.ofSurjective F q (by
      intro a
      obtain ⟨t, ht, htn⟩ := hm
      obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective a
      have htK : algebraMap R K t ≠ 0 :=
        fun h => htn ((IsFractionRing.injective R K) (by simpa using h))
      let f : K[X] := X ^ q + C (algebraMap R K t) * X - C (algebraMap R K b)
      have hfd : f.derivative ≠ 0 := by
        rw [show f.derivative = C (q : K) * X ^ (q - 1) + C (algebraMap R K t) by
          simp [f, Polynomial.derivative_add, Polynomial.derivative_sub,
            Polynomial.derivative_X_pow, Polynomial.derivative_mul]]
        by_cases hqK : (q : K) = 0
        · simp [hqK, htK]
        · intro h
          have hh := congr_arg (fun g : K[X] => g.coeff (q - 1)) h
          have hq1 : q - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hprime.two_le
          simp [coeff_add, coeff_C, hq1, hqK] at hh
      obtain ⟨g, hgirr, hgdiv, hgsep⟩ := exists_sep_irred_factor_of_deriv_ne f hfd
      have hgdeg : g.degree ≠ 0 := (degree_pos_of_irreducible hgirr).ne'
      obtain ⟨z, hz⟩ := (IsSepClosed.splits_of_separable g hgsep).exists_eval_eq_zero hgdeg
      have hz : f.IsRoot z := Polynomial.IsRoot.dvd hz hgdiv
      have hzint : IsIntegral R z := by
        refine ⟨X ^ q + C t * X - C b, ?_, ?_⟩
        · convert monic_X_pow_add (p := C t * X - C b) (n := q) (by
            calc
              degree (C t * X - C b) ≤ max (degree (C t * X)) (degree (C b)) := degree_sub_le _ _
              _ ≤ 1 := max_le (degree_C_mul_X_le _ |>.trans (by norm_num))
                (degree_C_le (a := b) |>.trans (by norm_num))
              _ < q := by exact_mod_cast hprime.two_le) using 1
          · ring
        · simpa [Polynomial.aeval_def, f] using hz
      obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzint
      refine ⟨IsLocalRing.residue R c, ?_⟩
      have hroot : c ^ q + t * c - b = 0 := by
        apply (IsFractionRing.injective R K); simpa [f, hc] using hz
      rw [← hb]; change (IsLocalRing.residue R c) ^ q = IsLocalRing.residue R b
      apply sub_eq_zero.mp
      simpa [frobenius, (IsLocalRing.residue_eq_zero_iff t).mpr ht] using
        congrArg (IsLocalRing.residue R) hroot)
    exact PerfectRing.toPerfectField F q
  · let : CharZero F := charZero_of_expChar_one' F
    exact PerfectField.ofCharZero

/-- The residue field at a nonzero prime ideal of a normal domain whose fraction field is
separably closed is algebraically closed. -/
@[stacks 0BSP]
public theorem isAlgClosed_residueField_of_normal
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [IsSepClosed K]
    (hA : IsIntegrallyClosed A) (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    IsAlgClosed p.ResidueField := by
  have hnorm : IsIntegrallyClosed A := hA
  let : IsIntegrallyClosed A := hnorm
  have hM : p.primeCompl ≤ nonZeroDivisors A := fun x hx =>
    mem_nonZeroDivisors_iff_ne_zero.mpr (fun h => hx (h ▸ p.zero_mem))
  have hmap : p.primeCompl ≤ Submonoid.comap (RingHom.id A) (nonZeroDivisors A) := hM
  let : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (R := A) (Localization.AtPrime p) p.primeCompl hM
  let g : Localization.AtPrime p →+* K := IsLocalization.map K
    (T := nonZeroDivisors A) (RingHom.id A) hmap
  let : Algebra (Localization.AtPrime p) K := g.toAlgebra
  let : IsScalarTower A (Localization.AtPrime p) K :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (IsLocalization.map_eq (T := nonZeroDivisors A) hmap x).symm)
  let : IsFractionRing (Localization.AtPrime p) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      p.primeCompl (Localization.AtPrime p) K
  let : IsSepClosed p.ResidueField := residue_sepClosed_half (Localization.AtPrime p) K
  let : PerfectField p.ResidueField := by
    apply residueField_perfect (Localization.AtPrime p) K
    obtain ⟨x, hx, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    refine ⟨algebraMap A (Localization.AtPrime p) x, ?_, ?_⟩
    · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime p) p x).mpr hx
    · intro hzero
      exact hxn ((IsLocalization.injective (Localization.AtPrime p) hM)
        (by simpa using hzero))
  infer_instance

end IsLocalRing
