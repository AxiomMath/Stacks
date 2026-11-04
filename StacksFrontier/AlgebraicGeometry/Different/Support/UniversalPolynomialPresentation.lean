module

public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamily

/-!
# Polynomial presentation of the universal quotient ring

The equations defining the universal quotient ring `B` of the universal quasi-finite family
eliminate the constant coefficient of each universal polynomial. So `B` is a polynomial ring over
`ℤ` in the variables `xᵢ` together with the nonconstant coefficients `a_{i,E}`. In particular `B`
is a domain.

## Main results

* `AlgebraicGeometry.universalQuotientRing_polynomial` gives the polynomial-ring presentation of
  the universal quotient ring.

## Implementation notes

The variable type is the disjoint union of the `xᵢ` and the pairs `(i, E)` with `E` a nonzero
multi-index. The statement asserts that a ring isomorphism exists, as `Nonempty` of the type of
ring isomorphisms.

## References

* [Stacks Project, Tag 0FK8](https://stacks.math.columbia.edu/tag/0FK8)
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry

private abbrev PresentationVars (n d : ℕ) :=
  Sum (Fin n) (Fin n × { E : MultiIndex n d // E.1 ≠ 0 })

/-- The zero multi-index. -/
def zeroMultiIndex (n d : ℕ) : MultiIndex n d := ⟨0, by simp⟩

private def xMonomial (n d : ℕ) (E : MultiIndex n d) :
    MvPolynomial (PresentationVars n d) ℤ :=
  (multiIndexExponent n d E).prod
    (fun j k => MvPolynomial.X (Sum.inl j) ^ k)

private def nonconstantTerm (n d : ℕ) (i : Fin n) (E : MultiIndex n d) :
    MvPolynomial (PresentationVars n d) ℤ :=
  if hE : E = zeroMultiIndex n d then 0 else
    MvPolynomial.X (Sum.inr (i, ⟨E, fun h => hE (Subtype.ext h)⟩)) * xMonomial n d E

private def nonconstantSum (n d : ℕ) (i : Fin n) : MvPolynomial (PresentationVars n d) ℤ :=
  ∑ E : MultiIndex n d, nonconstantTerm n d i E

private def coefficientValue (n d : ℕ) (i : Fin n) (E : MultiIndex n d) :
    MvPolynomial (PresentationVars n d) ℤ :=
  if hE : E = zeroMultiIndex n d then -nonconstantSum n d i else
    MvPolynomial.X (Sum.inr (i, ⟨E, fun h => hE (Subtype.ext h)⟩))

private def coefficientMap (n d : ℕ) :
    MvPolynomial (Fin n × MultiIndex n d) ℤ →+* MvPolynomial (PresentationVars n d) ℤ :=
  (MvPolynomial.aeval
    (fun (j : Fin n × MultiIndex n d) => coefficientValue n d j.1 j.2) :
      MvPolynomial (Fin n × MultiIndex n d) ℤ →ₐ[ℤ] MvPolynomial (PresentationVars n d) ℤ).toRingHom

private def ambientMap (n d : ℕ) :
    MvPolynomial (Fin n) (universalCoefficientRing n d) →+*
      MvPolynomial (PresentationVars n d) ℤ :=
  MvPolynomial.eval₂Hom (coefficientMap n d)
    (fun i => MvPolynomial.X (Sum.inl i))

private theorem zeroMultiIndex_eq_iff (n d : ℕ) (E : MultiIndex n d) :
    E = zeroMultiIndex n d ↔ E.1 = 0 :=
  Subtype.ext_iff

/-- The zero multi-index has zero exponent vector. -/
private theorem multiIndexExponent_zeroMultiIndex (n d : ℕ) :
    multiIndexExponent n d (zeroMultiIndex n d) = 0 := by
  ext j
  simp [zeroMultiIndex, multiIndexExponent]

private theorem coefficientMap_X (n d : ℕ) (i : Fin n) (E : MultiIndex n d) :
    coefficientMap n d (MvPolynomial.X (i, E)) = coefficientValue n d i E := by
  simp [coefficientMap]

private theorem coefficientValue_nonzero (n d : ℕ) (i : Fin n)
    (E : { E : MultiIndex n d // E.1 ≠ 0 }) :
    coefficientValue n d i E.1 = MvPolynomial.X (Sum.inr (i, E)) := by
  simp [coefficientValue, zeroMultiIndex_eq_iff, E.property]

private theorem ambientMap_universalPolynomial (n d : ℕ) (i : Fin n) :
    ambientMap n d (universalPolynomial n d i) = 0 := by
  classical
  let z := zeroMultiIndex n d
  let s := nonconstantSum n d i
  have hz : z ∈ (Finset.univ : Finset (MultiIndex n d)) := Finset.mem_univ _
  have hzexp : multiIndexExponent n d z = 0 := multiIndexExponent_zeroMultiIndex n d
  have hsum : s = ∑ E ∈ (Finset.univ.erase z), nonconstantTerm n d i E := by
    change (∑ E : MultiIndex n d, nonconstantTerm n d i E) = _
    rw [← Finset.sum_erase_add (Finset.univ : Finset (MultiIndex n d))
      (nonconstantTerm n d i) hz]
    simp [nonconstantTerm, z]
  simp only [ambientMap, universalPolynomial, universalCoefficient,
    map_sum, MvPolynomial.eval₂Hom_monomial, coefficientMap_X]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (MultiIndex n d))
    (fun E => coefficientValue n d i E *
      (multiIndexExponent n d E).prod
        (fun j k => MvPolynomial.X (Sum.inl j) ^ k)) hz]
  rw [show coefficientValue n d i z *
      (multiIndexExponent n d z).prod
        (fun j k => MvPolynomial.X (Sum.inl j) ^ k) = -s by
    simp [coefficientValue, z, s, hzexp]]
  have herase :
      (∑ E ∈ (Finset.univ.erase z), coefficientValue n d i E *
        (multiIndexExponent n d E).prod
          (fun j k => MvPolynomial.X (Sum.inl j) ^ k)) = s := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro E hE
    have hnz : E ≠ z := (Finset.mem_erase.mp hE).1
    simp [coefficientValue, nonconstantTerm, z, hnz, xMonomial]
  rw [herase]
  ring

private def targetValue (n d : ℕ) (v : PresentationVars n d) :
    universalQuotientRing n d :=
  match v with
  | Sum.inl i => Ideal.Quotient.mk _ (MvPolynomial.X i)
  | Sum.inr (i, E) =>
      Ideal.Quotient.mk _ (MvPolynomial.C (universalCoefficient n d i E.1))

private def targetMap (n d : ℕ) :
    MvPolynomial (PresentationVars n d) ℤ →+*
      universalQuotientRing n d :=
  (MvPolynomial.aeval (targetValue n d : PresentationVars n d →
      universalQuotientRing n d) :
    MvPolynomial (PresentationVars n d) ℤ →ₐ[ℤ] universalQuotientRing n d).toRingHom

private def quotientMap (n d : ℕ) :
    universalQuotientRing n d →+* MvPolynomial (PresentationVars n d) ℤ := by
  apply Ideal.Quotient.lift _ (ambientMap n d)
  intro p hp
  have hspan : universalRelationIdeal n d ≤ RingHom.ker (ambientMap n d) := by
    rw [universalRelationIdeal, Ideal.span_le]
    rintro q ⟨i, rfl⟩
    exact ambientMap_universalPolynomial n d i
  exact hspan hp

private theorem quotientMap_targetMap (n d : ℕ) :
    (quotientMap n d).comp (targetMap n d) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [targetMap, quotientMap, ambientMap, coefficientMap]
  · intro v
    cases v with
    | inl i => simp [targetMap, targetValue, quotientMap, ambientMap]
    | inr j =>
      rcases j with ⟨i, E⟩
      simp [targetMap, targetValue, quotientMap, ambientMap, coefficientMap,
        universalCoefficient, coefficientValue_nonzero]

private theorem universalPolynomial_eq_zero_quotient (n d : ℕ) (i : Fin n) :
    (Ideal.Quotient.mk (universalRelationIdeal n d)
      (universalPolynomial n d i) : universalQuotientRing n d) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

private theorem targetMap_nonconstantSum (n d : ℕ) (i : Fin n) :
    targetMap n d (nonconstantSum n d i) =
      ∑ E ∈ (Finset.univ.erase (zeroMultiIndex n d)),
        (Ideal.Quotient.mk (universalRelationIdeal n d)
          (MvPolynomial.monomial (multiIndexExponent n d E)
            (universalCoefficient n d i E)) : universalQuotientRing n d) := by
  classical
  let z := zeroMultiIndex n d
  have hz : z ∈ (Finset.univ : Finset (MultiIndex n d)) := Finset.mem_univ _
  calc
    targetMap n d (nonconstantSum n d i) =
        ∑ E : MultiIndex n d, targetMap n d (nonconstantTerm n d i E) := by
          simp [nonconstantSum]
    _ = ∑ E ∈ (Finset.univ.erase z), targetMap n d (nonconstantTerm n d i E) := by
          rw [← Finset.sum_erase_add (Finset.univ : Finset (MultiIndex n d))
            (fun E => targetMap n d (nonconstantTerm n d i E)) hz]
          simp [nonconstantTerm, z]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro E hE
          have hnz : E ≠ z := (Finset.mem_erase.mp hE).1
          simp [targetMap, targetValue, nonconstantTerm, z, hnz, xMonomial,
            universalCoefficient, MvPolynomial.monomial_eq]

private theorem quotient_zero_coefficient (n d : ℕ) (i : Fin n) :
    (Ideal.Quotient.mk (universalRelationIdeal n d)
      (MvPolynomial.C (universalCoefficient n d i (zeroMultiIndex n d))) :
        universalQuotientRing n d) = -targetMap n d (nonconstantSum n d i) := by
  classical
  let z := zeroMultiIndex n d
  have hz : z ∈ (Finset.univ : Finset (MultiIndex n d)) := Finset.mem_univ _
  have hzexp : multiIndexExponent n d z = 0 := multiIndexExponent_zeroMultiIndex n d
  have h := universalPolynomial_eq_zero_quotient n d i
  rw [universalPolynomial, map_sum] at h
  rw [← Finset.sum_erase_add (Finset.univ : Finset (MultiIndex n d))
    (fun E => Ideal.Quotient.mk (universalRelationIdeal n d)
      (MvPolynomial.monomial (multiIndexExponent n d E)
        (universalCoefficient n d i E))) hz] at h
  have hconst : (Ideal.Quotient.mk (universalRelationIdeal n d)
      (MvPolynomial.monomial (multiIndexExponent n d z)
        (universalCoefficient n d i z)) : universalQuotientRing n d) =
      Ideal.Quotient.mk _ (MvPolynomial.C (universalCoefficient n d i z)) := by
    simp [hzexp, MvPolynomial.monomial_zero']
  rw [hconst] at h
  rw [targetMap_nonconstantSum]
  linear_combination h

private theorem coefficientMap_targetMap (n d : ℕ) :
    (targetMap n d).comp (coefficientMap n d) =
      (Ideal.Quotient.mk (universalRelationIdeal n d)).comp MvPolynomial.C := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [targetMap, coefficientMap]
  · intro j
    rcases j with ⟨i, E⟩
    change targetMap n d (coefficientMap n d (MvPolynomial.X (i, E))) =
      Ideal.Quotient.mk (universalRelationIdeal n d)
        (MvPolynomial.C (MvPolynomial.X (i, E)) :
          MvPolynomial (Fin n) (universalCoefficientRing n d))
    rw [coefficientMap_X]
    by_cases hE : E = zeroMultiIndex n d
    · subst E
      rw [show targetMap n d (coefficientValue n d i (zeroMultiIndex n d)) =
        -targetMap n d (nonconstantSum n d i) by simp [coefficientValue]]
      exact (quotient_zero_coefficient n d i).symm
    · simp [coefficientValue, hE, targetMap, targetValue, universalCoefficient]

private theorem targetMap_quotientMap (n d : ℕ) :
    (targetMap n d).comp (quotientMap n d) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change targetMap n d (ambientMap n d (MvPolynomial.C a)) =
      Ideal.Quotient.mk (universalRelationIdeal n d) (MvPolynomial.C a)
    simp only [ambientMap, MvPolynomial.eval₂Hom_C]
    exact DFunLike.congr_fun (coefficientMap_targetMap n d) a
  · intro i
    simp [quotientMap, ambientMap, targetMap, targetValue]

/-- The universal quotient ring is a polynomial ring in the `xᵢ` and the
nonconstant universal coefficients. -/
public theorem universalQuotientRing_polynomial (n d : ℕ) :
    Nonempty (universalQuotientRing n d ≃+*
      MvPolynomial
        (Sum (Fin n)
          (Fin n × { E : MultiIndex n d // E.1 ≠ 0 })) ℤ) :=
  ⟨RingEquiv.ofRingHom (quotientMap n d) (targetMap n d)
    (quotientMap_targetMap n d) (targetMap_quotientMap n d)⟩

end AlgebraicGeometry
