module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.MonogenicPresentation
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed

/-!
# Lifting points through a monogenic localization map

Let `Φ` be a monic polynomial of positive degree satisfying `(πX + 1)^ℓ = π^ℓ Φ + 1`. Over an
absolutely integrally closed `A`-algebra, every point of the localization at `π^ℓ X + 1` lifts
through the substitution map `X ↦ Φ(X)` from the localization at `π X + 1`.

## Main results

* `surjective_precomp_localizationMap_of_isAbsolutelyIntegrallyClosed` gives surjectivity on
  `A`-algebra-valued points.

## Implementation notes

The source's group schemes `G` and `H` are represented by the two localized polynomial rings.
Their map on points is precomposition with the canonical substitution homomorphism of
Stacks 0GY3. The statement applies to any `A`, `π`, `ℓ`, and `Φ` satisfying that lemma's
hypotheses; the cyclotomic construction in the source supplies a particular such choice, with
`deg Φ = ℓ > 0`. Positive degree must be explicit for arbitrary base rings: if `π = 0`, the
displayed identity also admits the constant polynomial `1`, whose substitution map is not
surjective on points.

## References

* [Stacks Project, Tag 0GY5](https://stacks.math.columbia.edu/tag/0GY5)
-/

@[expose] public section

open Polynomial


/-- Every point of the target of the monogenic map lifts over an absolutely
integrally closed `A`-algebra. -/
@[stacks 0GY5]
public theorem surjective_precomp_localizationMap_of_isAbsolutelyIntegrallyClosed
    (A : Type*) [CommRing A] (π : A) (ℓ : ℕ) (Φ : A[X])
    (hΦ : (C π * X + 1) ^ ℓ = C (π ^ ℓ) * Φ + 1)
    (hMonic : Φ.Monic)
    (hDegree : 0 < Φ.natDegree)
    (R : Type*) [CommRing R] [Algebra A R]
    (hR : IsAbsolutelyIntegrallyClosed R) :
    Function.Surjective (fun g : Localization.Away (C π * X + 1) →ₐ[A] R =>
      g.comp (localizationMap A π ℓ Φ hΦ)) := by
  classical
  intro h
  rcases subsingleton_or_nontrivial R with hR' | hR'
  · exact ⟨IsLocalization.Away.liftAlgHom (C π * X + 1) (f := aeval (0 : R)) (by simp),
      Subsingleton.elim _ _⟩
  · let a : R := h (algebraMap A[X] (Localization.Away (C (π ^ ℓ) * X + 1)) X)
    have hℓ : ℓ ≠ 0 := by
      rintro rfl
      have hΦ0 : Φ = 0 := add_right_cancel (show Φ + 1 = (0 : A[X]) + 1 by simpa using hΦ.symm)
      simp [hΦ0] at hDegree
    let P : R[X] := Φ.map (algebraMap A R) - C a
    have hPmonic : P.Monic := by
      show (Φ.map (algebraMap A R) - C a).Monic
      rw [Monic, leadingCoeff_sub_of_degree_lt]
      · exact hMonic.map (algebraMap A R)
      · rw [degree_eq_natDegree (hMonic.map (algebraMap A R)).ne_zero]
        exact degree_C_le.trans_lt
          (WithBot.coe_lt_coe.mpr (by simpa [hMonic.natDegree_map] using hDegree))
    have hPdegree : 1 ≤ P.natDegree := by
      simpa [P, natDegree_sub_C, hMonic.natDegree_map] using (Nat.succ_le_iff.mpr hDegree)
    obtain ⟨b, hb⟩ := hR.exists_root P hPmonic hPdegree
    have hΦb : aeval b Φ = a := by
      simpa [P, eval_sub, aeval_def, eval_map, sub_eq_zero] using hb
    let f : A[X] →ₐ[A] R := aeval b
    have hpower : (algebraMap A R π * b + 1) ^ ℓ =
        algebraMap A R (π ^ ℓ) * a + 1 := by
      calc
        (algebraMap A R π * b + 1) ^ ℓ = aeval b ((C π * X + 1) ^ ℓ) := by simp
        _ = aeval b (C (π ^ ℓ) * Φ + 1) := congrArg (aeval b) hΦ
        _ = algebraMap A R (π ^ ℓ) * a + 1 := by simp [hΦb]
    have hscalar (r : A) :
        h (algebraMap A[X] (Localization.Away (C (π ^ ℓ) * X + 1)) (C r)) =
          algebraMap A R r := by
      simpa only [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply] using h.commutes r
    have htarget : IsUnit (algebraMap A R (π ^ ℓ) * a + 1) := by
      convert IsUnit.map h
        (IsLocalization.Away.algebraMap_isUnit (C (π ^ ℓ) * X + 1)) using 1
      simp [a, hscalar, map_mul, map_add]
    have hdenUnit : IsUnit (f (C π * X + 1)) := by
      rw [show f (C π * X + 1) = algebraMap A R π * b + 1 by simp [f]]
      exact (isUnit_pow_iff hℓ).mp (hpower.symm ▸ htarget)
    let g : Localization.Away (C π * X + 1) →ₐ[A] R :=
      IsLocalization.Away.liftAlgHom (C π * X + 1) (f := f) hdenUnit
    refine ⟨g, ?_⟩
    apply IsLocalization.algHom_ext (Submonoid.powers (C (π ^ ℓ) * X + 1))
    ext
    show g (localizationMap A π ℓ Φ hΦ
      (algebraMap A[X] (Localization.Away (C (π ^ ℓ) * X + 1)) X)) =
        h (algebraMap A[X] (Localization.Away (C (π ^ ℓ) * X + 1)) X)
    rw [localizationMap_X]
    have hgX : g (algebraMap A[X] (Localization.Away (C π * X + 1)) X) = b := by
      show IsLocalization.Away.lift (C π * X + 1) hdenUnit
        (algebraMap A[X] (Localization.Away (C π * X + 1)) X) = b
      rw [IsLocalization.Away.lift_eq]
      simp [f]
    rw [← Polynomial.aeval_algHom_apply, hgX, hΦb]

