module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelSingularPoint
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelBlowup
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCover
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.RingTheory.NodalChart.QuotientLocalization
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# The regular locus of the standard nodal model and of its blowup

Let `R` be a discrete valuation ring with uniformizer `π` and let `X = Spec R[x, y]/(xy - πⁿ)` be
the standard nodal model of [Stacks, Tag 0CDC]. Whatever the exponent, `X` is regular at every
point other than its origin `(π, x, y)`. Consequently the blowup `X'` of `X` at the origin, which
is covered by two regular outer charts and the central chart `Spec R[x, y]/(xy - π^(n - 2))`, is
regular away from the origin of the central chart.

## Main results

* `Stacks.isRegularLocalRing_localization_quotient_span_singleton_of_notMem_sq` — the pointwise
  Jacobian criterion for a hypersurface.
* `Stacks.isRegularLocalRing_stalk_spec_iff` — the stalk of `Spec A` at a prime is regular exactly
  when the localization at that prime is.
* `Stacks.isRegularLocalRing_localization_nodalChartRing_of_ne` — the nodal chart ring is regular
  at every prime other than the origin.
* `Stacks.isRegularLocalRing_stalk_nodalModel_of_asIdeal_ne` — the same for the stalks of the
  standard nodal model.
* `Stacks.exists_isOpenImmersion_nodalModel_sub_two_of_not_isRegularLocalRing` — the blowup of
  the standard nodal model at its origin is regular away from the origin of its central chart.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing MvPolynomial

universe u

namespace Stacks

/-- **The pointwise Jacobian criterion for a hypersurface.** Let `A` be a regular ring, `f ∈ A`,
and `q` a prime of `A ⧸ (f)` with contraction `p` to `A`. If `f` does not lie in the square of
the maximal ideal of `A_p`, then the localization of `A ⧸ (f)` at `q` is a regular local ring. -/
public theorem isRegularLocalRing_localization_quotient_span_singleton_of_notMem_sq
    {A : Type u} [CommRing A] [IsRegularRing A] (f : A) (q : Ideal (A ⧸ Ideal.span {f}))
    [q.IsPrime]
    (h : algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {f})))) f ∉
      maximalIdeal (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span {f})))) ^ 2) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let p : Ideal A := q.comap (Ideal.Quotient.mk (Ideal.span {f}))
  have : p.IsPrime := Ideal.IsPrime.comap _
  have hf : f ∈ p := by
    change Ideal.Quotient.mk (Ideal.span {f}) f ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
    exact q.zero_mem
  have hx : algebraMap A (Localization.AtPrime p) f ∈ maximalIdeal (Localization.AtPrime p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p) ▸
      Ideal.mem_map_of_mem _ hf
  have hJ : (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))
      = Ideal.span {algebraMap A (Localization.AtPrime p) f} := by
    simp [Ideal.map_span]
  have hreg : IsRegularLocalRing
      (Localization.AtPrime p ⧸ (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))) := by
    rw [hJ]
    exact Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton hx h
  have : IsLocalization q.primeCompl
      (Localization.AtPrime p ⧸ (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))) :=
    isLocalization_quotient_atPrime_of_mem_iff (p := p) (q := q) f (fun _ ↦ Iff.rfl)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime p ⧸ (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p)))
      (Localization.AtPrime q)).toRingEquiv

/-- **On an affine scheme `Spec A` the stalk at a point is regular exactly when the localization
of `A` at the corresponding prime is.** -/
public theorem isRegularLocalRing_stalk_spec_iff {A : Type u} [CommRing A]
    (z : PrimeSpectrum (CommRingCat.of A)) :
    IsRegularLocalRing ↑((Spec (CommRingCat.of A)).presheaf.stalk z) ↔
      IsRegularLocalRing (Localization.AtPrime z.asIdeal) := by
  refine ⟨fun h ↦ ?_, fun _ ↦
    IsRegularLocalRing.of_ringEquiv (StructureSheaf.stalkIso (CommRingCat.of A) z).toRingEquiv⟩
  have : IsRegularLocalRing ↑((structurePresheafInCommRingCat (CommRingCat.of A)).stalk z) := h
  exact .of_ringEquiv (StructureSheaf.stalkIso (CommRingCat.of A) z).toRingEquiv.symm

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The nodal chart ring `R[x, y]/(xy - πⁿ)` is regular away from its origin.** Its
localization at every prime other than the origin `(π, x, y)` is a regular local ring. -/
public theorem isRegularLocalRing_localization_nodalChartRing_of_ne {π : R} (hπ : Irreducible π)
    (n : ℕ) (q : Ideal (nodalChartRing R (π ^ n))) [q.IsPrime]
    (hq : q ≠ nodalModelOrigin R π n) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have hmax : (Ideal.span {π}).IsMaximal := isMaximal_span_singleton_of_irreducible hπ
  refine isRegularLocalRing_localization_quotient_span_singleton_of_notMem_sq _ q ?_
  set p := q.comap (Ideal.Quotient.mk (Ideal.span {nodalEquation R (π ^ n)})) with hpdef
  have : p.IsPrime := Ideal.IsPrime.comap _
  have hfp : nodalEquation R (π ^ n) ∈ p := by
    rw [Ideal.mem_comap, Ideal.Quotient.mk_singleton_self]
    exact q.zero_mem
  suffices h : ∃ i : Fin 2, MvPolynomial.pderiv (R := R) i (nodalEquation R (π ^ n)) ∉ p by
    obtain ⟨i, hi⟩ := h
    exact notMem_sq_of_derivation ((MvPolynomial.pderiv (R := R) i).restrictScalars ℤ) hi
  by_cases hx0 : X 0 ∈ p
  · by_cases hx1 : X 1 ∈ p
    · exfalso
      have heq : nodalOriginIdeal R π = p := (isMaximal_nodalOriginIdeal hmax).eq_of_le
        (Ideal.IsPrime.ne_top inferInstance) (nodalOriginIdeal_le_of_mem hfp hx0 hx1)
      apply hq
      rw [nodalModelOrigin_eq_map, heq, hpdef]
      exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q).symm
    · exact ⟨0, by simpa [nodalEquation_def] using hx1⟩
  · exact ⟨1, by simpa [nodalEquation_def] using hx0⟩

/-- **The standard nodal model is regular away from its origin.** Every stalk of
`Spec R[x, y]/(xy - πⁿ)` at a point other than the origin `(π, x, y)` is a regular local ring. -/
public theorem isRegularLocalRing_stalk_nodalModel_of_asIdeal_ne {π : R} (hπ : Irreducible π)
    (n : ℕ) (z : nodalModel R π n) (hz : z.asIdeal ≠ nodalModelOrigin R π n) :
    IsRegularLocalRing ((nodalModel R π n).presheaf.stalk z) := by
  have := z.isPrime
  exact (isRegularLocalRing_stalk_spec_iff z).mpr
    (isRegularLocalRing_localization_nodalChartRing_of_ne hπ n z.asIdeal hz)

/-- At exponent zero the origin of the standard nodal model is the unit ideal. -/
public theorem nodalModelOrigin_zero_eq_top (π : R) : nodalModelOrigin R π 0 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : nodalGen R (π ^ 0) 0 * nodalGen R (π ^ 0) 1 = 1 := by
    rw [nodalGen_zero_mul_nodalGen_one, pow_zero, map_one]
  rw [← h]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- **The blowup of the standard nodal model at its origin is regular away from the origin of its
central chart.** For `n ≥ 2` the central chart of the blowup `X'` of `Spec R[x, y]/(xy - πⁿ)` at
`(π, x, y)` is an open immersion of the standard nodal model of exponent `n - 2` over `S`, and
every point of `X'` at which `X'` is not regular is the image of a point of that chart lying at its
origin. -/
public theorem exists_isOpenImmersion_nodalModel_sub_two_of_not_isRegularLocalRing
    {π : R} (hπ : Irreducible π) {n : ℕ} (hn : 2 ≤ n) :
    ∃ jc : nodalModel R π (n - 2) ⟶ nodalModelBlowup R π n,
      IsOpenImmersion jc ∧ jc ≫ nodalModelBlowupToBase R π n = nodalModelHom R π (n - 2) ∧
        ∀ y : nodalModelBlowup R π n,
          ¬ IsRegularLocalRing ((nodalModelBlowup R π n).presheaf.stalk y) →
            ∃ z : nodalModel R π (n - 2), jc.base z = y ∧
              z.asIdeal = nodalModelOrigin R π (n - 2) := by
  obtain ⟨jc, hjcoi, hjcw, hjcrange⟩ := exists_isOpenImmersion_nodalModel_sub_two hπ.ne_zero hn
  refine ⟨jc, hjcoi, hjcw, fun y hy ↦ ?_⟩
  obtain ⟨i, u, hu⟩ := exists_mem_range_nodalModelBlowupChart π n y
  by_cases hi : i = 0
  · subst hi
    obtain ⟨z, rfl⟩ : y ∈ Set.range jc.base := by
      rw [hjcrange]
      exact ⟨u, hu⟩
    refine ⟨z, rfl, ?_⟩
    by_contra hz
    exact hy ((isRegularLocalRing_stalk_iff_of_isOpenImmersion jc z).mp
      (isRegularLocalRing_stalk_nodalModel_of_asIdeal_ne hπ (n - 2) z hz))
  · exfalso
    have hring : IsRegularRing
        (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i)) := by
      fin_cases i
      · exact absurd rfl hi
      · obtain ⟨ee, -⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_one hπ.ne_zero hn
        exact (isRegularRing_nodalChartRing hπ).of_ringEquiv ee.symm
      · obtain ⟨ee, -⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_two hπ.ne_zero hn
        exact (isRegularRing_nodalChartRing hπ).of_ringEquiv ee.symm
    subst hu
    exact hy ((isRegularLocalRing_stalk_iff_of_isOpenImmersion
      (nodalModelBlowupChart R π n i) u).mp
        ((@isRegular_spec_of_isRegularRing _ _ hring).isRegularLocalRing_stalk u))

end Stacks

end
