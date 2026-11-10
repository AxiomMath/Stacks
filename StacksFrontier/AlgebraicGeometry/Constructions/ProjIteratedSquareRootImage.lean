module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjIteratedSquareRoot

/-!
# The image of `Proj` in the iterated-square-root example

Let `S = ℂ[t][X₁, X₂, …]/(Xᵢ² - t Xᵢ₊₁)` with the grading of
`Stacks.IteratedSquareRootAlgebra.Grading`, whose degree-zero part is `ℂ[t]`. This file computes
the image of the structure morphism `Proj S → Spec ℂ[t]`: it is the distinguished open `D(t)`,
and in particular it is *not* closed. Since `Proj S` is affine in this example, this exhibits an
affine `Proj` whose structure morphism is not a closed immersion — the point of Tag 01MH.

## Main results

* `Stacks.IteratedSquareRootAlgebra.range_toSpec_eq_basicOpen_t`: the set-theoretic image of
  `Proj S → Spec ℂ[t]` is the distinguished open `D(t)`.
* `Stacks.IteratedSquareRootAlgebra.range_toSpec_eq_basicOpen_t_canonical`: the same for the
  grading the source specifies, with no grading hypothesised.
* `Stacks.IteratedSquareRootAlgebra.not_isClosed_range_toSpec`: **the structure morphism
  `Proj S → Spec ℂ[t]` is not closed.**

## Implementation notes

The structure morphism is written as `AlgebraicGeometry.Proj.toSpecZero` followed by the spectrum
map of the composite `ℂ[t] → S → S₀`, rather than through any packaging of the relative `Proj`.

Both inclusions are checked after restricting to the standard open `D₊(X₁)`, which is all of
`Proj S` by `Stacks.IteratedSquareRootAlgebra.basicOpen_x_zero_eq_top`, so that the morphism
becomes `Spec` of the ring map `ℂ[t] → S₍X₁₎`.

`D(t)` is not closed because `ℂ[t]` is a domain: the generic point `(0)` lies in `D(t)`, its
closure is all of `Spec ℂ[t]`, and the point `(t)` does not lie in `D(t)`.

The containment `image ⊆ D(t)` holds because `t` becomes invertible in `S₍X₁₎`: the relation
`X₁² = t X₂` makes `X₂ / X₁²` an inverse of the image of `t`. The reverse containment is the
standard construction of a prime of `S₍X₁₎` over a given prime of `ℂ[t]` avoiding `t`: the
`ℂ[t]`-algebra `S₍X₁₎` is given a `ℂ[t]`-algebra map to `ℂ[t]_t` by sending `Xᵢ₊₁` to `t^{-i}`
(the only choice compatible with the relations once `X₁ ↦ 1`), and the prime is pulled back along
it from the extension of the given prime to `ℂ[t]_t`.

## References

* [Stacks Project, Tag 01MH](https://stacks.math.columbia.edu/tag/01MH)
-/

@[expose] public section

namespace Stacks.IteratedSquareRootAlgebra

open AlgebraicGeometry CategoryTheory

/-- The localization `ℂ[t]_t`, the target of the auxiliary evaluation of the variables. -/
private abbrev AwayT := Localization.Away t

private noncomputable def awayTUnit : AwayTˣ :=
  (IsLocalization.Away.algebraMap_isUnit t).unit

private lemma awayTUnit_spec :
    (↑awayTUnit : AwayT) = algebraMap baseRing AwayT t := by
  simp [awayTUnit]

/-- The value of `Xᵢ₊₁` under the evaluation `S → ℂ[t]_t`: inductively `t^{-1}` times the square
of the previous value, starting from `X₁ ↦ 1`. -/
private noncomputable def xEval : ℕ → AwayT
  | 0 => 1
  | n + 1 => (↑(awayTUnit⁻¹) : AwayT) * (xEval n) ^ 2

private lemma xEval_relation (i : ℕ) :
    (xEval (i + 1)) * (algebraMap baseRing AwayT t) = (xEval i) ^ 2 := by
  simp only [xEval]
  calc
    (↑(awayTUnit⁻¹) : AwayT) * (xEval i) ^ 2 * (algebraMap baseRing AwayT t) =
      (↑(awayTUnit⁻¹) : AwayT) * ((↑awayTUnit : AwayT) * (xEval i) ^ 2) := by
        rw [awayTUnit_spec]
        ac_rfl
    _ = (xEval i) ^ 2 := by simp

private noncomputable def polynomialEval : polynomialRing →+* AwayT :=
  MvPolynomial.eval₂Hom (algebraMap baseRing AwayT) xEval

private noncomputable def ringEval : ring →+* AwayT :=
  Ideal.Quotient.lift relationIdeal polynomialEval (by
    have hrel : Ideal.span (Set.range relation) ≤ RingHom.ker polynomialEval := by
      apply Ideal.span_le.2
      rintro _ ⟨i, rfl⟩
      change polynomialEval (relation i) = 0
      simp only [polynomialEval, relation,
        map_sub, map_mul, MvPolynomial.eval₂Hom_X', map_pow, MvPolynomial.eval₂Hom_C]
      rw [mul_comm (algebraMap baseRing AwayT t) (xEval (i + 1)), xEval_relation]
      ring
    intro a ha
    exact RingHom.mem_ker.mp (by simpa [relationIdeal] using hrel ha))

private lemma ringEval_x (i : ℕ) : ringEval (x i) = xEval i := by
  simp [ringEval, x, polynomialEval]

private lemma ringEval_algebraMap (r : baseRing) :
    ringEval (algebraMap baseRing ring r) = algebraMap baseRing AwayT r := by
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := baseRing) (A := polynomialRing) relationIdeal r]
  unfold ringEval
  rw [Ideal.Quotient.lift_mk]
  simp [polynomialEval]

private noncomputable def localizationEval : Localization.Away (x 0) →+* AwayT :=
  Localization.awayLift ringEval (x 0) (by
    rw [ringEval_x]
    exact isUnit_one)

private noncomputable def degreeZeroEval (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    HomogeneousLocalization.Away s.grading (x 0) →+* AwayT := by
  letI : GradedAlgebra s.grading := s.gradedAlgebra
  exact localizationEval.comp
    (algebraMap (HomogeneousLocalization.Away s.grading (x 0)) (Localization.Away (x 0)))

private noncomputable def baseToDegreeZero (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    baseRing →+* HomogeneousLocalization.Away s.grading (x 0) := by
  letI : GradedAlgebra s.grading := s.gradedAlgebra
  exact (HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0))).comp
    ((GradedRing.projZeroRingHom' s.grading).comp (algebraMap baseRing ring))

private lemma fromZeroRingHom_eq_mk (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    ∀ a : s.grading 0,
      HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0)) a =
        HomogeneousLocalization.Away.mk s.grading (s.x_mem 0) 0 (a : ring) a.2 := by
  let : GradedAlgebra s.grading := s.gradedAlgebra
  intro a
  apply HomogeneousLocalization.val_injective (Submonoid.powers (x 0))
  simp only [HomogeneousLocalization.fromZeroRingHom]
  rfl

private lemma degreeZeroEval_comp_base (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    (degreeZeroEval s).comp (baseToDegreeZero s) = algebraMap baseRing AwayT := by
  let : GradedAlgebra s.grading := s.gradedAlgebra
  apply RingHom.ext
  intro (r : baseRing)
  have hr : algebraMap baseRing ring r ∈ s.grading 0 :=
    SetLike.algebraMap_mem_graded s.grading r
  simp only [degreeZeroEval, baseToDegreeZero, RingHom.comp_apply]
  change localizationEval
      (algebraMap (HomogeneousLocalization.Away s.grading (x 0))
        (Localization.Away (x 0))
        (HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0))
          ((GradedRing.projZeroRingHom' s.grading) (algebraMap baseRing ring r)))) = _
  let c : s.grading 0 := ⟨algebraMap baseRing ring r, hr⟩
  have hproj : (GradedRing.projZeroRingHom' s.grading) (algebraMap baseRing ring r) = c := by
    apply Subtype.ext
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_same s.grading hr]
  rw [hproj]
  change localizationEval
      (algebraMap (HomogeneousLocalization.Away s.grading (x 0))
        (Localization.Away (x 0))
        (HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0)) c)) = _
  rw [fromZeroRingHom_eq_mk s c]
  simp only [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  simpa [localizationEval, ringEval_algebraMap] using
    (Localization.awayLift_mk ringEval (x 0) (algebraMap baseRing ring r)
      (1 : AwayT) (by simp [ringEval_x, xEval]) 0)

private lemma isUnit_baseToDegreeZero_t (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    IsUnit (baseToDegreeZero s t) := by
  let : GradedAlgebra s.grading := s.gradedAlgebra
  have htmem : algebraMap baseRing ring t ∈ s.grading 0 :=
    SetLike.algebraMap_mem_graded s.grading t
  let ct : s.grading 0 := ⟨algebraMap baseRing ring t, htmem⟩
  have hproj : (GradedRing.projZeroRingHom' s.grading) (algebraMap baseRing ring t) = ct := by
    apply Subtype.ext
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_same s.grading htmem]
  have hmap : baseToDegreeZero s t =
      HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0)) ct := by
    change HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0))
      (GradedRing.projZeroRingHom' s.grading (algebraMap baseRing ring t)) = _
    rw [hproj]
  let ti : HomogeneousLocalization.Away s.grading (x 0) :=
    HomogeneousLocalization.Away.mk s.grading (s.x_mem 0) 2 (x 1) (by simpa using s.x_mem 1)
  refine (isUnit_iff_exists_inv).2 ⟨ti, ?_⟩
  rw [hmap, fromZeroRingHom_eq_mk s ct]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (x 0))
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, ti]
  simp only [Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff]
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, pow_zero]
  change (↑ct * x 1) = x 0 ^ 2 * 1
  rw [mul_one]
  change (algebraMap baseRing ring t) * x 1 = x 0 ^ 2
  exact (s.x_sq 0).symm

private lemma mem_spec_basicOpen_t_iff (q : Spec (.of baseRing)) :
    q ∈ (Spec (.of baseRing)).basicOpen ((Scheme.ΓSpecIso (.of baseRing)).inv t) ↔
      t ∉ q.asIdeal := by
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen t q

/-- The image of the structure morphism `Proj S → Spec ℂ[t]` is contained in `D(t)`. -/
private lemma range_toSpec_subset_basicOpen_t (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    ∀ p : AlgebraicGeometry.Proj s.grading,
      (Proj.toSpecZero s.grading ≫
        Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' s.grading).comp (algebraMap baseRing ring)))).base p ∈
        ((Spec (.of baseRing)).basicOpen ((Scheme.ΓSpecIso (.of baseRing)).inv t) :
          Set (Spec (.of baseRing))) := by
  let : GradedAlgebra s.grading := s.gradedAlgebra
  let f : baseRing →+* s.grading 0 :=
    (GradedRing.projZeroRingHom' s.grading).comp (algebraMap baseRing ring)
  let g : baseRing →+* HomogeneousLocalization.Away s.grading (x 0) :=
    (HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0))).comp f
  have hsurj : Function.Surjective
      (Proj.awayι s.grading (x 0) (s.x_mem 0) (by norm_num)).base := by
    intro p
    apply Scheme.Hom.mem_opensRange.mp
    rw [AlgebraicGeometry.Proj.opensRange_awayι, basicOpen_x_zero_eq_top s]
    exact Set.mem_univ _
  have hg : (Proj.awayι s.grading (x 0) (s.x_mem 0) (by norm_num) ≫
      (Proj.toSpecZero s.grading ≫ Spec.map (CommRingCat.ofHom f))) =
      Spec.map (CommRingCat.ofHom g) := by
    change (Proj.awayι s.grading (x 0) (s.x_mem 0) (by norm_num) ≫
      Proj.toSpecZero s.grading) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom g)
    rw [Proj.awayι_toSpecZero, ← Spec.map_comp]
    congr 1
  have htunit : IsUnit (g t) := by
    change IsUnit (baseToDegreeZero s t)
    exact isUnit_baseToDegreeZero_t s
  intro p
  obtain ⟨pAway, rfl⟩ := hsurj p
  rw [← Scheme.Hom.comp_apply, hg]
  apply (mem_spec_basicOpen_t_iff (Spec.map (CommRingCat.ofHom g) pAway)).2
  let pAwayPrime : PrimeSpectrum (HomogeneousLocalization.Away s.grading (x 0)) :=
    cast (Spec_carrier (.of <| HomogeneousLocalization.Away s.grading (x 0))) pAway
  change t ∉ (PrimeSpectrum.comap g pAwayPrime).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  intro h
  exact pAwayPrime.isPrime.ne_top (pAwayPrime.asIdeal.eq_top_of_isUnit_mem h htunit)

/-- Every point of `D(t)` is in the image of the structure morphism `Proj S → Spec ℂ[t]`. -/
private lemma basicOpen_t_subset_range_toSpec (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    ∀ q : Spec (.of baseRing),
      q ∈ ((Spec (.of baseRing)).basicOpen ((Scheme.ΓSpecIso (.of baseRing)).inv t) :
          Set (Spec (.of baseRing))) →
      q ∈ Set.range
        (Proj.toSpecZero s.grading ≫
          Spec.map (CommRingCat.ofHom
            ((GradedRing.projZeroRingHom' s.grading).comp (algebraMap baseRing ring)))).base := by
  let : GradedAlgebra s.grading := s.gradedAlgebra
  let f : baseRing →+* s.grading 0 :=
    (GradedRing.projZeroRingHom' s.grading).comp (algebraMap baseRing ring)
  let g : baseRing →+* HomogeneousLocalization.Away s.grading (x 0) :=
    (HomogeneousLocalization.fromZeroRingHom s.grading (Submonoid.powers (x 0))).comp f
  have hg : (Proj.awayι s.grading (x 0) (s.x_mem 0) (by norm_num) ≫
      (Proj.toSpecZero s.grading ≫ Spec.map (CommRingCat.ofHom f))) =
      Spec.map (CommRingCat.ofHom g) := by
    change (Proj.awayι s.grading (x 0) (s.x_mem 0) (by norm_num) ≫
      Proj.toSpecZero s.grading) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom g)
    rw [Proj.awayι_toSpecZero, ← Spec.map_comp]
    congr 1
  intro q hqt
  have hqt' : t ∉ q.asIdeal :=
    (mem_spec_basicOpen_t_iff q).mp (by simpa only [SetLike.mem_coe] using hqt)
  let qPrime : PrimeSpectrum baseRing := cast (Spec_carrier (.of baseRing)) q
  let qIdeal : Ideal baseRing := qPrime.asIdeal
  have hdisj : Disjoint (Submonoid.powers t : Set baseRing) (qIdeal : Set baseRing) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime t).2 hqt'
  let qAway : Ideal AwayT := Ideal.map (algebraMap baseRing AwayT) qIdeal
  have hqAwayPrime : qAway.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) AwayT qIdeal
      qPrime.isPrime hdisj
  let pAwayPrime : PrimeSpectrum (HomogeneousLocalization.Away s.grading (x 0)) :=
    ⟨Ideal.comap (degreeZeroEval s) qAway, Ideal.comap_isPrime (degreeZeroEval s) qAway⟩
  let pAway : Spec (.of <| HomogeneousLocalization.Away s.grading (x 0)) :=
    cast (Spec_carrier (.of <| HomogeneousLocalization.Away s.grading (x 0))).symm pAwayPrime
  have hcompPrime : PrimeSpectrum.comap g pAwayPrime = qPrime := by
    apply PrimeSpectrum.ext
    change Ideal.comap ((degreeZeroEval s).comp g) qAway = qIdeal
    change Ideal.comap ((degreeZeroEval s).comp (baseToDegreeZero s)) qAway = qIdeal
    rw [degreeZeroEval_comp_base]
    exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) AwayT
      qPrime.isPrime hdisj
  have hcomp : (Spec.map (CommRingCat.ofHom g)) pAway = q := by
    change cast (Spec_carrier (.of baseRing)).symm (PrimeSpectrum.comap g pAwayPrime) = q
    rw [hcompPrime]
    rfl
  refine ⟨(Proj.awayι s.grading (x 0) (s.x_mem 0) (by norm_num)).base pAway, ?_⟩
  rw [← Scheme.Hom.comp_apply, hg, hcomp]

/-- The image of the canonical morphism `Proj(S) → Spec(ℂ[t])` is `D(t)`. -/
public theorem range_toSpec_eq_basicOpen_t (s : Grading) :
    letI : GradedAlgebra s.grading := s.gradedAlgebra
    Set.range
        (Proj.toSpecZero s.grading ≫
          Spec.map (CommRingCat.ofHom
            ((GradedRing.projZeroRingHom' s.grading).comp
              (algebraMap baseRing ring)))).base =
      ((Spec (.of baseRing)).basicOpen
        ((Scheme.ΓSpecIso (.of baseRing)).inv t) : Set (Spec (.of baseRing))) := by
  let : GradedAlgebra s.grading := s.gradedAlgebra
  apply Set.ext
  intro q
  exact ⟨fun ⟨p, hp⟩ => hp ▸ range_toSpec_subset_basicOpen_t s p,
    basicOpen_t_subset_range_toSpec s q⟩

/-- **Stacks Project, Tag 01MH.** For the grading the source specifies, the image of the
canonical morphism `Proj(S) → Spec(ℂ[t])` is the distinguished open `D(t)`. -/
public theorem range_toSpec_eq_basicOpen_t_canonical :
    Set.range
        (Proj.toSpecZero canonicalGrading.grading ≫
          Spec.map (CommRingCat.ofHom
            ((GradedRing.projZeroRingHom' canonicalGrading.grading).comp
              (algebraMap baseRing ring)))).base =
      ((Spec (.of baseRing)).basicOpen
        ((Scheme.ΓSpecIso (.of baseRing)).inv t) : Set (Spec (.of baseRing))) :=
  range_toSpec_eq_basicOpen_t canonicalGrading

/-- The distinguished open `D(t)` is not closed in `Spec ℂ[t]`: it contains the generic point
`(0)`, whose closure is everything, but not the point `(t)`. -/
private lemma not_isClosed_primeSpectrum_basicOpen_t :
    ¬ IsClosed (PrimeSpectrum.basicOpen (t : baseRing) : Set (PrimeSpectrum baseRing)) := by
  intro hclosed
  set p₀ : PrimeSpectrum baseRing := ⟨⊥, Ideal.isPrime_bot⟩ with hp₀def
  have hp₀ : p₀.asIdeal = ⊥ := rfl
  have hgeneric : p₀ ∈
      (PrimeSpectrum.basicOpen (t : baseRing) : Set (PrimeSpectrum baseRing)) := by
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hp₀]
    simp
  have hsubset := hclosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hgeneric)
  rw [PrimeSpectrum.closure_singleton, hp₀, PrimeSpectrum.zeroLocus_bot] at hsubset
  have hprime : (Ideal.span {(t : baseRing)}).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have hmem := hsubset
    (Set.mem_univ (⟨Ideal.span {(t : baseRing)}, hprime⟩ : PrimeSpectrum baseRing))
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hmem
  exact hmem (Ideal.mem_span_singleton_self _)

/-- **Stacks Project, Tag 01MH.** The canonical morphism `Proj(S) → Spec(ℂ[t])` is **not
closed**: its image is `D(t)`, which is not a closed subset of `Spec ℂ[t]`. -/
public theorem not_isClosed_range_toSpec :
    ¬ IsClosed (Set.range
      (Proj.toSpecZero canonicalGrading.grading ≫
        Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' canonicalGrading.grading).comp
            (algebraMap baseRing ring)))).base) := by
  rw [range_toSpec_eq_basicOpen_t_canonical, basicOpen_eq_of_affine]
  exact not_isClosed_primeSpectrum_basicOpen_t

/-- **Stacks Project, Tag 01MH.** The worked example in a single statement, for the grading the
source specifies on `S = ℂ[t][X₁, X₂, …]/(Xᵢ² - t Xᵢ₊₁)`, `deg Xᵢ = 2ⁱ⁻¹`. In order: the image
of `t` lies in no point of `Proj S`; consecutive generators define the same standard open,
`D₊(Xᵢ) = D₊(Xᵢ₊₁)`; `Proj S` is quasi-compact; it is affine, being the single standard open
`D₊(X₁)`; the image of `Proj S → Spec ℂ[t]` is the distinguished open `D(t)`; and that morphism
is therefore not closed. -/
@[stacks 01MH "the example's six assertions in one statement"]
public theorem projCanonicalProperties :
    (∀ p : ProjectiveSpectrum canonicalGrading.grading,
        algebraMap baseRing ring t ∉ p.asHomogeneousIdeal) ∧
      (∀ i : ℕ, ProjectiveSpectrum.basicOpen canonicalGrading.grading (x i) =
        ProjectiveSpectrum.basicOpen canonicalGrading.grading (x (i + 1))) ∧
      CompactSpace (AlgebraicGeometry.Proj canonicalGrading.grading) ∧
      Proj.basicOpen canonicalGrading.grading (x 0) = ⊤ ∧
      IsAffine (AlgebraicGeometry.Proj canonicalGrading.grading) ∧
      Set.range
          (Proj.toSpecZero canonicalGrading.grading ≫
            Spec.map (CommRingCat.ofHom
              ((GradedRing.projZeroRingHom' canonicalGrading.grading).comp
                (algebraMap baseRing ring)))).base =
        ((Spec (.of baseRing)).basicOpen
          ((Scheme.ΓSpecIso (.of baseRing)).inv t) : Set (Spec (.of baseRing))) ∧
      ¬ IsClosed (Set.range
        (Proj.toSpecZero canonicalGrading.grading ≫
          Spec.map (CommRingCat.ofHom
            ((GradedRing.projZeroRingHom' canonicalGrading.grading).comp
              (algebraMap baseRing ring)))).base) :=
  ⟨algebraMap_t_notMem_canonical, basicOpen_x_eq_basicOpen_succ_canonical,
    compactSpace_proj_canonical, basicOpen_x_zero_eq_top_canonical, isAffine_proj_canonical,
    range_toSpec_eq_basicOpen_t_canonical, not_isClosed_range_toSpec⟩

end Stacks.IteratedSquareRootAlgebra

end
