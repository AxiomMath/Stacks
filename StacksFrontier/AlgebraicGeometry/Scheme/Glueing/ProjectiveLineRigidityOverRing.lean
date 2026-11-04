module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ProjectiveLineCompactification
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineChartMorphisms
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLinePoints
public import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Automorphisms of the projective line over a ring fixing `0` and `∞`

Let `R` be a commutative ring and `ψ` an automorphism of `ℙ¹_R` over `R` which fixes the two
sections `0` and `∞`. Then `ψ` is a scaling `x ↦ u x` by a unit `u` of `R`.

## Main definitions

* `AlgebraicGeometry.projectiveLineZeroSection`: the section `0` of `ℙ¹_R ⟶ Spec R`, the origin
  of the first chart; the section `∞` is `AlgebraicGeometry.projectiveLineInfinitySection`, the
  origin of the second chart (`AlgebraicGeometry.projectiveLineInfinitySection_eq`).

## Main results

* `Polynomial.exists_eq_C_mul_X_of_toLaurent_mul_eq_one`: if `p, q ∈ R[x]` vanish at `0`, are
  invertible under composition and satisfy `p(T) q(T⁻¹) = 1`, then `p = u x` and `q = u⁻¹ x` for
  a unit `u`.
* `AlgebraicGeometry.range_projectiveLineXChart_eq_compl`: the first chart is the complement of
  `∞`, and `AlgebraicGeometry.range_projectiveLineYChart_eq_compl` the second the complement of
  `0`.
* `AlgebraicGeometry.exists_eq_projectiveLineScaling`: **an automorphism of `ℙ¹_R` over `R`
  fixing `0` and `∞` is a scaling.**

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Polynomial

universe u

/-! ### The algebraic lemma -/

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- Multiplication by `X` is injective. -/
theorem eq_of_X_mul_eq_X_mul {a b : R[X]} (h : X * a = X * b) : a = b :=
  Polynomial.ext fun n ↦ by simpa [coeff_X_mul] using congrArg (coeff · (n + 1)) h

/-- A polynomial `x p₁` with an inverse under composition has `p₁` a unit. -/
theorem isUnit_of_X_mul_comp_eq_X {p₁ p' : R[X]} (h : p'.comp (X * p₁) = X) :
    IsUnit p₁ := by
  have h0 : p'.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simpa [eval_comp] using congrArg (fun f : R[X] ↦ f.eval 0) h
  obtain ⟨p₁', rfl⟩ := X_dvd_iff.2 h0
  rw [mul_comp, X_comp] at h
  have hX : X * (p₁ * p₁'.comp (X * p₁)) = X * 1 := by
    rw [mul_one, ← mul_assoc]; exact h
  exact IsUnit.of_mul_eq_one _ (eq_of_X_mul_eq_X_mul hX)

open LaurentPolynomial in
/-- If `p₁(T) q₁(T⁻¹) = 1` in `R[T, T⁻¹]`, `p₁ ≠ 0` and the constant term of `q₁` is a unit, then
`p₁` is a constant. -/
theorem eq_C_of_toLaurent_mul_invert_eq_one [Nontrivial R] {p₁ q₁ : R[X]} (hp₁ : p₁ ≠ 0)
    (hq₁ : IsUnit (q₁.coeff 0)) (h : toLaurent p₁ * invert (toLaurent q₁) = 1) :
    p₁ = C (p₁.coeff 0) := by
  have hrev : p₁ * q₁.reverse = X ^ q₁.natDegree := by
    apply toLaurent_injective
    rw [map_mul, toLaurent_reverse, ← mul_assoc, h, one_mul, toLaurent_X_pow]
  have htr : q₁.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.2 (Or.inr hq₁.ne_zero)
  have hlc : q₁.reverse.leadingCoeff = q₁.coeff 0 := by
    rw [reverse_leadingCoeff, trailingCoeff, htr]
  have hdeg : q₁.reverse.natDegree = q₁.natDegree := by
    rw [reverse_natDegree, htr, Nat.sub_zero]
  have hmul : p₁.leadingCoeff * q₁.reverse.leadingCoeff ≠ 0 := by
    rw [hlc]
    exact fun h0 ↦ (leadingCoeff_ne_zero.2 hp₁) ((hq₁.mul_left_eq_zero).1 h0)
  have := natDegree_mul' hmul
  rw [hrev, natDegree_X_pow, hdeg] at this
  exact eq_C_of_natDegree_eq_zero (by omega)

open LaurentPolynomial in
/-- Let `p, q ∈ R[x]` vanish at `0`, be invertible under composition, and satisfy
`p(T) q(T⁻¹) = 1` in `R[T, T⁻¹]`. Then `p = u x` and `q = u⁻¹ x` for a unit `u`. -/
theorem exists_eq_C_mul_X_of_toLaurent_mul_eq_one {p q p' q' : R[X]} (hp0 : p.coeff 0 = 0)
    (hq0 : q.coeff 0 = 0) (hp' : p'.comp p = X) (hq' : q'.comp q = X)
    (h : toLaurent p * invert (toLaurent q) = 1) :
    ∃ u : Rˣ, p = C (u : R) * X ∧ q = C ((u⁻¹ : Rˣ) : R) * X := by
  nontriviality R
  obtain ⟨p₁, rfl⟩ := X_dvd_iff.2 hp0
  obtain ⟨q₁, rfl⟩ := X_dvd_iff.2 hq0
  have hu₁ := (isUnit_iff_coeff_isUnit_isNilpotent.1 (isUnit_of_X_mul_comp_eq_X hp')).1
  have hv₁ := (isUnit_iff_coeff_isUnit_isNilpotent.1 (isUnit_of_X_mul_comp_eq_X hq')).1
  have h₁ : toLaurent p₁ * invert (toLaurent q₁) = 1 := by
    have e : toLaurent (X * p₁) * invert (toLaurent (X * q₁)) =
        (T 1 * invert (T 1)) * (toLaurent p₁ * invert (toLaurent q₁)) := by
      simp only [map_mul, toLaurent_X]; ring
    rw [e, invert_T, ← T_add, add_neg_cancel, T_zero, one_mul] at h
    exact h
  have h₂ : toLaurent q₁ * invert (toLaurent p₁) = 1 := by
    have := congrArg invert h₁
    rwa [map_mul, involutive_invert, map_one, mul_comm] at this
  have hp₁ := eq_C_of_toLaurent_mul_invert_eq_one (fun h0 ↦ by simp [h0] at hu₁) hv₁ h₁
  have hq₁ := eq_C_of_toLaurent_mul_invert_eq_one (fun h0 ↦ by simp [h0] at hv₁) hu₁ h₂
  set a := p₁.coeff 0
  set b := q₁.coeff 0
  have hab : a * b = 1 := by
    rw [hp₁, hq₁] at h₁
    have e : invert (toLaurent (C b)) = toLaurent (C b) := by
      rw [Polynomial.toLaurent_C, invert_C]
    rw [e, ← map_mul, ← map_one (toLaurent (R := R)), ← map_mul C] at h₁
    exact C_injective (by rw [toLaurent_injective h₁, map_one])
  refine ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ?_, ?_⟩
  · rw [hp₁, mul_comm]
  · rw [hq₁, mul_comm]
    rfl

end Polynomial

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-- The origin `Spec R ⟶ Spec R[x]` of the affine line. -/
abbrev affineLineOriginHom : Spec (.of R) ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))

/-- The section `0` of `ℙ¹_R ⟶ Spec R`: the origin of the first chart. -/
abbrev projectiveLineZeroSection : Spec (.of R) ⟶ projectiveLine R :=
  affineLineOriginHom R ≫ projectiveLineXChart R

/-- The section `∞` of `ℙ¹_R ⟶ Spec R`, `AlgebraicGeometry.projectiveLineInfinitySection`, is
the origin of the second chart. -/
theorem projectiveLineInfinitySection_eq :
    projectiveLineInfinitySection R = affineLineOriginHom R ≫ projectiveLineYChart R :=
  rfl

/-- The origin of the affine line is the closed subset where the coordinate vanishes. -/
theorem range_affineLineOriginHom :
    Set.range (affineLineOriginHom R).base = {y | (X : R[X]) ∈ y.asIdeal} := by
  have h := range_comap_of_surjective (S := R) (Polynomial.evalRingHom (0 : R))
    (fun r ↦ ⟨C r, by simp⟩)
  rw [Polynomial.ker_evalRingHom, map_zero, sub_zero] at h
  show Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R))) = _
  rw [h, PrimeSpectrum.zeroLocus_span]
  ext y
  simp [PrimeSpectrum.mem_zeroLocus]
  rfl

variable {R}

/-- For a pullback square, a point of `B` maps into the range of `f` iff it is in the range of the
projection `d`. -/
private theorem base_mem_range_iff_of_isPullback {A B C Z : Scheme.{u}} {c : C ⟶ A} {d : C ⟶ B}
    {f : A ⟶ Z} {g : B ⟶ Z} (hp : IsPullback c d f g) (b : B) :
    g.base b ∈ Set.range f.base ↔ b ∈ Set.range d.base := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) a b ha
    refine ⟨hp.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_snd]
    exact hw₂
  · rintro ⟨t, rfl⟩
    refine ⟨c.base t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp.w]

/-- A point of the second chart lies in the first chart exactly when the coordinate does not
vanish there. -/
theorem projectiveLineYChart_mem_range_XChart_iff (b : Spec (.of R[X])) :
    (projectiveLineYChart R).base b ∈ Set.range (projectiveLineXChart R).base ↔
      (X : R[X]) ∉ b.asIdeal := by
  rw [← mem_range_projectiveLineOverlapYInclusion_iff]
  exact base_mem_range_iff_of_isPullback (isPullback_projectiveLineCharts R) b

/-- **The first chart is the complement of `∞`.** -/
theorem range_projectiveLineXChart_eq_compl :
    Set.range (projectiveLineXChart R).base =
      (Set.range (projectiveLineInfinitySection R).base)ᶜ := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩ ⟨s, hs⟩
    rw [projectiveLineInfinitySection_eq, Scheme.Hom.comp_apply] at hs
    exact (projectiveLineYChart_mem_range_XChart_iff _).1 ⟨a, hs.symm⟩
      ((range_affineLineOriginHom R).subset ⟨s, rfl⟩)
  · intro hz
    obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData R).ι_jointly_surjective z
    rcases i with ⟨_ | _⟩
    · exact ⟨y, rfl⟩
    · let y' : Spec (.of R[X]) := y
      show (projectiveLineYChart R).base y' ∈ _
      rw [projectiveLineYChart_mem_range_XChart_iff]
      intro hX
      obtain ⟨s, hs⟩ := (range_affineLineOriginHom R).ge hX
      exact hz ⟨s, by rw [projectiveLineInfinitySection_eq, Scheme.Hom.comp_apply, hs]; rfl⟩

/-- A point of the first chart lies in the second chart exactly when the coordinate does not
vanish there. -/
theorem projectiveLineXChart_mem_range_YChart_iff (b : Spec (.of R[X])) :
    (projectiveLineXChart R).base b ∈ Set.range (projectiveLineYChart R).base ↔
      (X : R[X]) ∉ b.asIdeal := by
  rw [← mem_range_projectiveLineOverlapYInclusion_iff]
  exact base_mem_range_iff_of_isPullback (isPullback_projectiveLineCharts' R) b

/-- **The second chart is the complement of `0`.** -/
theorem range_projectiveLineYChart_eq_compl :
    Set.range (projectiveLineYChart R).base =
      (Set.range (projectiveLineZeroSection R).base)ᶜ := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩ ⟨s, hs⟩
    rw [Scheme.Hom.comp_apply] at hs
    exact (projectiveLineXChart_mem_range_YChart_iff _).1 ⟨a, hs.symm⟩
      ((range_affineLineOriginHom R).subset ⟨s, rfl⟩)
  · intro hz
    obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData R).ι_jointly_surjective z
    rcases i with ⟨_ | _⟩
    · let y' : Spec (.of R[X]) := y
      show (projectiveLineXChart R).base y' ∈ _
      rw [projectiveLineXChart_mem_range_YChart_iff]
      intro hX
      obtain ⟨s, hs⟩ := (range_affineLineOriginHom R).ge hX
      exact hz ⟨s, by rw [Scheme.Hom.comp_apply, hs]; rfl⟩
    · exact ⟨y, rfl⟩

/-- An automorphism of `ℙ¹_R` fixing a section preserves its complement, read through an open
immersion whose range is that complement. -/
theorem range_comp_subset_of_fix {U : Scheme.{u}} (j : U ⟶ projectiveLine R)
    (σ : Spec (.of R) ⟶ projectiveLine R) (hj : Set.range j.base = (Set.range σ.base)ᶜ)
    (ψ : projectiveLine R ≅ projectiveLine R) (hσ : σ ≫ ψ.hom = σ) :
    Set.range (j ≫ ψ.hom).base ⊆ Set.range j.base := by
  rintro _ ⟨a, rfl⟩
  rw [hj]
  rintro ⟨s, hs⟩
  have hinj : Function.Injective ψ.hom.base := ψ.hom.isOpenEmbedding.injective
  have h1 : ψ.hom.base (σ.base s) = σ.base s := by
    rw [← Scheme.Hom.comp_apply, hσ]
  rw [Scheme.Hom.comp_apply, ← h1] at hs
  have : j.base a ∈ Set.range σ.base := ⟨s, hinj hs⟩
  exact (hj ▸ ⟨a, rfl⟩ : j.base a ∈ (Set.range σ.base)ᶜ) this

/-- The inverse coordinate `y ↦ T⁻¹` of the overlap is the inversion of the Laurent polynomial. -/
theorem projectiveLineOverlapInverseCoordinate_apply (q : R[X]) :
    projectiveLineOverlapInverseCoordinate R q = LaurentPolynomial.invert (toLaurent q) := by
  have : (projectiveLineOverlapInverseCoordinate R).toRingHom =
      (LaurentPolynomial.invert (R := R)).toRingEquiv.toRingHom.comp (toLaurent (R := R)) := by
    refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
    · simp [projectiveLineOverlapInverseCoordinate, LaurentPolynomial.algebraMap_apply,
        Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
    · simp [projectiveLineOverlapInverseCoordinate, LaurentPolynomial.invert_T]
  exact congrArg (fun f : R[X] →+* LaurentPolynomial R ↦ f q) this

/-- An automorphism of `ℙ¹_R` preserving the range of a chart acts on it by a ring endomorphism
of `R[x]`. -/
theorem exists_ringHom_of_range_subset (j : Spec (.of R[X]) ⟶ projectiveLine R)
    [IsOpenImmersion j] (ψ : projectiveLine R ⟶ projectiveLine R)
    (h : Set.range (j ≫ ψ).base ⊆ Set.range j.base) :
    ∃ φ : CommRingCat.of R[X] ⟶ CommRingCat.of R[X], Spec.map φ ≫ j = j ≫ ψ :=
  ⟨Spec.preimage (IsOpenImmersion.lift j (j ≫ ψ) h), by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

/-- A ring endomorphism of `R[x]` read on a chart of `ℙ¹_R` by an automorphism over `R` is an
`R`-algebra map, hence a substitution. -/
theorem ringHom_eq_eval₂RingHom_of_chart {j : Spec (.of R[X]) ⟶ projectiveLine R}
    (hj : j ≫ (projectiveLine R ↘ Spec (.of R)) = projectiveLineAffineStructureMorphism R)
    {ψ : projectiveLine R ⟶ projectiveLine R}
    (hψ : ψ ≫ (projectiveLine R ↘ Spec (.of R)) = projectiveLine R ↘ Spec (.of R))
    {φ : CommRingCat.of R[X] ⟶ CommRingCat.of R[X]} (hφ : Spec.map φ ≫ j = j ≫ ψ) :
    φ.hom = eval₂RingHom C (φ.hom X) := by
  have h1 : Spec.map φ ≫ projectiveLineAffineStructureMorphism R =
      projectiveLineAffineStructureMorphism R := by
    rw [← hj, ← Category.assoc, hφ, Category.assoc, hψ]
  have h2 : CommRingCat.ofHom (C : R →+* R[X]) ≫ φ = CommRingCat.ofHom C := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact h1
  refine Polynomial.ringHom_ext (fun r ↦ ?_) (by simp)
  have := congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of R[X] ↦ g r) h2
  simpa using this

/-- **An automorphism of `ℙ¹_R` over `R` fixing `0` and `∞` is a scaling `x ↦ u x`.** -/
theorem exists_eq_projectiveLineScaling (ψ : projectiveLine R ≅ projectiveLine R)
    (hψ : ψ.hom ≫ (projectiveLine R ↘ Spec (.of R)) = projectiveLine R ↘ Spec (.of R))
    (h0 : projectiveLineZeroSection R ≫ ψ.hom = projectiveLineZeroSection R)
    (hinf : projectiveLineInfinitySection R ≫ ψ.hom = projectiveLineInfinitySection R) :
    ∃ u : Rˣ, ψ.hom = projectiveLineScaling u := by
  have hsymm {σ : Spec (.of R) ⟶ projectiveLine R} (h : σ ≫ ψ.hom = σ) :
      σ ≫ ψ.symm.hom = σ := by
    simpa using (congrArg (· ≫ ψ.inv) h).symm
  obtain ⟨φx, hφx⟩ := exists_ringHom_of_range_subset (projectiveLineXChart R) ψ.hom
    (range_comp_subset_of_fix _ _ range_projectiveLineXChart_eq_compl ψ hinf)
  obtain ⟨φy, hφy⟩ := exists_ringHom_of_range_subset (projectiveLineYChart R) ψ.hom
    (range_comp_subset_of_fix _ _ range_projectiveLineYChart_eq_compl ψ h0)
  obtain ⟨φx', hφx'⟩ := exists_ringHom_of_range_subset (projectiveLineXChart R) ψ.inv
    (range_comp_subset_of_fix _ _ range_projectiveLineXChart_eq_compl ψ.symm (hsymm hinf))
  obtain ⟨φy', hφy'⟩ := exists_ringHom_of_range_subset (projectiveLineYChart R) ψ.inv
    (range_comp_subset_of_fix _ _ range_projectiveLineYChart_eq_compl ψ.symm (hsymm h0))
  have ex := ringHom_eq_eval₂RingHom_of_chart (projectiveLineXChart_comp_structureMorphism R)
    hψ hφx
  have ey := ringHom_eq_eval₂RingHom_of_chart (projectiveLineYChart_comp_structureMorphism R)
    hψ hφy
  have hcomp (j : Spec (.of R[X]) ⟶ projectiveLine R) [IsOpenImmersion j]
      {φ φ' : CommRingCat.of R[X] ⟶ CommRingCat.of R[X]} (hφ : Spec.map φ ≫ j = j ≫ ψ.hom)
      (hφ' : Spec.map φ' ≫ j = j ≫ ψ.inv) : φ.hom (φ'.hom X) = X := by
    have : φ' ≫ φ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_id]
      apply (cancel_mono j).1
      rw [Category.assoc, hφ', reassoc_of% hφ, ψ.hom_inv_id, Category.comp_id, Category.id_comp]
    exact congrArg (fun g : CommRingCat.of R[X] ⟶ CommRingCat.of R[X] ↦ g X) this
  have hpx : (φx'.hom X).comp (φx.hom X) = X := by
    exact (DFunLike.congr_fun ex _).symm.trans (hcomp _ hφx hφx')
  have hpy : (φy'.hom X).comp (φy.hom X) = X := by
    exact (DFunLike.congr_fun ey _).symm.trans (hcomp _ hφy hφy')
  have hzero (j : Spec (.of R[X]) ⟶ projectiveLine R) [IsOpenImmersion j]
      {φ : CommRingCat.of R[X] ⟶ CommRingCat.of R[X]} (hφ : Spec.map φ ≫ j = j ≫ ψ.hom)
      (hfix : affineLineOriginHom R ≫ j ≫ ψ.hom = affineLineOriginHom R ≫ j) :
      (φ.hom X).coeff 0 = 0 := by
    have : φ ≫ CommRingCat.ofHom (Polynomial.evalRingHom 0) =
        CommRingCat.ofHom (Polynomial.evalRingHom 0) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      apply (cancel_mono j).1
      rw [Category.assoc, hφ, hfix]
    have := congrArg (fun g : CommRingCat.of R[X] ⟶ CommRingCat.of R ↦ g X) this
    rw [coeff_zero_eq_eval_zero]
    simpa using this
  have hp0 := hzero _ hφx (by rw [← Category.assoc]; exact h0)
  have hq0 := hzero _ hφy (by rw [← Category.assoc]; exact hinf)
  have hp := isPullback_projectiveLineCharts R
  let w := hp.lift (projectiveLinePuncturedChart R ≫ Spec.map φx)
    (Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫
      Spec.map φy) (by
      rw [Category.assoc, hφx, ← Category.assoc, hp.w, Category.assoc, Category.assoc, hφy])
  let ω := Spec.preimage w
  have hω₁ : CommRingCat.ofHom (toLaurent (R := R)) ≫ ω =
      φx ≫ CommRingCat.ofHom (toLaurent (R := R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hp.lift_fst _ _ _
  have hω₂ : CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom ≫ ω =
      φy ≫ CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hp.lift_snd _ _ _
  have hlaurent : toLaurent (φx.hom X) * LaurentPolynomial.invert (toLaurent (φy.hom X)) = 1 := by
    have e₁ : ω.hom (toLaurent X) = toLaurent (φx.hom X) :=
      congrArg (fun g : CommRingCat.of R[X] ⟶ CommRingCat.of (LaurentPolynomial R) ↦ g.hom X) hω₁
    have e₂ : ω.hom (projectiveLineOverlapInverseCoordinate R X) =
        projectiveLineOverlapInverseCoordinate R (φy.hom X) :=
      congrArg (fun g : CommRingCat.of R[X] ⟶ CommRingCat.of (LaurentPolynomial R) ↦ g.hom X) hω₂
    rw [← projectiveLineOverlapInverseCoordinate_apply, ← e₁, ← e₂, ← map_mul,
      toLaurent_X_mul_overlapInverseCoordinate_X, map_one]
  obtain ⟨u, hu₁, hu₂⟩ := exists_eq_C_mul_X_of_toLaurent_mul_eq_one hp0 hq0 hpx hpy hlaurent
  refine ⟨u, projectiveLine_hom_ext ?_ ?_⟩
  · rw [← hφx, projectiveLineScaling, projectiveLineXChart_comp_projectiveLineHom]
    congr 2
    ext1
    rw [ex, hu₁]
    rfl
  · rw [← hφy, projectiveLineScaling, projectiveLineYChart_comp_projectiveLineHom]
    congr 2
    ext1
    rw [ey, hu₂]
    rfl

end AlgebraicGeometry
