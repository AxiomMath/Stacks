module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistSections
public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationGraded

/-!
# The degree-zero localization of the truncation algebra on the punctured cone

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring, let `B = ⨁_{d ≥ 0} A_{≥ d}` be its truncation algebra,
let `f ∈ A_d` be homogeneous and write `ψ f = f⁽ᵈ⁾ ∈ B_d` and `σ f = f⁽⁰⁾ ∈ B_0`. Over the standard
open `D₊(f)` of `P = Proj A` the part of the cone `L = Proj B` lying over `U = Spec A ∖ V(A₊)` is
the standard open `D₊(σ f · ψ f)`, so the functions on it are the degree-zero part
`(B[1/σ f · ψ f])₀` of a localization of `B`. This file identifies that ring with the whole of the
localization `A[1/f]`, hence with the direct sum of all its homogeneous parts:

  `(B[1/σ f · ψ f])₀ = A[1/f] = ⨁_{m ∈ ℤ} (A[1/f])_m`.

## Main definitions

* `Stacks.Truncation.sigmaMulPsi`: the element `σ f · ψ f = (f²)⁽ᵈ⁾` of `B_d` whose standard open
  is the punctured cone over `D₊(f)`.
* `Stacks.Truncation.puncturedElt`: the fraction `a⁽ᵏᵈ⁾ / (σ f · ψ f)ᵏ` of `(B[1/σ f · ψ f])₀`.
* `Stacks.Truncation.puncturedToLocalization`: the comparison ring map
  `(B[1/σ f · ψ f])₀ → A[1/f]`.
* `Stacks.Truncation.puncturedGrading`: the degree-`m` part of `(B[1/σ f · ψ f])₀`, for `m ∈ ℤ`.

## Main results

* `Stacks.Truncation.puncturedRingEquiv`: the comparison map is a ring isomorphism
  `(B[1/σ f · ψ f])₀ ≃+* A[1/f]`.
* `Stacks.Truncation.isInternal_puncturedGrading`: `(B[1/σ f · ψ f])₀ = ⨁_{m ∈ ℤ} (A[1/f])_m`,
  with `Stacks.Truncation.gradedRingPuncturedGrading` the resulting graded-ring structure and
  `Stacks.Truncation.puncturedGradingEquivAwayGrading` the identification of the summands.
* `Stacks.Truncation.puncturedGradingEquivSectionsTwist`: the degree-`m` summand is the module of
  sections of the twisting sheaf `𝒪_P(m)` over `D₊(f)`.
* `Stacks.Truncation.awayPieceEquivAwayGrading` and
  `Stacks.Truncation.awayGradingEquivSectionsTwist`: the same identification of the summands for
  the nonnegative half `Stacks.Truncation.awayGrading`.
* `Stacks.Truncation.puncturedDirectSumEquivSectionsTwist` and
  `Stacks.Truncation.awayDirectSumEquivSectionsTwist`: those identifications assembled over all
  degrees at once.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj DirectSum Opposite
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.Truncation

universe u

section Punctured

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {f : A}

/-! ### The element cutting out the punctured cone -/

/-- The element `σ f · ψ f` of `B = ⨁_{d ≥ 0} A_{≥ d}`, whose standard open is the part of the
cone lying over `U = Spec A ∖ V(A₊)` above the standard open `D₊(f)` of `P = Proj A`. -/
def sigmaMulPsi (f : A) : TruncationRing 𝒜 :=
  ((sigma 𝒜 f : grading 𝒜 0) : TruncationRing 𝒜) * psi 𝒜 f

/-- The square of a homogeneous element of degree `d` lies in `A_{≥ d}`. -/
theorem sq_mem_truncation (hf : f ∈ 𝒜 d) : f ^ 2 ∈ truncation 𝒜 d := by
  simpa [pow_two] using
    mul_mem_truncation 𝒜 (mem_truncation_of_mem 𝒜 le_rfl hf) (mem_truncation_zero 𝒜 f)

/-- `σ f · ψ f = (f²)⁽ᵈ⁾` for `f` homogeneous of degree `d`. -/
theorem sigmaMulPsi_eq_degElt (hf : f ∈ 𝒜 d) :
    sigmaMulPsi 𝒜 f = degElt 𝒜 d (f ^ 2) (sq_mem_truncation 𝒜 d hf) := by
  rw [sigmaMulPsi, coe_sigma_eq_degElt, psi_eq_degElt 𝒜 f hf, degElt_mul]
  exact degElt_congr 𝒜 (zero_add d) (pow_two f).symm _ _

/-- `σ f · ψ f` is homogeneous of degree `d`. -/
theorem sigmaMulPsi_mem_grading (hf : f ∈ 𝒜 d) : sigmaMulPsi 𝒜 f ∈ grading 𝒜 d := by
  rw [sigmaMulPsi_eq_degElt 𝒜 d hf]
  exact degElt_mem_grading _ _ _ _

/-- `(σ f · ψ f)ᵏ = (f ²ᵏ)⁽ᵏᵈ⁾`. -/
theorem sigmaMulPsi_pow_eq_degElt (hf : f ∈ 𝒜 d) (k : ℕ) :
    sigmaMulPsi 𝒜 f ^ k =
      degElt 𝒜 (k * d) ((f ^ 2) ^ k)
        (pow_mem_truncation 𝒜 (sq_mem_truncation 𝒜 d hf) k) := by
  rw [sigmaMulPsi_eq_degElt 𝒜 d hf, degElt_pow]

/-- `(σ f · ψ f)ᵏ` is homogeneous of degree `k * d`. -/
theorem sigmaMulPsi_pow_mem_grading (hf : f ∈ 𝒜 d) (k : ℕ) :
    sigmaMulPsi 𝒜 f ^ k ∈ grading 𝒜 (k * d) := by
  rw [sigmaMulPsi_pow_eq_degElt 𝒜 d hf k]
  exact degElt_mem_grading _ _ _ _

/-! ### The comparison ring map `(B[1/σ f · ψ f])₀ → A[1/f]` -/

/-- Forgetting the degree sends `σ a` to `a`. -/
theorem forgetDegree_coe_sigma (a : A) :
    forgetDegree 𝒜 ((sigma 𝒜 a : grading 𝒜 0) : TruncationRing 𝒜) = a := by
  rw [coe_sigma_eq_degElt, forgetDegree_degElt]

/-- Forgetting the degree sends `σ f · ψ f` to `f²`. -/
theorem forgetDegree_sigmaMulPsi : forgetDegree 𝒜 (sigmaMulPsi 𝒜 f) = f ^ 2 := by
  rw [sigmaMulPsi, map_mul, forgetDegree_coe_sigma, forgetDegree_psi, pow_two]

/-- The fraction `1 / f ²` inverts the image of `σ f · ψ f` under the composite
`B → A → A[1/f]`. -/
theorem comp_sigmaMulPsi_mul_awayFrac :
    ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜)) (sigmaMulPsi 𝒜 f) *
      awayFrac f 2 1 = 1 := by
  rw [RingHom.comp_apply, forgetDegree_sigmaMulPsi, ← awayFrac_zero_eq_algebraMap, awayFrac_mul,
    ← awayFrac_shift f 0 2 1, awayFrac_one]

/-- The comparison map `(B[1/σ f · ψ f])₀ → A[1/f]`: it sends the fraction
`a⁽ᵏᵈ⁾ / (σ f · ψ f)ᵏ` to the fraction `a / f ²ᵏ`. It is the composite of the inclusion of
`(B[1/σ f · ψ f])₀` into the full localization with the map induced on localizations by the
degree-forgetting ring map `B → A`. -/
def puncturedToLocalization :
    HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f) →+* Localization.Away f :=
  (Localization.awayLift ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜))
      (sigmaMulPsi 𝒜 f)
      (isUnit_iff_exists_inv.mpr ⟨awayFrac f 2 1, comp_sigmaMulPsi_mul_awayFrac 𝒜⟩)).comp
    (algebraMap (HomogeneousLocalization (grading 𝒜) (Submonoid.powers (sigmaMulPsi 𝒜 f)))
      (Localization (Submonoid.powers (sigmaMulPsi 𝒜 f))))

/-- The element `a⁽ᵏᵈ⁾ / (σ f · ψ f)ᵏ` of the degree-zero part `(B[1/σ f · ψ f])₀` of the
localization of the truncation algebra at `σ f · ψ f`. -/
def puncturedElt (hf : f ∈ 𝒜 d) (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * d)) :
    HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f) :=
  HomogeneousLocalization.mk
    ⟨k * d, ⟨degElt 𝒜 (k * d) a ha, degElt_mem_grading 𝒜 (k * d) a ha⟩,
      ⟨sigmaMulPsi 𝒜 f ^ k, sigmaMulPsi_pow_mem_grading 𝒜 d hf k⟩, ⟨k, rfl⟩⟩

/-- Powers of the fraction `1 / f ²`. -/
theorem awayFrac_two_one_pow (n : ℕ) : awayFrac f 2 (1 : A) ^ n = awayFrac f (2 * n) 1 := by
  rw [← awayFrac_one_one_pow f 2, ← pow_mul, awayFrac_one_one_pow]

/-- The comparison map sends `a⁽ᵏᵈ⁾ / (σ f · ψ f)ᵏ` to `a / f ²ᵏ`. -/
theorem puncturedToLocalization_puncturedElt (hf : f ∈ 𝒜 d) (k : ℕ) (a : A)
    (ha : a ∈ truncation 𝒜 (k * d)) :
    puncturedToLocalization 𝒜 (puncturedElt 𝒜 d hf k a ha) = awayFrac f (2 * k) a := by
  rw [puncturedToLocalization, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    puncturedElt, HomogeneousLocalization.val_mk,
    Localization.awayLift_mk _ _ _ _ (comp_sigmaMulPsi_mul_awayFrac 𝒜) k, RingHom.comp_apply,
    forgetDegree_degElt, ← awayFrac_zero_eq_algebraMap, awayFrac_two_one_pow, awayFrac_mul,
    mul_one, zero_add]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- Two homogeneous parts of `B` in equal degrees have the same elements. -/
private theorem mem_grading_of_eq {i j : ℕ} (h : i = j) {x : TruncationRing 𝒜}
    (hx : x ∈ grading 𝒜 i) : x ∈ grading 𝒜 j :=
  h ▸ hx

/-- Every element of `(B[1/σ f · ψ f])₀` is a fraction `a⁽ᵏᵈ⁾ / (σ f · ψ f)ᵏ` with
`a ∈ A_{≥ kd}`. -/
theorem puncturedElt_surjective (hf : f ∈ 𝒜 d)
    (y : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) :
    ∃ (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * d)), puncturedElt 𝒜 d hf k a ha = y := by
  obtain ⟨k, x, hx, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading 𝒜) (sigmaMulPsi_mem_grading 𝒜 d hf) y
  obtain ⟨a, ha, rfl⟩ := exists_eq_degElt 𝒜 (mem_grading_of_eq 𝒜 (nsmul_eq_mul k d) hx)
  refine ⟨k, a, ha, congrArg HomogeneousLocalization.mk ?_⟩
  exact HomogeneousLocalization.NumDenSameDeg.ext _ (nsmul_eq_mul k d).symm rfl rfl

/-- A fraction `a⁽ᵏᵈ⁾ / (σ f · ψ f)ᵏ` vanishes as soon as a power of `f` kills `a`. -/
theorem puncturedElt_eq_zero (hf : f ∈ 𝒜 d) (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * d))
    (n : ℕ) (hn : f ^ n * a = 0) : puncturedElt 𝒜 d hf k a ha = 0 := by
  have hzero : (f ^ 2) ^ n * a = 0 := by
    rw [← pow_mul, two_mul, pow_add, mul_assoc, hn, mul_zero]
  refine HomogeneousLocalization.val_injective _ ?_
  rw [puncturedElt, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨sigmaMulPsi 𝒜 f ^ n, n, rfl⟩, ?_⟩
  show sigmaMulPsi 𝒜 f ^ n * degElt 𝒜 (k * d) a ha = 0
  rw [sigmaMulPsi_pow_eq_degElt 𝒜 d hf n, degElt_mul,
    degElt_congr 𝒜 rfl hzero _ (zero_mem _), degElt_zero]

/-- The comparison map `(B[1/σ f · ψ f])₀ → A[1/f]` is injective. -/
theorem puncturedToLocalization_injective (hf : f ∈ 𝒜 d) :
    Function.Injective (puncturedToLocalization 𝒜 (f := f)) := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
  obtain ⟨k, a, ha, rfl⟩ := puncturedElt_surjective 𝒜 d hf y
  rw [puncturedToLocalization_puncturedElt 𝒜 d hf k a ha, awayFrac_eq_zero_iff] at hy
  exact hy.elim (puncturedElt_eq_zero 𝒜 d hf k a ha)

/-- The comparison map `(B[1/σ f · ψ f])₀ → A[1/f]` is surjective. -/
theorem puncturedToLocalization_surjective (hf : f ∈ 𝒜 d) :
    Function.Surjective (puncturedToLocalization 𝒜 (f := f)) := by
  intro z
  induction z using Localization.induction_on with
  | H y =>
    obtain ⟨a, s⟩ := y
    obtain ⟨n, hn⟩ := s.2
    have hs : Localization.mk a s = awayFrac f n a :=
      congrArg (Localization.mk a) (Subtype.ext hn.symm)
    have hmem : f ^ n * a ∈ truncation 𝒜 (n * d) := by
      simpa using mul_mem_truncation 𝒜
        (pow_mem_truncation 𝒜 (mem_truncation_of_mem 𝒜 le_rfl hf) n) (mem_truncation_zero 𝒜 a)
    refine ⟨puncturedElt 𝒜 d hf n (f ^ n * a) hmem, ?_⟩
    rw [puncturedToLocalization_puncturedElt 𝒜 d hf n _ hmem, two_mul,
      ← awayFrac_shift f n n a, hs]

/-- `(B[1/σ f · ψ f])₀ = A[1/f]`: the degree-zero part of the localization of the truncation
algebra at `σ f · ψ f` is the whole localization of `A` at `f`, the comparison map
`a⁽ᵏᵈ⁾ / (σ f · ψ f)ᵏ ↦ a / f ²ᵏ` being a ring isomorphism. -/
@[stacks 0EKG "the equality of rings (B[1/σ f · ψ f])_0 = A[1/f], the functions on the punctured \
cone over a standard open D₊(f) of P"]
def puncturedRingEquiv (hf : f ∈ 𝒜 d) :
    HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f) ≃+* Localization.Away f :=
  RingEquiv.ofBijective (puncturedToLocalization 𝒜)
    ⟨puncturedToLocalization_injective 𝒜 d hf, puncturedToLocalization_surjective 𝒜 d hf⟩

/-- The comparison map undoes the inverse of the comparison isomorphism. -/
theorem puncturedToLocalization_symm_apply (hf : f ∈ 𝒜 d) (z : Localization.Away f) :
    puncturedToLocalization 𝒜 ((puncturedRingEquiv 𝒜 d hf).symm z) = z :=
  (puncturedRingEquiv 𝒜 d hf).apply_symm_apply z

/-! ### The `ℤ`-grading of `(B[1/σ f · ψ f])₀` -/

/-- The product of two homogeneous elements of `A` is homogeneous of the sum of the degrees, in
the grading extended to `ℤ` by zero. -/
private theorem mul_mem_integerGrading_add {i j : ℤ} {a b : A}
    (ha : a ∈ integerGrading 𝒜 i) (hb : b ∈ integerGrading 𝒜 j) :
    a * b ∈ integerGrading 𝒜 (i + j) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [integerGrading_neg 𝒜 i hi, Submodule.mem_bot] at ha
    simp [ha]
  rcases lt_or_ge j 0 with hj | hj
  · rw [integerGrading_neg 𝒜 j hj, Submodule.mem_bot] at hb
    simp [hb]
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = (q : ℤ) := ⟨j.toNat, by omega⟩
  rw [integerGrading_natCast, mem_homogeneousSubmodule] at ha hb
  rw [show (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ) from by push_cast; ring,
    integerGrading_natCast, mem_homogeneousSubmodule]
  exact SetLike.mul_mem_graded ha hb

/-- The `ℤ`-grading of `A[1/f]` is multiplicative: two fractions with homogeneous numerators
multiply to one with a homogeneous numerator, over the product of the denominators. -/
private theorem mul_mem_awayGrading (hf : f ∈ 𝒜 d) {m n : ℤ} {z w : Localization.Away f}
    (hz : z ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m)
    (hw : w ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf n) :
    z * w ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf (m + n) := by
  obtain ⟨k, a, ha, rfl⟩ := (Stacks.ProjectiveCohomology.mem_awayGrading 𝒜).mp hz
  obtain ⟨l, b, hb, rfl⟩ := (Stacks.ProjectiveCohomology.mem_awayGrading 𝒜).mp hw
  refine (Stacks.ProjectiveCohomology.mem_awayGrading 𝒜).mpr
    ⟨k + l, a * b, ?_, awayFrac_mul f k l a b⟩
  have h := mul_mem_integerGrading_add 𝒜 ha hb
  rwa [show ((k * d : ℕ) : ℤ) + m + (((l * d : ℕ) : ℤ) + n) =
    (((k + l) * d : ℕ) : ℤ) + (m + n) from by push_cast; ring] at h

/-- The degree-`m` part of `(B[1/σ f · ψ f])₀`, for an arbitrary integer `m`: the elements
whose image in `A[1/f]` is homogeneous of degree `m`. -/
def puncturedGrading (hf : f ∈ 𝒜 d) (m : ℤ) :
    AddSubgroup (HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) :=
  AddSubgroup.comap (puncturedToLocalization 𝒜 (f := f)).toAddMonoidHom
    (Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m).toAddSubgroup

/-- An element of `(B[1/σ f · ψ f])₀` is of degree `m` exactly when its image in `A[1/f]` is. -/
theorem mem_puncturedGrading_iff (hf : f ∈ 𝒜 d) (m : ℤ)
    (y : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) :
    y ∈ puncturedGrading 𝒜 d hf m ↔
      puncturedToLocalization 𝒜 y ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m :=
  Iff.rfl

/-- The pieces of `(B[1/σ f · ψ f])₀` form a graded monoid of additive subgroups. -/
instance instGradedMonoidPuncturedGrading (hf : f ∈ 𝒜 d) :
    SetLike.GradedMonoid (puncturedGrading 𝒜 d hf) where
  one_mem := by
    rw [mem_puncturedGrading_iff, map_one]
    refine (Stacks.ProjectiveCohomology.mem_awayGrading 𝒜).mpr
      ⟨0, 1, ?_, (awayFrac_one f).symm⟩
    rw [show ((0 * d : ℕ) : ℤ) + (0 : ℤ) = ((0 : ℕ) : ℤ) from by push_cast; ring,
      integerGrading_natCast, mem_homogeneousSubmodule]
    exact SetLike.one_mem_graded 𝒜
  mul_mem := @fun m n x y hx hy => by
    rw [mem_puncturedGrading_iff, map_mul]
    exact mul_mem_awayGrading 𝒜 d hf hx hy

/-- The image of `x` in `M` under `DirectSum.coeAddMonoidHom` is the sum of its components. -/
private theorem coeAddMonoidHom_eq_sum_support {ι M S : Type*} [DecidableEq ι]
    [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M] (A : ι → S)
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (x : ⨁ i, A i) :
    DirectSum.coeAddMonoidHom A x = ∑ j ∈ x.support, (x j : M) := by
  classical
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  congr

/-- `(B[1/σ f · ψ f])₀ = ⨁_{m ∈ ℤ} (A[1/f])_m`: the degree-zero part of the localization of the
truncation algebra at `σ f · ψ f` is the internal direct sum of its homogeneous pieces, which the
comparison map identifies with the homogeneous parts of `A[1/f]` in all integer degrees. -/
@[stacks 0EKG "the equality of homogeneous parts (B[1/σ f · ψ f])_0 = ⨁_{m ∈ ℤ} (A[1/f])_m, the \
ring-theoretic form of the identification of the direct image of the structure sheaf of the \
punctured cone with the sum of all the integral twists"]
theorem isInternal_puncturedGrading (hf : f ∈ 𝒜 d) :
    DirectSum.IsInternal (puncturedGrading 𝒜 d hf) := by
  classical
  have hint : DirectSum.IsInternal (Stacks.ProjectiveCohomology.awayGrading 𝒜 hf) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Stacks.ProjectiveCohomology.iSupIndep_awayGrading 𝒜 hf)
      (Stacks.ProjectiveCohomology.iSup_awayGrading_eq_top 𝒜 hf)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
  · refine DFinsupp.ext fun m => ?_
    by_cases hm : m ∈ x.support
    · have h0 : ∑ j ∈ x.support, puncturedToLocalization 𝒜 (f := f) (x j) = 0 := by
        rw [← map_sum, ← coeAddMonoidHom_eq_sum_support, hx, map_zero]
      have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
        (Stacks.ProjectiveCohomology.awayGrading 𝒜 hf)).mp
        (Stacks.ProjectiveCohomology.iSupIndep_awayGrading 𝒜 hf) x.support
        (fun j => puncturedToLocalization 𝒜 (f := f) (x j))
        (fun j _ => (x j).2) h0 m hm
      refine ZeroMemClass.coe_eq_zero.mp (puncturedToLocalization_injective 𝒜 d hf ?_)
      rw [hzero, map_zero]
    · exact DFinsupp.notMem_support_iff.mp hm
  · obtain ⟨ζ, hζ⟩ := hint.2 (puncturedToLocalization 𝒜 (f := f) y)
    have hmem : ∀ j : ℤ, (puncturedRingEquiv 𝒜 d hf).symm
        ((ζ j : LocalizedModule.Away f A)) ∈ puncturedGrading 𝒜 d hf j := fun j => by
      rw [mem_puncturedGrading_iff, puncturedToLocalization_symm_apply]
      exact (ζ j).2
    refine ⟨∑ j ∈ ζ.support,
      DirectSum.of (fun m : ℤ => ↥(puncturedGrading 𝒜 d hf m)) j ⟨_, hmem j⟩, ?_⟩
    refine puncturedToLocalization_injective 𝒜 d hf ?_
    rw [map_sum, Finset.sum_congr rfl fun j _ =>
        DirectSum.coeAddMonoidHom_of (puncturedGrading 𝒜 d hf) j ⟨_, hmem j⟩, map_sum,
      Finset.sum_congr rfl fun j _ =>
        puncturedToLocalization_symm_apply 𝒜 d hf ((ζ j : LocalizedModule.Away f A)),
      ← hζ, coeAddMonoidHom_eq_sum_support]

/-- The graded-ring structure on `(B[1/σ f · ψ f])₀` given by the pieces
`Stacks.Truncation.puncturedGrading`. -/
@[instance_reducible]
def gradedRingPuncturedGrading (hf : f ∈ 𝒜 d) : GradedRing (puncturedGrading 𝒜 d hf) :=
  { instGradedMonoidPuncturedGrading 𝒜 d hf,
    (isInternal_puncturedGrading 𝒜 d hf).chooseDecomposition with }

/-- The degree-`m` piece of `(B[1/σ f · ψ f])₀` is the degree-`m` part of `A[1/f]`, for every
integer `m`. -/
@[stacks 0EKG "the degree-m piece of (B[1/σ f · ψ f])_0 is (A[1/f])_m, for every integer m"]
def puncturedGradingEquivAwayGrading (hf : f ∈ 𝒜 d) (m : ℤ) :
    puncturedGrading 𝒜 d hf m ≃+ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m where
  toFun y := ⟨puncturedToLocalization 𝒜 (y : _), y.2⟩
  invFun z := ⟨(puncturedRingEquiv 𝒜 d hf).symm (z : LocalizedModule.Away f A), by
    rw [mem_puncturedGrading_iff, puncturedToLocalization_symm_apply]
    exact z.2⟩
  left_inv y := Subtype.ext ((puncturedRingEquiv 𝒜 d hf).symm_apply_apply (y : _))
  right_inv z := Subtype.ext ((puncturedRingEquiv 𝒜 d hf).apply_symm_apply (z : _))
  map_add' y y' := Subtype.ext (map_add _ _ _)

end Punctured

/-! ### The summands as sections of the twisting sheaves -/

section Sections

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {f : A}

/-- In a nonnegative degree `m` the `ℤ`-graded piece of `A[1/f]` is the piece
`Stacks.Truncation.awayPiece`: both are the fractions `a / f ᵏ` with `a` homogeneous of degree
`m + kd`. -/
theorem mem_awayGrading_natCast_iff (hf : f ∈ 𝒜 d) (m : ℕ) (z : Localization.Away f) :
    z ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf (m : ℤ) ↔ z ∈ awayPiece 𝒜 d hf m := by
  have hcast (k : ℕ) : ((k * d : ℕ) : ℤ) + (m : ℤ) = ((m + k * d : ℕ) : ℤ) := by push_cast; ring
  simp only [Stacks.ProjectiveCohomology.mem_awayGrading, mem_awayPiece_iff, hcast,
    integerGrading_natCast, mem_homogeneousSubmodule]
  rfl

/-- For `m ≥ 0`, the degree-`m` piece `Stacks.Truncation.awayPiece` of `Localization.Away f` is
the degree-`m` part `Stacks.ProjectiveCohomology.awayGrading` of `LocalizedModule.Away f A`, the
two localizations being the same ring. -/
def awayPieceEquivAwayGrading (hf : f ∈ 𝒜 d) (m : ℕ) :
    awayPiece 𝒜 d hf m ≃+ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf (m : ℤ) where
  toFun z := ⟨(z : Localization.Away f), (mem_awayGrading_natCast_iff 𝒜 d hf m _).mpr z.2⟩
  invFun z := ⟨(z : LocalizedModule.Away f A),
    (mem_awayGrading_natCast_iff 𝒜 d hf m _).mp z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The degree-`m` summand of `(B[1/ψ f])₀` is the module of sections of the twisting sheaf
`𝒪_P(m)` over `D₊(f)`, for `m ≥ 0`. -/
@[stacks 0EKG "the degree-m summand of the functions on the cone over D₊(f) is the module of \
sections of O_P(m) over D₊(f), for m ≥ 0"]
def awayGradingEquivSectionsTwist (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℕ) :
    awayGrading 𝒜 d hf m ≃+
      (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  ((awayGradingEquivAwayPiece 𝒜 d hf m).trans (awayPieceEquivAwayGrading 𝒜 d hf m)).trans
    (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd (m : ℤ)).symm

/-- The degree-`m` summand of `(B[1/σ f · ψ f])₀` is the module of sections of the twisting
sheaf `𝒪_P(m)` over `D₊(f)`, for every integer `m`. -/
@[stacks 0EKG "the degree-m summand of the functions on the punctured cone over D₊(f) is the \
module of sections of O_P(m) over D₊(f), for every integer m"]
def puncturedGradingEquivSectionsTwist (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℤ) :
    puncturedGrading 𝒜 d hf m ≃+
      (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  (puncturedGradingEquivAwayGrading 𝒜 d hf m).trans
    (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m).symm

/-- `⨁_{m ≥ 0} (A[1/f])_m = ⨁_{m ≥ 0} Γ(D₊(f), 𝒪_P(m))`: the direct sum of the degree
pieces of `(B[1/ψ f])₀` is the direct sum of the sections of the nonnegative twisting sheaves over
`D₊(f)`, summand by summand. -/
def awayDirectSumEquivSectionsTwist (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (⨁ m : ℕ, ↥(awayGrading 𝒜 d hf m)) ≃+
      (⨁ m : ℕ, ↥((twistingSheaf 𝒜 (m : ℤ)).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) :=
  DFinsupp.mapRange.addEquiv fun m => awayGradingEquivSectionsTwist 𝒜 d hf hd m

/-- `⨁_{m ∈ ℤ} (A[1/f])_m = ⨁_{m ∈ ℤ} Γ(D₊(f), 𝒪_P(m))`: the direct sum of the degree pieces
of `(B[1/σ f · ψ f])₀` is the direct sum of the sections of all the twisting sheaves over `D₊(f)`,
summand by summand. -/
def puncturedDirectSumEquivSectionsTwist (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (⨁ m : ℤ, ↥(puncturedGrading 𝒜 d hf m)) ≃+
      (⨁ m : ℤ, ↥((twistingSheaf 𝒜 m).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) :=
  DFinsupp.mapRange.addEquiv fun m => puncturedGradingEquivSectionsTwist 𝒜 d hf hd m

end Sections

end Stacks.Truncation

end
