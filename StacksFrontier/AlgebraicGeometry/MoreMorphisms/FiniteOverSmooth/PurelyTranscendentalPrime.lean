module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFiniteAffineSpace

/-!
# The residue field of `(𝔭, X_i : i ∈ s)` in a polynomial ring

Let `A` be a commutative ring, `𝔭 ⊂ A` a prime and `s` a set of variables. This file identifies
the quotient of `A[X_ι]` by the ideal `𝔭 A[X_ι] + (X_i : i ∈ s)` with a polynomial ring over
`A/𝔭` in the remaining variables, and deduces that the ideal is prime, lies over `𝔭`, and that
its residue field is a purely transcendental extension of `κ(𝔭)`.

This is the residue-field input of Stacks 052E: the point of affine `n`-space through which a
finite type morphism is factored is the prime `(𝔭, x_{r+1}, …, x_n)` produced by Stacks 0520,
and the lemma below is what makes `κ` of that point purely transcendental over `κ(𝔭)`.

## Main results

* `purelyTranscendental_of_isFractionRing_mvPolynomial`: the fraction field of a polynomial ring
  over a domain `D` is purely transcendental over any fraction field of `D`.
* `MvPolynomial.comap_C_mapC_sup_span_X_image`: the ideal `𝔭 A[X_ι] + (X_i : i ∈ s)` contracts
  to `𝔭`.
* `MvPolynomial.isPrime_mapC_sup_span_X_image`: it is prime.
* `MvPolynomial.purelyTranscendental_residueField_mapC_sup_span_X_image`: its residue field is
  purely transcendental over `κ(𝔭)`.

## Implementation notes

The quotient is computed by the ring homomorphism `A[X_ι] → (A/𝔭)[X_i : i ∉ s]` which reduces
coefficients modulo `𝔭` and sets the variables in `s` to zero. Its kernel is computed in two
steps: the kernel of setting the variables of `s` to zero is the ideal they generate (proved
here, from `MvPolynomial.mem_ideal_span_X_image`), and the contraction of that ideal along the
reduction of coefficients is given by `MvPolynomial.comap_map_span_X_image`.

Pure transcendence is obtained by transporting the instance
`PurelyTranscendental k (MvRatFunc σ k)`: the polynomial ring over a fraction field `k` of `D`
is a localization of the polynomial ring over `D`, hence a fraction ring of the latter is also
a fraction ring of the former.

The statement about residue fields takes the `κ(𝔭)`-algebra structure on `κ(Q)` as a hypothesis,
together with its compatibility with the constants, so that the caller may use whichever
structure is at hand; `MvPolynomial.comap_C_mapC_sup_span_X_image` provides the equality of
ideals needed to build one with `Ideal.ResidueField.map`.

## References

* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
* [Stacks Project, Tag 0520](https://stacks.math.columbia.edu/tag/0520)
-/

@[expose] public section

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A fraction ring of `D[X_σ]` is purely transcendental over a fraction field `k` of the domain
`D`, provided the two maps from `D` agree. -/
theorem purelyTranscendental_of_isFractionRing_mvPolynomial
    {D k K : Type*} (σ : Type*) [CommRing D] [IsDomain D] [Field k] [Field K]
    [Algebra D k] [IsFractionRing D k]
    [Algebra (MvPolynomial σ D) K] [IsFractionRing (MvPolynomial σ D) K]
    [Algebra k K]
    (h : ∀ d : D, algebraMap k K (algebraMap D k d) =
      algebraMap (MvPolynomial σ D) K (MvPolynomial.C d)) :
    PurelyTranscendental k K := by
  let ψ : MvPolynomial σ k →ₐ[k] K := aeval fun i => algebraMap (MvPolynomial σ D) K (X i)
  let : Algebra (MvPolynomial σ k) K := ψ.toRingHom.toAlgebra
  have halg : algebraMap (MvPolynomial σ k) K = ψ.toRingHom := rfl
  have : IsScalarTower k (MvPolynomial σ k) K := .of_algebraMap_eq fun a => (ψ.commutes a).symm
  have : IsScalarTower (MvPolynomial σ D) (MvPolynomial σ k) K := by
    refine .of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun d => ?_) (fun i => ?_))
    · simpa [halg, ψ] using (h d).symm
    · simp [halg, ψ]
  have : IsLocalization ((nonZeroDivisors D).map (C (σ := σ))) (MvPolynomial σ k) :=
    MvPolynomial.isLocalization _ _
  have : IsFractionRing (MvPolynomial σ k) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      ((nonZeroDivisors D).map (C (σ := σ))) (MvPolynomial σ k) K
  exact ((IsLocalization.algEquiv (nonZeroDivisors (MvPolynomial σ k))
    (MvRatFunc σ k) K).restrictScalars k).purelyTranscendental

/-- A fraction field of a domain `R` is purely transcendental over a fraction field `k` of a
domain `D` as soon as `R` is isomorphic to a polynomial ring over `D`, compatibly with the two
maps from `D`. -/
theorem purelyTranscendental_of_ringEquiv_mvPolynomial
    {R D k K : Type*} (σ : Type*) [CommRing R] [CommRing D] [IsDomain D] [Field k] [Field K]
    [Algebra D k] [IsFractionRing D k] [Algebra R K] [IsFractionRing R K] [Algebra k K]
    (e : R ≃+* MvPolynomial σ D)
    (h : ∀ (x : R) (d : D), e x = MvPolynomial.C d →
      algebraMap k K (algebraMap D k d) = algebraMap R K x) :
    PurelyTranscendental k K := by
  let : Algebra (MvPolynomial σ D) K := ((algebraMap R K).comp e.symm.toRingHom).toAlgebra
  have : IsFractionRing (MvPolynomial σ D) K :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv K e).mp ‹_›
  exact purelyTranscendental_of_isFractionRing_mvPolynomial (D := D) σ fun d =>
    h (e.symm (MvPolynomial.C d)) d (e.apply_symm_apply _)

namespace MvPolynomial

variable {ι A : Type*} [CommRing A]

section Proj

variable {D : Type*} [CommRing D] (s : Set ι) [DecidablePred (· ∈ s)]

/-- Setting the variables indexed by `s` to zero. -/
private noncomputable def proj : MvPolynomial ι D →ₐ[D] MvPolynomial {i : ι // i ∉ s} D :=
  aeval fun i => if h : i ∈ s then 0 else X ⟨i, h⟩

private lemma proj_rename (q : MvPolynomial {i : ι // i ∉ s} D) :
    proj s (rename Subtype.val q) = q := by
  have h : ((fun i => if h : i ∈ s then 0 else X ⟨i, h⟩) ∘ (Subtype.val : _ → ι)) =
      (X : {i : ι // i ∉ s} → MvPolynomial {i : ι // i ∉ s} D) := by
    funext j
    simp [j.2]
  rw [proj, aeval_rename, h, aeval_X_left, AlgHom.id_apply]

private lemma proj_surjective : Function.Surjective (proj (D := D) s) :=
  fun q => ⟨rename Subtype.val q, proj_rename s q⟩

private lemma proj_monomial_eq_zero {m : ι →₀ ℕ} {i : ι} (hi : i ∈ s) (hmi : m i ≠ 0) (c : D) :
    proj s (monomial m c) = 0 := by
  rw [proj, aeval_monomial, Finsupp.prod,
    Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hmi) (by simp [hi, hmi]), mul_zero]

omit [DecidablePred (· ∈ s)] in
private lemma monomial_mem_range_rename {m : ι →₀ ℕ} (hm : ∀ i ∈ s, m i = 0) (c : D) :
    ∃ q, rename (Subtype.val : {i : ι // i ∉ s} → ι) q = monomial m c := by
  have hsub : (m.support : Set ι) ⊆ Set.range (Subtype.val : {i : ι // i ∉ s} → ι) :=
    fun i hi => ⟨⟨i, fun h => Finsupp.mem_support_iff.1 hi (hm i h)⟩, rfl⟩
  exact ⟨monomial (m.comapDomain _ Subtype.val_injective.injOn) c, by
    rw [rename_monomial, Finsupp.mapDomain_comapDomain _ Subtype.val_injective _ hsub]⟩

private lemma sub_rename_proj_mem (p : MvPolynomial ι D) :
    p - rename Subtype.val (proj s p) ∈ Ideal.span (X '' s : Set (MvPolynomial ι D)) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    by_cases hm : ∃ i ∈ s, m i ≠ 0
    · obtain ⟨i, hi, hmi⟩ := hm
      rw [proj_monomial_eq_zero s hi hmi, map_zero, sub_zero]
      refine MvPolynomial.mem_ideal_span_X_image.2 fun m' hm' => ?_
      obtain rfl : m' = m := by simpa using MvPolynomial.support_monomial_subset hm'
      exact ⟨i, hi, hmi⟩
    · push Not at hm
      obtain ⟨q, hq⟩ := monomial_mem_range_rename s hm c
      rw [← hq, proj_rename, sub_self]
      exact Ideal.zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq

private lemma ker_proj : RingHom.ker (proj (D := D) s).toRingHom =
    Ideal.span (X '' s : Set (MvPolynomial ι D)) := by
  refine le_antisymm (fun p hp => ?_) ?_
  · simpa [show proj s p = 0 from hp] using sub_rename_proj_mem s p
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp [RingHom.mem_ker, proj, hi]

end Proj

section Quotient

variable (P : Ideal A) (s : Set ι) [DecidablePred (· ∈ s)]

/-- Reduce the coefficients modulo `P` and set the variables indexed by `s` to zero. -/
private noncomputable def reduce :
    MvPolynomial ι A →+* MvPolynomial {i : ι // i ∉ s} (A ⧸ P) :=
  (proj s).toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk P))

private lemma reduce_surjective : Function.Surjective (reduce P s) :=
  (proj_surjective s).comp (map_surjective _ Ideal.Quotient.mk_surjective)

private lemma ker_reduce : RingHom.ker (reduce P s) =
    Ideal.map C P ⊔ Ideal.span (X '' s : Set (MvPolynomial ι A)) := by
  rw [reduce, ← RingHom.comap_ker, ker_proj, MvPolynomial.comap_map_span_X_image,
    Ideal.mk_ker]

private lemma reduce_C (a : A) : reduce P s (C a) = C (Ideal.Quotient.mk P a) := by
  rw [reduce, RingHom.comp_apply, map_C]
  exact (aeval_C _ _).trans rfl

end Quotient

variable (P : Ideal A) [P.IsPrime] (s : Set ι)

omit [P.IsPrime] in
/-- The ideal `𝔭 A[X_ι] + (X_i : i ∈ s)` contracts to `𝔭` along the constants. -/
theorem comap_C_mapC_sup_span_X_image :
    (Ideal.map C P ⊔ Ideal.span (X '' s : Set (MvPolynomial ι A))).comap
      (C : A →+* MvPolynomial ι A) = P := by
  classical
  ext a
  rw [Ideal.mem_comap, ← ker_reduce P s, RingHom.mem_ker, reduce_C, MvPolynomial.C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The ideal `𝔭 A[X_ι] + (X_i : i ∈ s)` is prime. -/
theorem isPrime_mapC_sup_span_X_image :
    (Ideal.map C P ⊔ Ideal.span (X '' s : Set (MvPolynomial ι A))).IsPrime := by
  classical
  rw [← ker_reduce P s, RingHom.ker_eq_comap_bot]
  exact Ideal.comap_isPrime _ _

/-- **The residue-field input of Stacks 052E.** The residue field of the prime
`𝔭 A[X_ι] + (X_i : i ∈ s)` is a purely transcendental extension of `κ(𝔭)`. The `κ(𝔭)`-algebra
structure is any one compatible with the constants. -/
theorem purelyTranscendental_residueField_mapC_sup_span_X_image
    (Q : Ideal (MvPolynomial ι A)) [Q.IsPrime]
    (hQ : Q = Ideal.map C P ⊔ Ideal.span (X '' s : Set (MvPolynomial ι A)))
    [Algebra P.ResidueField Q.ResidueField]
    (hcompat : ∀ a : A, algebraMap P.ResidueField Q.ResidueField
        (algebraMap A P.ResidueField a) =
      algebraMap (MvPolynomial ι A) Q.ResidueField (C a)) :
    PurelyTranscendental P.ResidueField Q.ResidueField := by
  classical
  have hker : RingHom.ker (reduce P s) = Q := by rw [ker_reduce P s, hQ]
  let e : (MvPolynomial ι A ⧸ Q) ≃+* MvPolynomial {i : ι // i ∉ s} (A ⧸ P) :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective (reduce_surjective P s))
  refine purelyTranscendental_of_ringEquiv_mvPolynomial _ e fun x d hx => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hep : e (Ideal.Quotient.mk Q p) = reduce P s p := by
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
  rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
    hcompat a]
  have hmem : C a - p ∈ Q := by
    rw [← hker, RingHom.mem_ker, map_sub, reduce_C P s a, ← hep, hx, sub_self]
  rw [← sub_eq_zero, ← map_sub]
  exact Ideal.algebraMap_residueField_eq_zero.2 hmem

end MvPolynomial
