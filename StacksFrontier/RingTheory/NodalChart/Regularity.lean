module

public import StacksFrontier.RingTheory.NodalChart.Blowup
public import StacksFrontier.RingTheory.Derivation.Regularity
import all StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.AlgebraicGeometry.Properties.RegularLocus
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Regularity of the standard nodal model `R[x, y]/(xy - πⁿ)`

Over a discrete valuation ring `R` with uniformizer `π` the standard nodal model
`R[x, y]/(xy - πⁿ)` is regular exactly when `n ≤ 1`. The threshold is the origin, the closed
point cut out by `(π, x, y)`: the nodal equation `xy - πⁿ` lies in the square of that maximal
ideal precisely when `n ≥ 2`, and away from the origin one of the two partial derivatives of the
equation is invertible.

The two halves are proved from one criterion for a hypersurface quotient `A ⧸ (f)` of a regular
ring, applied at each prime: the quotient of a regular local ring by a nonzerodivisor `f` is
regular when `f ∉ 𝔪²` and is *never* regular when `f ∈ 𝔪²`. The second direction is the
embedding-dimension count in the form that avoids computing either side: cutting by an element of
`𝔪²` cannot lower the minimal number of generators of the maximal ideal (Nakayama), while it does
lower the Krull dimension by one.

## Main results

* `Stacks.spanFinrank_maximalIdeal_le_of_ker_le_sq` — a surjection of local rings whose kernel
  lies in `𝔪²` does not decrease the minimal number of generators of the maximal ideal.
* `Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq` — a regular local ring cut by
  a nonzerodivisor inside `𝔪²` is not regular.
* `Stacks.notMem_sq_of_derivation` — the derivation criterion for `f ∉ 𝔪ₚ²`.
* `Stacks.isRegularRing_quotient_span_singleton_of_forall_notMem_sq` and
  `Stacks.not_isRegular_spec_quotient_span_singleton_of_mem_sq` — the two directions of the
  hypersurface criterion, the second stated for the affine scheme.
* `Stacks.nodalOriginIdeal` and `Stacks.isMaximal_nodalOriginIdeal` — the origin `(π, x, y)`.
* `Stacks.isRegularRing_nodalChartRing` — `R[x, y]/(xy - π)` is a regular ring.
* `Stacks.isRegular_spec_nodalChartRing_pow_one` — the standard model with exponent one is a
  regular scheme.
* `Stacks.not_isRegular_spec_nodalChartRing_pow_of_one_lt` — the standard model with exponent
  greater than one is not.
* `Stacks.isRegular_spec_nodalXChart`, `Stacks.isRegular_spec_nodalYChart` — the two outer charts
  of the blowup at the origin are regular, because they are the exponent one model.

## Implementation notes

The regularity criterion is applied prime by prime. For a prime `p` of `R[x, y]` containing
`xy - πⁿ` there are three cases. If `x ∉ p` or `y ∉ p` then `∂/∂y` resp. `∂/∂x` sends the
equation outside `p`, and a derivation taking a value outside `p` certifies `f ∉ 𝔪ₚ²`; this is
where the exponent plays no role. If both `x ∈ p` and `y ∈ p` then `π ∈ p` as well, so `p`
contains — hence, the origin ideal being maximal, equals — `(π, x, y)`. There the computation is
the only place the uniformizer is used: `π ∉ 𝔪²` because evaluation of both coordinates at zero
carries `(π, x, y)` into `(π)` and is the exact preimage of `(π)`, so a relation `s·π ∈ (π, x, y)²`
with `s ∉ (π, x, y)` would give `π ∈ (π²)` in `R`.

For `n ≥ 2` the equation lies in the square of the origin ideal, which is what the negative
direction consumes; the scheme-level statement is obtained at the point of `Spec` given by the
image of the origin, whose stalk is the localization by
`AlgebraicGeometry.StructureSheaf.stalkIso`.

The localization plumbing — that `Localization.AtPrime q` of `A ⧸ (f)` is the quotient of
`Localization.AtPrime p` by `(f)`, for `p` the contraction of `q` — is shared by both directions
and isolated in a private lemma.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 07PF](https://stacks.math.columbia.edu/tag/07PF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing MvPolynomial

universe u

namespace Stacks

/-! ### Minimal numbers of generators under a quotient -/

private theorem nakayama_maximalIdeal_le {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {N : Ideal A} (h : maximalIdeal A ≤ N ⊔ maximalIdeal A ^ 2) :
    maximalIdeal A ≤ N := by
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
  refine h.trans (sup_le_sup_left (le_of_eq ?_) N)
  rw [Ideal.smul_eq_mul, pow_two]

/-- **Cutting by an element of `𝔪²` does not lower the embedding dimension.** If the kernel of a
surjection of local rings is contained in the square of the maximal ideal, then the minimal
number of generators of the maximal ideal does not drop. -/
public theorem spanFinrank_maximalIdeal_le_of_ker_le_sq
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ maximalIdeal A ^ 2) :
    (maximalIdeal A).spanFinrank ≤ (maximalIdeal B).spanFinrank := by
  classical
  let _ := IsLocalHom.of_surjective φ hφ
  let _ : IsNoetherianRing B := isNoetherianRing_of_surjective A B φ hφ
  obtain ⟨t, htcard, htspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsNoetherian.noetherian (maximalIdeal B))
  obtain ⟨s, hscard, hs⟩ :
      ∃ s : Finset A, s.card ≤ t.card ∧ φ '' (↑s : Set A) = (↑t : Set B) := by
    refine ⟨t.image (Function.surjInv hφ), Finset.card_image_le, ?_⟩
    rw [Finset.coe_image, ← Set.image_comp]
    exact (Set.image_congr' (fun b ↦ Function.surjInv_eq hφ b)).trans (Set.image_id _)
  obtain ⟨N, hN⟩ : ∃ N : Ideal A, N = Ideal.span (↑s : Set A) := ⟨_, rfl⟩
  have hmapN : Ideal.map φ N = maximalIdeal B := by
    rw [hN, Ideal.map_span, hs]
    exact htspan
  have hmA : Ideal.comap φ (maximalIdeal B) = maximalIdeal A := maximalIdeal_comap φ
  have hcomap : N ⊔ RingHom.ker φ = maximalIdeal A := by
    rw [← hmA, ← hmapN, Ideal.comap_map_of_surjective φ hφ]
    rfl
  have hNle : N ≤ maximalIdeal A := le_sup_left.trans hcomap.le
  have hsup : maximalIdeal A ≤ N ⊔ maximalIdeal A ^ 2 :=
    hcomap.ge.trans (sup_le le_sup_left (hker.trans le_sup_right))
  have heq : maximalIdeal A = N := le_antisymm (nakayama_maximalIdeal_le hsup) hNle
  calc (maximalIdeal A).spanFinrank
      = (Ideal.span (↑s : Set A)).spanFinrank := by rw [heq, hN]
    _ ≤ (↑s : Set A).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet
    _ = s.card := Set.ncard_coe_finset _
    _ ≤ t.card := hscard
    _ = (maximalIdeal B).spanFinrank := htcard

/-- **A regular local ring cut by a nonzerodivisor inside `𝔪²` is not regular.** The quotient has
Krull dimension one less, while its maximal ideal needs at least as many generators. -/
public theorem not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    {A : Type u} [CommRing A] [IsRegularLocalRing A] {x : A}
    (hnzd : x ∈ nonZeroDivisors A) (hx2 : x ∈ maximalIdeal A ^ 2) :
    ¬ IsRegularLocalRing (A ⧸ Ideal.span {x}) := by
  intro hreg
  have hx : x ∈ maximalIdeal A := Ideal.pow_le_self two_ne_zero hx2
  let _ : Nontrivial (A ⧸ Ideal.span {x}) := nontrivial_quotient_span_singleton hx
  let _ : IsLocalRing (A ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {x})) ≤ maximalIdeal A ^ 2 := by
    rw [Ideal.mk_ker, Ideal.span_le]
    simpa using hx2
  have hsf := spanFinrank_maximalIdeal_le_of_ker_le_sq
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective hker
  have hdim : ringKrullDim (A ⧸ Ideal.span {x}) + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hx
  have hA : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) = ringKrullDim A :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hB : ((maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
      = ringKrullDim (A ⧸ Ideal.span {x}) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hcast : (((maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞)
      = (((maximalIdeal A).spanFinrank : ℕ) : WithBot ℕ∞) := by
    push_cast
    rw [hA, hB, hdim]
  have hnat : (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank + 1
      = (maximalIdeal A).spanFinrank := by exact_mod_cast hcast
  omega

/-! ### The hypersurface criterion -/

/-- **The derivation criterion for `f ∉ 𝔪ₚ²`.** If some derivation sends `f` outside the prime
`p`, then the image of `f` in the localization at `p` is not in the square of the maximal
ideal. -/
public theorem notMem_sq_of_derivation {R : Type u} [CommRing R] {f : R} {p : Ideal R}
    [p.IsPrime] (D : Derivation ℤ R R) (hD : D f ∉ p) :
    algebraMap R (Localization.AtPrime p) f ∉
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  intro hsq
  have hunit : IsUnit (algebraMap R (Localization.AtPrime p) (D f)) :=
    IsLocalization.map_units _ (⟨D f, hD⟩ : p.primeCompl)
  have hmem := derivation_mem_of_mem_sq
    (Stacks.DerivationExtension.locDeriv D p.primeCompl (Localization.AtPrime p)) hsq
  rw [Stacks.DerivationExtension.locDeriv_algebraMap] at hmem
  exact (mem_maximalIdeal _).mp hmem hunit

/-- The localization of `R ⧸ (f)` at a prime `q` is the quotient of the localization of `R` at
the contraction of `q` by the image of `(f)`. -/
private theorem isLocalization_quotient_atPrime
    {R : Type u} [CommRing R] (f : R) {p : Ideal R} [p.IsPrime]
    {q : Ideal (R ⧸ Ideal.span {f})} [q.IsPrime]
    (hpq : ∀ r : R, Ideal.Quotient.mk (Ideal.span {f}) r ∈ q ↔ r ∈ p) :
    IsLocalization q.primeCompl
      (Localization.AtPrime p ⧸
        (Ideal.span {f}).map (algebraMap R (Localization.AtPrime p))) := by
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {f}) p.primeCompl)
      (Localization.AtPrime p ⧸
        (Ideal.span {f}).map (algebraMap R (Localization.AtPrime p))) :=
    IsLocalization.of_surjective p.primeCompl (Localization.AtPrime p)
      (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
      (by
        intro a ha
        rw [Ideal.mk_ker] at ha ⊢
        exact ha)
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {f}) p.primeCompl = q.primeCompl := by
    ext y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨s, hs, heq⟩ hqr
      refine hs ((hpq s).mp ?_)
      show (algebraMap R (R ⧸ Ideal.span {f})) s ∈ q
      rw [heq]
      exact hqr
    · intro hr
      exact ⟨r, fun hrp ↦ hr ((hpq r).mpr hrp), rfl⟩
  rwa [hsub] at hloc

/-- The quotient of the localization of `R` at `p` by the image of `f` is regular local exactly when
the localization of `R ⧸ (f)` at a prime `q` over `p` is. -/
private theorem isRegularLocalRing_quotient_atPrime_iff
    {R : Type u} [CommRing R] (f : R) {p : Ideal R} [p.IsPrime]
    {q : Ideal (R ⧸ Ideal.span {f})} [q.IsPrime]
    (hpq : ∀ r : R, Ideal.Quotient.mk (Ideal.span {f}) r ∈ q ↔ r ∈ p) :
    IsRegularLocalRing
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap R (Localization.AtPrime p) f}) ↔
      IsRegularLocalRing (Localization.AtPrime q) := by
  have _ := isLocalization_quotient_atPrime f hpq
  have hJ : (Ideal.span {f}).map (algebraMap R (Localization.AtPrime p))
      = Ideal.span {algebraMap R (Localization.AtPrime p) f} := by
    simp [Ideal.map_span]
  rw [← hJ]
  have e := (IsLocalization.algEquiv q.primeCompl
    (Localization.AtPrime p ⧸ (Ideal.span {f}).map (algebraMap R (Localization.AtPrime p)))
    (Localization.AtPrime q)).toRingEquiv
  exact ⟨fun _ ↦ IsRegularLocalRing.of_ringEquiv e, fun _ ↦ IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- **The Jacobian criterion for a hypersurface, in the form `f ∉ 𝔪ₚ²`.** If for every prime `p`
of a regular ring containing `f` the image of `f` avoids the square of the maximal ideal of the
localization, then `R ⧸ (f)` is a regular ring. -/
public theorem isRegularRing_quotient_span_singleton_of_forall_notMem_sq
    {R : Type u} [CommRing R] [IsRegularRing R] (f : R)
    (h : ∀ (p : Ideal R) [p.IsPrime], f ∈ p →
      algebraMap R (Localization.AtPrime p) f ∉
        maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularRing (R ⧸ Ideal.span {f}) := by
  rw [isRegularRing_iff]
  intro q hq
  let p : Ideal R := q.comap (Ideal.Quotient.mk (Ideal.span {f}))
  have hp : p.IsPrime := Ideal.IsPrime.comap _
  let _ : p.IsPrime := hp
  have hf : f ∈ p := by
    show Ideal.Quotient.mk (Ideal.span {f}) f ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
    exact q.zero_mem
  have hx : algebraMap R (Localization.AtPrime p) f
      ∈ maximalIdeal (Localization.AtPrime p) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]
    exact Ideal.mem_map_of_mem _ hf
  exact (isRegularLocalRing_quotient_atPrime_iff (p := p) (q := q) f fun _ ↦ Iff.rfl).mp
    (Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton hx
      (h p hf))

/-- `Spec` of a regular ring is a regular scheme. -/
public theorem isRegular_spec_of_isRegularRing (A : Type u) [CommRing A] [IsRegularRing A] :
    IsRegular (Spec (CommRingCat.of A)) := fun _ ↦
  ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm⟩

/-- On a regular affine scheme every localization of the ring is a regular local ring. -/
public theorem isRegularLocalRing_localization_of_isRegular_spec {A : Type u} [CommRing A]
    (p : Ideal A) [p.IsPrime] (h : IsRegular (Spec (CommRingCat.of A))) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let x : PrimeSpectrum (CommRingCat.of A) := ⟨p, inferInstance⟩
  let _ : IsRegularLocalRing
      ↑((structurePresheafInCommRingCat (CommRingCat.of A)).stalk x) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk h x
  exact IsRegularLocalRing.of_ringEquiv
    (StructureSheaf.stalkIso (CommRingCat.of A) x).toRingEquiv.symm

/-- **The converse half of the hypersurface criterion.** If `f` is a nonzerodivisor of a regular
ring lying in the square of the maximal ideal of some localization, then `Spec (R ⧸ (f))` is not
a regular scheme: it is singular at the point cut out by that prime. -/
public theorem not_isRegular_spec_quotient_span_singleton_of_mem_sq
    {R : Type u} [CommRing R] [IsRegularRing R] {f : R} (p : Ideal R) [p.IsPrime]
    (hnzd : algebraMap R (Localization.AtPrime p) f
      ∈ nonZeroDivisors (Localization.AtPrime p))
    (hsq : algebraMap R (Localization.AtPrime p) f
      ∈ maximalIdeal (Localization.AtPrime p) ^ 2) :
    ¬ IsRegular (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) := by
  intro hX
  have hf : f ∈ p := by
    by_contra hfp
    refine absurd hsq ?_
    have : IsUnit (algebraMap R (Localization.AtPrime p) f) :=
      IsLocalization.map_units _ (⟨f, hfp⟩ : p.primeCompl)
    exact fun hmem ↦ (mem_maximalIdeal _).mp (Ideal.pow_le_self two_ne_zero hmem) this
  have hkerle : RingHom.ker (Ideal.Quotient.mk (Ideal.span {f})) ≤ p := by
    rw [Ideal.mk_ker, Ideal.span_le]
    simpa using hf
  have hq : (p.map (Ideal.Quotient.mk (Ideal.span {f}))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerle
  let _ : (p.map (Ideal.Quotient.mk (Ideal.span {f}))).IsPrime := hq
  have hcomap : (p.map (Ideal.Quotient.mk (Ideal.span {f}))).comap
      (Ideal.Quotient.mk (Ideal.span {f})) = p := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_eq_left.mpr ?_
    rw [← RingHom.ker_eq_comap_bot]
    exact hkerle
  refine not_isRegularLocalRing_quotient_span_singleton_of_mem_sq hnzd hsq ?_
  exact (isRegularLocalRing_quotient_atPrime_iff (p := p)
    (q := p.map (Ideal.Quotient.mk (Ideal.span {f}))) f
    (fun r ↦ by rw [← Ideal.mem_comap, hcomap])).mpr
    (isRegularLocalRing_localization_of_isRegular_spec _ hX)

/-! ### The origin of the standard nodal model -/

variable {R : Type u} [CommRing R]

/-- Evaluation of both coordinates of `R[x, y]` at zero. -/
public def nodalEvalZero (R : Type u) [CommRing R] : MvPolynomial (Fin 2) R →+* R :=
  MvPolynomial.eval (fun _ ↦ 0)

@[simp] public theorem nodalEvalZero_C (r : R) : nodalEvalZero R (C r) = r := by
  simp [nodalEvalZero]

@[simp] public theorem nodalEvalZero_X (i : Fin 2) : nodalEvalZero R (X i) = 0 := by
  simp [nodalEvalZero]

public theorem surjective_nodalEvalZero : Function.Surjective (nodalEvalZero R) :=
  fun r ↦ ⟨C r, by simp⟩

private theorem sub_C_nodalEvalZero_mem (g : MvPolynomial (Fin 2) R) :
    g - C (nodalEvalZero R g) ∈
      Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) R)) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      have hpq : p + q - C (nodalEvalZero R (p + q))
          = (p - C (nodalEvalZero R p)) + (q - C (nodalEvalZero R q)) := by
        rw [map_add, map_add]
        ring
      rw [hpq]
      exact add_mem hp hq
  | mul_X p i hp =>
      have h0 : nodalEvalZero R (p * X i) = 0 := by simp [map_mul]
      rw [h0, map_zero, sub_zero]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- The ideal `(π, x, y)` of the origin of the standard nodal model. -/
public def nodalOriginIdeal (R : Type u) [CommRing R] (π : R) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span ({C π, X 0, X 1} : Set (MvPolynomial (Fin 2) R))

public theorem C_mem_nodalOriginIdeal (π : R) : C π ∈ nodalOriginIdeal R π :=
  Ideal.subset_span (Or.inl rfl)

public theorem X_mem_nodalOriginIdeal (π : R) (i : Fin 2) : X i ∈ nodalOriginIdeal R π := by
  refine Ideal.subset_span ?_
  fin_cases i
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The product of the two coordinates lies in the square of the origin ideal. -/
private theorem X_mul_X_mem_sq_nodalOriginIdeal (π : R) :
    (X 0 * X 1 : MvPolynomial (Fin 2) R) ∈ nodalOriginIdeal R π ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul (X_mem_nodalOriginIdeal π 0) (X_mem_nodalOriginIdeal π 1)

/-- Elements of the square of a prime stay in the square of the maximal ideal after localizing. -/
private theorem algebraMap_mem_sq_maximalIdeal {A : Type u} [CommRing A] {p : Ideal A}
    [p.IsPrime] {x : A} (hx : x ∈ p ^ 2) :
    algebraMap A (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) ^ 2 := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hx

/-- The origin ideal is the preimage of `(π)` under evaluation of the coordinates at zero. -/
public theorem nodalOriginIdeal_eq_comap (π : R) :
    nodalOriginIdeal R π = Ideal.comap (nodalEvalZero R) (Ideal.span {π}) := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun g hg ↦ ?_
  · rintro z (rfl | rfl | rfl)
    · simp
    · simp
    · simp
  · obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hg)
    have hC : C (nodalEvalZero R g) ∈ nodalOriginIdeal R π := by
      rw [← hr, map_mul]
      exact Ideal.mul_mem_left _ _ (C_mem_nodalOriginIdeal π)
    have hrest : g - C (nodalEvalZero R g) ∈ nodalOriginIdeal R π := by
      refine Ideal.span_mono ?_ (sub_C_nodalEvalZero_mem g)
      intro z hz
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    simpa using add_mem hC hrest

/-- The origin ideal is maximal as soon as `(π)` is maximal in `R`. -/
public theorem isMaximal_nodalOriginIdeal {π : R} (hπ : (Ideal.span {π}).IsMaximal) :
    (nodalOriginIdeal R π).IsMaximal := by
  rw [nodalOriginIdeal_eq_comap]
  have _ := hπ
  exact Ideal.comap_isMaximal_of_surjective _ surjective_nodalEvalZero

/-- **The uniformizer is not in the square of the origin ideal, after localizing there.** This is
the one step of the regularity proof that uses `π`. -/
public theorem C_notMem_sq_localization_nodalOriginIdeal [IsDomain R] {π : R} (hπ0 : π ≠ 0)
    [(nodalOriginIdeal R π).IsPrime] :
    algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime (nodalOriginIdeal R π)) (C π)
      ∉ maximalIdeal (Localization.AtPrime (nodalOriginIdeal R π)) ^ 2 := by
  intro hsq
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (nodalOriginIdeal R π), ← Ideal.map_pow,
    IsLocalization.algebraMap_mem_map_algebraMap_iff
      (nodalOriginIdeal R π).primeCompl] at hsq
  obtain ⟨s, hs, hmem⟩ := hsq
  have hmap : Ideal.map (nodalEvalZero R) (nodalOriginIdeal R π) ≤ Ideal.span {π} := by
    rw [Ideal.map_le_iff_le_comap, ← nodalOriginIdeal_eq_comap]
  have hsq2 : Ideal.map (nodalEvalZero R) (nodalOriginIdeal R π ^ 2)
      ≤ Ideal.span {π ^ 2} := by
    rw [Ideal.map_pow, ← Ideal.span_singleton_pow, pow_two, pow_two]
    exact Ideal.mul_mono hmap hmap
  have hev : nodalEvalZero R s * π ∈ Ideal.span {π ^ 2} := by
    have h1 := hsq2 (Ideal.mem_map_of_mem (nodalEvalZero R) hmem)
    rwa [map_mul, nodalEvalZero_C] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hev
  have hcancel : nodalEvalZero R s = π * c := by
    refine mul_left_cancel₀ hπ0 ?_
    linear_combination -hc
  refine hs ?_
  show s ∈ nodalOriginIdeal R π
  rw [nodalOriginIdeal_eq_comap, Ideal.mem_comap, hcancel]
  exact Ideal.mem_span_singleton'.2 ⟨c, mul_comm c π⟩

/-- **The nodal equation with exponent one is not in the square of the origin ideal**, after
localizing at the origin: the two coordinates contribute to the square, so this is the previous
statement about the uniformizer. -/
public theorem nodalEquation_notMem_sq_localization_nodalOriginIdeal [IsDomain R] {π : R}
    (hπ0 : π ≠ 0) [(nodalOriginIdeal R π).IsPrime] :
    algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime (nodalOriginIdeal R π)) (nodalEquation R π)
      ∉ maximalIdeal (Localization.AtPrime (nodalOriginIdeal R π)) ^ 2 := by
  intro hsq
  refine C_notMem_sq_localization_nodalOriginIdeal hπ0 ?_
  have hXX : algebraMap (MvPolynomial (Fin 2) R)
      (Localization.AtPrime (nodalOriginIdeal R π)) (X 0 * X 1)
      ∈ maximalIdeal (Localization.AtPrime (nodalOriginIdeal R π)) ^ 2 := by
    exact algebraMap_mem_sq_maximalIdeal (X_mul_X_mem_sq_nodalOriginIdeal π)
  have hCeq : algebraMap (MvPolynomial (Fin 2) R)
      (Localization.AtPrime (nodalOriginIdeal R π)) (C π)
      = algebraMap (MvPolynomial (Fin 2) R)
          (Localization.AtPrime (nodalOriginIdeal R π)) (X 0 * X 1)
        - algebraMap (MvPolynomial (Fin 2) R)
          (Localization.AtPrime (nodalOriginIdeal R π)) (nodalEquation R π) := by
    rw [nodalEquation_def, map_sub]
    ring
  rw [hCeq]
  exact sub_mem hXX hsq

/-! ### The nodal equation at a prime -/

/-- A prime containing the nodal equation and both coordinates contains the origin ideal. -/
public theorem nodalOriginIdeal_le_of_mem {π : R} {n : ℕ}
    {p : Ideal (MvPolynomial (Fin 2) R)} [hp : p.IsPrime]
    (hf : nodalEquation R (π ^ n) ∈ p)
    (hx0 : X 0 ∈ p) (hx1 : X 1 ∈ p) : nodalOriginIdeal R π ≤ p := by
  have hCpow : C (π ^ n) ∈ p := by
    have : (X 0 * X 1 : MvPolynomial (Fin 2) R) - nodalEquation R (π ^ n) = C (π ^ n) := by
      rw [nodalEquation_def]
      ring
    rw [← this]
    exact sub_mem (Ideal.mul_mem_right _ _ hx0) hf
  have hC : C π ∈ p := by
    refine hp.mem_of_pow_mem n ?_
    rwa [← map_pow]
  rw [nodalOriginIdeal, Ideal.span_le]
  rintro z (rfl | rfl | rfl)
  · exact hC
  · exact hx0
  · exact hx1

/-- For exponent at least two the nodal equation lies in the square of the origin ideal. -/
public theorem nodalEquation_mem_sq_nodalOriginIdeal (π : R) {n : ℕ} (hn : 2 ≤ n) :
    nodalEquation R (π ^ n) ∈ nodalOriginIdeal R π ^ 2 := by
  rw [nodalEquation_def]
  refine sub_mem ?_ ?_
  · exact X_mul_X_mem_sq_nodalOriginIdeal π
  · rw [map_pow]
    exact Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow (C_mem_nodalOriginIdeal π) n)

/-! ### Regularity of the standard model at exponent one -/

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **`R[x, y]/(xy - π)` is a regular ring** for `π` a uniformizer of a discrete valuation ring
`R`. -/
public theorem isRegularRing_nodalChartRing {π : R} (hπ : Irreducible π) :
    IsRegularRing (nodalChartRing R π) := by
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible hπ
  refine isRegularRing_quotient_span_singleton_of_forall_notMem_sq _ ?_
  intro p hp hfp
  by_cases hx0 : X 0 ∈ p
  · by_cases hx1 : X 1 ∈ p
    · have hle : nodalOriginIdeal R π ≤ p := by
        refine nodalOriginIdeal_le_of_mem (n := 1) ?_ hx0 hx1
        rwa [pow_one]
      have heq : nodalOriginIdeal R π = p :=
        (isMaximal_nodalOriginIdeal hmax).eq_of_le hp.ne_top hle
      subst heq
      exact nodalEquation_notMem_sq_localization_nodalOriginIdeal (R := R) hπ.ne_zero
    · refine notMem_sq_of_derivation
        ((MvPolynomial.pderiv (R := R) (0 : Fin 2)).restrictScalars ℤ) ?_
      show (MvPolynomial.pderiv (R := R) (0 : Fin 2)) (nodalEquation R π) ∉ p
      simpa [nodalEquation_def] using hx1
  · refine notMem_sq_of_derivation
      ((MvPolynomial.pderiv (R := R) (1 : Fin 2)).restrictScalars ℤ) ?_
    show (MvPolynomial.pderiv (R := R) (1 : Fin 2)) (nodalEquation R π) ∉ p
    simpa [nodalEquation_def] using hx0

/-- A scheme whose ring is isomorphic to the exponent one nodal model is regular. -/
private theorem isRegular_spec_of_ringEquiv_nodalChartRing {π : R} (hπ : Irreducible π)
    {T : Type u} [CommRing T] (e : T ≃+* nodalChartRing R π) :
    IsRegular (Spec (CommRingCat.of T)) := by
  have _ := isRegularRing_nodalChartRing hπ
  have _ : IsRegularRing T := IsRegularRing.of_ringEquiv e.symm
  exact isRegular_spec_of_isRegularRing _

/-- **The standard nodal model with exponent one is a regular scheme**: `Spec R[x, y]/(xy - π¹)`
is regular. This is the case `n = 1` of the standard model `Spec R[x, y]/(xy - πⁿ)`. -/
public theorem isRegular_spec_nodalChartRing_pow_one {π : R} (hπ : Irreducible π) :
    IsRegular (Spec (CommRingCat.of (nodalChartRing R (π ^ 1)))) := by
  rw [pow_one]
  exact isRegular_spec_of_ringEquiv_nodalChartRing hπ (RingEquiv.refl _)

/-- **The standard nodal model with exponent greater than one is not regular**: it is singular at
the origin. -/
public theorem not_isRegular_spec_nodalChartRing_pow_of_one_lt {π : R} (hπ : Irreducible π)
    {n : ℕ} (hn : 1 < n) :
    ¬ IsRegular (Spec (CommRingCat.of (nodalChartRing R (π ^ n)))) := by
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible hπ
  let _ : (nodalOriginIdeal R π).IsPrime := (isMaximal_nodalOriginIdeal hmax).isPrime
  have hπn : π ^ n ≠ 0 := pow_ne_zero n hπ.ne_zero
  have hne : nodalEquation R (π ^ n) ≠ 0 := (prime_nodalEquation hπn).ne_zero
  have hnzd : algebraMap (MvPolynomial (Fin 2) R)
      (Localization.AtPrime (nodalOriginIdeal R π)) (nodalEquation R (π ^ n))
      ∈ nonZeroDivisors (Localization.AtPrime (nodalOriginIdeal R π)) := by
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ hne ?_
    refine IsLocalization.injective (Localization.AtPrime (nodalOriginIdeal R π))
      (Ideal.primeCompl_le_nonZeroDivisors (nodalOriginIdeal R π)) ?_
    rw [h, map_zero]
  refine not_isRegular_spec_quotient_span_singleton_of_mem_sq (nodalOriginIdeal R π) hnzd ?_
  exact algebraMap_mem_sq_maximalIdeal (nodalEquation_mem_sq_nodalOriginIdeal π hn)

/-! ### The outer charts of the blowup at the origin -/

/-- **The `x`-chart of the blowup of the standard nodal model is regular.** It is the exponent one
model `R[x, u]/(xu - π)`, by `Stacks.nodalXChart_equiv`. -/
@[stacks 0CDC "the x-chart of X' is regular"]
public theorem isRegular_spec_nodalXChart {π : R} (hπ : Irreducible π) {n : ℕ} (hn : 2 ≤ n)
    (S : Type u) [CommRing S] [Algebra (nodalChartRing R (π ^ n)) S]
    [IsLocalization.Away (nodalGen R (π ^ n) 0) S] [Algebra R S]
    [IsScalarTower R (nodalChartRing R (π ^ n)) S] :
    IsRegular (Spec (CommRingCat.of ↥(nodalXChart π n S))) := by
  obtain ⟨e, -, -, -⟩ := nodalXChart_equiv π n S hπ.ne_zero hn
  exact isRegular_spec_of_ringEquiv_nodalChartRing hπ e

/-- **The `y`-chart of the blowup of the standard nodal model is regular.** -/
@[stacks 0CDC "the y-chart of X' is regular"]
public theorem isRegular_spec_nodalYChart {π : R} (hπ : Irreducible π) {n : ℕ} (hn : 2 ≤ n)
    (S : Type u) [CommRing S] [Algebra (nodalChartRing R (π ^ n)) S]
    [IsLocalization.Away (nodalGen R (π ^ n) 1) S] [Algebra R S]
    [IsScalarTower R (nodalChartRing R (π ^ n)) S] :
    IsRegular (Spec (CommRingCat.of ↥(nodalYChart π n S))) := by
  obtain ⟨e, -, -, -⟩ := nodalYChart_equiv π n S hπ.ne_zero hn
  exact isRegular_spec_of_ringEquiv_nodalChartRing hπ e

/-! ### Non-vacuity

The hypothesis set — a discrete valuation ring with an irreducible element — is inhabited by the
`2`-adic integers, and the two statements above are instantiated there. They have opposite
truth values at `n = 1` and `n = 2` over the *same* ring, so neither is vacuous and the exponent
threshold is a property of the models, not an artifact of the hypotheses. -/

/-- The standard nodal model `xy = 2` over the `2`-adic integers is a regular scheme. -/
public theorem isRegular_spec_nodalChartRing_padic_one :
    IsRegular (Spec (CommRingCat.of (nodalChartRing ℤ_[2] ((2 : ℤ_[2]) ^ 1)))) :=
  isRegular_spec_nodalChartRing_pow_one PadicInt.irreducible_p

/-- The predicted failure: the standard nodal model `xy = 4` over the `2`-adic integers is *not*
a regular scheme. Together with `Stacks.isRegular_spec_nodalChartRing_padic_one` this pins the
exponent threshold. -/
public theorem not_isRegular_spec_nodalChartRing_padic_two :
    ¬ IsRegular (Spec (CommRingCat.of (nodalChartRing ℤ_[2] ((2 : ℤ_[2]) ^ 2)))) :=
  not_isRegular_spec_nodalChartRing_pow_of_one_lt PadicInt.irreducible_p one_lt_two

end Stacks

end
