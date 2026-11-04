module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.Finset.Order
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.AffineBlowup.ChartEquiv
public import StacksFrontier.RingTheory.AffineBlowup.DirectedSystem
public import StacksFrontier.RingTheory.Blowup.StrictTransform

/-!
# Rescaling the pair of an affine blowup chart

Let `R` be a domain with fraction field `K`, `I` an ideal of `R`, `a ∈ I` and `x ∈ R` nonzero.
The affine blowup charts of `(I, a)` and of `(xI, xa)`, with `xI` realized as
`Ideal.span {x} * I`, are the same subring `R[I/a] = R[(xI)/(xa)]` of `K`. Hence rescaling
preserves the nonzero-fibre condition and admissibility, the rescaled admissible chart has the
same ring as the original one, and its denominator `xa` is divisible by `x`.

## Main definitions

* `Stacks.AffineBlowup.AdmissibleChart.rescale`: the admissible chart of `(xI, xa)`.

## Main results

* `Stacks.AffineBlowup.affineBlowupImage_rescale`: for `x ≠ 0`, `R[(xI)/(xa)] = R[I/a]` as
  subrings of `K`.
* `Stacks.AffineBlowup.fibreNonzero_rescale`: rescaling preserves the nonzero-fibre condition.
* `Stacks.AffineBlowup.isAdmissiblePair_rescale`: rescaling preserves admissibility.
* `Stacks.AffineBlowup.AdmissibleChart.subring_rescale`: the rescaled chart has the same ring.
* `Stacks.AffineBlowup.mem_torsion'_powers_of_smul_eq_zero`: an element killed by `x` is
  `(xa)`-power torsion.
* `Stacks.AffineBlowup.exists_chart_forall_mem`: finitely many elements of the valuation ring
  come from a single admissible chart.

## References

* [Stacks Project, Tag 053I](https://stacks.math.columbia.edu/tag/053I)
* [Stacks Project, Tag 052M](https://stacks.math.columbia.edu/tag/052M)
-/


@[expose] public section

namespace Stacks.AffineBlowup

variable {R : Type*} [CommRing R] {I : Ideal R} {a x : R}

/-! ### The rescaled pair -/

/-- The rescaled denominator lies in the rescaled ideal: `x * a ∈ (x) * I` whenever
`a ∈ I`. -/
theorem mul_mem_span_singleton_mul (x a : R) (I : Ideal R) (ha : a ∈ I) :
    x * a ∈ Ideal.span {x} * I :=
  Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) ha

/-- Powers of a rescaled ideal: `((x) * I)ⁿ = (xⁿ) * Iⁿ`. -/
theorem span_singleton_mul_pow (x : R) (I : Ideal R) (n : ℕ) :
    (Ideal.span {x} * I) ^ n = Ideal.span {x ^ n} * I ^ n := by
  rw [mul_pow, Ideal.span_singleton_pow]

/-! ### The chart is unchanged by rescaling -/

section FractionField

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The rescale lemma.** For a nonzero `x` in a ring `R` with fraction field `K`, the
affine blowup chart of the rescaled pair `((x) * I, x * a)` is equal, as a subring of `K`, to
the chart of `(I, a)`. -/
theorem affineBlowupImage_rescale (hx : x ≠ 0) (ha : a ∈ I)
    (hxa : x * a ∈ Ideal.span {x} * I) :
    (affineBlowupImage (Ideal.span {x} * I) (x * a) hxa : Subring K)
      = affineBlowupImage I a ha := by
  have hxK : algebraMap R K x ≠ 0 := mt IsFractionRing.to_map_eq_zero_iff.mp hx
  have hxa' (n : ℕ) : algebraMap R K (x * a) ^ n = algebraMap R K a ^ n * algebraMap R K x ^ n := by
    rw [map_mul, mul_pow, mul_comm]
  have hxw (n : ℕ) (w : R) :
      algebraMap R K (x ^ n * w) = algebraMap R K w * algebraMap R K x ^ n := by
    rw [map_mul, map_pow, mul_comm]
  ext y
  constructor
  · rintro ⟨n, z, hz, hyz⟩
    rw [span_singleton_mul_pow] at hz
    obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.mp hz
    refine ⟨n, w, hw, mul_right_cancel₀ (pow_ne_zero n hxK) ?_⟩
    rw [mul_assoc, ← hxa', hyz, hxw]
  · rintro ⟨n, w, hw, hyw⟩
    refine ⟨n, x ^ n * w, ?_, ?_⟩
    · rw [span_singleton_mul_pow]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hw
    · rw [hxa', ← mul_assoc, hyw, hxw]

/-- For a nonzero `x`, the affine blowup chart of `((x) * I, x * a)` is equal, as an
`R`-subalgebra of `K`, to the chart of `(I, a)`. -/
theorem affineBlowupImageAlg_rescale (hx : x ≠ 0) (ha : a ∈ I)
    (hxa : x * a ∈ Ideal.span {x} * I) :
    affineBlowupImageAlg (K := K) (Ideal.span {x} * I) (x * a) hxa
      = affineBlowupImageAlg I a ha :=
  Subalgebra.toSubring_injective <| by
    rw [affineBlowupImageAlg_toSubring, affineBlowupImageAlg_toSubring,
      affineBlowupImage_rescale hx ha hxa]

end FractionField

/-! ### Transport of the nonzero-fibre condition -/

/-- **The nonzero-fibre condition survives rescaling.** For `R` a local domain, `x ≠ 0`
and `a ∈ I`, if the fibre ring of `R → R[I/a]` at `𝔪` is nonzero then so is that of
`R → R[(xI)/(xa)]`. -/
theorem fibreNonzero_rescale [IsDomain R] [IsLocalRing R] (hx : x ≠ 0) (ha : a ∈ I)
    (hxa : x * a ∈ Ideal.span {x} * I) (h : FibreNonzero ha) : FibreNonzero hxa := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact not_fibreNonzero_of_zero I ha h
  have : Fact (a ∈ I) := ⟨ha⟩
  have : Fact (x * a ∈ Ideal.span {x} * I) := ⟨hxa⟩
  have e : Blowup (Ideal.span {x} * I) (x * a) ≃ₐ[R] Blowup I a :=
    (blowupEquivAffineBlowupImage' (K := FractionRing R) (mul_ne_zero hx ha0)).trans
      (((Subalgebra.equivOfEq _ _
            (affineBlowupImageAlg_rescale (K := FractionRing R) hx ha hxa))).trans
        (blowupEquivAffineBlowupImage' (K := FractionRing R) ha0).symm)
  exact (fibreNonzero_iff (I := Ideal.span {x} * I) (a := x * a)).mpr fun htop ↦
    fibreNonzero_iff.mp h ((map_algebraMap_eq_top_iff e (IsLocalRing.maximalIdeal R)).mpr htop)

/-! ### Transport of admissibility, and the rescaled chart -/

section Admissible

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Admissibility survives rescaling.** If `(I, a)` is an admissible pair for the
valuation subring `A` and `x ≠ 0`, then so is `((x) * I, x * a)`. -/
theorem isAdmissiblePair_rescale [IsDomain R] [IsLocalRing R] (A : ValuationSubring K)
    (hx : x ≠ 0) (ha : a ∈ I) (hxa : x * a ∈ Ideal.span {x} * I)
    (h : IsAdmissiblePair R A I a ha) :
    IsAdmissiblePair R A (Ideal.span {x} * I) (x * a) hxa := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨Ideal.mul_le_right.trans h1, (Submodule.fg_span_singleton x).mul h2,
    fibreNonzero_rescale hx ha hxa h3, ?_⟩
  rwa [affineBlowupImage_rescale hx ha hxa]

namespace AdmissibleChart

variable {A : ValuationSubring K}

/-- **The rescaled chart.** The admissible chart obtained from an admissible chart by
multiplying both its ideal and its denominator by a nonzero `x ∈ R`. -/
def rescale [IsDomain R] [IsLocalRing R] (c : AdmissibleChart R A) (hx : x ≠ 0) :
    AdmissibleChart R A where
  I := Ideal.span {x} * c.I
  a := x * c.a
  ha := mul_mem_span_singleton_mul x c.a c.I c.ha
  adm := isAdmissiblePair_rescale A hx c.ha (mul_mem_span_singleton_mul x c.a c.I c.ha) c.adm

/-- **The rescaled chart has the same ring** as the original chart. -/
@[simp] theorem subring_rescale [IsDomain R] [IsLocalRing R] (c : AdmissibleChart R A)
    (hx : x ≠ 0) : (c.rescale hx).subring = c.subring :=
  affineBlowupImage_rescale hx c.ha (c.rescale hx).ha

/-- The original chart is below its rescaling in the preorder of charts. -/
theorem le_rescale [IsDomain R] [IsLocalRing R] (c : AdmissibleChart R A) (hx : x ≠ 0) :
    c ≤ c.rescale hx :=
  le_iff_subring_le.mpr (subring_rescale c hx).ge

/-- The rescaling of a chart is below the original chart in the preorder of charts. -/
theorem rescale_le [IsDomain R] [IsLocalRing R] (c : AdmissibleChart R A) (hx : x ≠ 0) :
    c.rescale hx ≤ c :=
  le_iff_subring_le.mpr (subring_rescale c hx).le

end AdmissibleChart

/-! ### Finitely many elements of the valuation ring come from one chart -/

/-- **A finite family of elements of the valuation ring is carried by a single chart.**
For `(R, 𝔪)` a local domain with `𝔪 ≠ 0` and `A` a valuation subring of `K` dominating
`R`, every finite set of elements of `A` lies in the image of one admissible chart. -/
theorem exists_chart_forall_mem [IsDomain R] [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (A : ValuationSubring K) (hdom : Dominates R A)
    (s : Finset (valRing A)) :
    ∃ c : AdmissibleChart R A, ∀ α ∈ s, ∃ y : chartRing c, chartToVal c y = α := by
  classical
  have : Nonempty (AdmissibleChart R A) :=
    AdmissibleChart.nonempty_of_maximalIdeal_ne_bot hm hdom
  have : IsDirected (AdmissibleChart R A) (· ≤ ·) :=
    AdmissibleChart.isDirected_of_dominates hdom
  choose f y hy using chartToVal_surjective hm A hdom
  obtain ⟨c, hc⟩ := (s.image f).exists_le
  exact ⟨c, fun α hα ↦ ⟨chartMap (f α) c (hc (f α) (Finset.mem_image_of_mem f hα)) (y α),
    by rw [chartToVal_chartMap, hy α]⟩⟩

end Admissible

/-! ### Torsion for the rescaled denominator -/

/-- **Anything killed by `x` is `(xa)`-power torsion.** For an `R`-algebra `B` and a
`B`-module `N`, if the image of `x` in `B` annihilates `t : N`, then so does the first
power of the image of `x * a`, so `t` lies in the submonoid-torsion submodule for the
powers of the image of `x * a`. -/
theorem mem_torsion'_powers_of_smul_eq_zero {B : Type*} [CommRing B] [Algebra R B]
    {N : Type*} [AddCommGroup N] [Module B N] (a : R) {x : R} {t : N}
    (ht : algebraMap R B x • t = 0) :
    t ∈ Submodule.torsion' B N (Submonoid.powers (algebraMap R B (x * a))) := by
  refine ⟨⟨_, 1, rfl⟩, ?_⟩
  show algebraMap R B (x * a) ^ 1 • t = 0
  rw [pow_one, map_mul, mul_comm (algebraMap R B x), mul_smul, ht, smul_zero]

/-- An element of `R[(xI)/(xa)] ⊗[R] M` killed by the image of `x` lies in the submodule
`strictTransform.torsionSubmodule ((x) * I) (x * a) M` of `(xa)`-power torsion, which dies in the
strict transform `strictTransform ((x) * I) (x * a) M` of Stacks 053H. -/
theorem mem_torsionSubmodule_of_smul_eq_zero [Fact (x * a ∈ Ideal.span {x} * I)]
    {M : Type*} [AddCommGroup M] [Module R M]
    {t : TensorProduct R (Blowup (Ideal.span {x} * I) (x * a)) M}
    (ht : algebraMap R (Blowup (Ideal.span {x} * I) (x * a)) x • t = 0) :
    t ∈ strictTransform.torsionSubmodule (Ideal.span {x} * I) (x * a) M :=
  mem_torsion'_powers_of_smul_eq_zero a ht

end Stacks.AffineBlowup
