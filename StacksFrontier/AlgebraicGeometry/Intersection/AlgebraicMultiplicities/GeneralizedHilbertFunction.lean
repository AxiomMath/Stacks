module

public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.QuotientAnnihilator
public import StacksFrontier.RingTheory.HilbertSamuel.Function
public import StacksFrontier.RingTheory.Support.Basic
public import StacksFrontier.RingTheory.Support.Finite
public import Mathlib.Topology.JacobsonSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generalized Hilbert function

For a finite module `M` over a Noetherian local ring, if `M / IM` has finite length then the
lengths of all the quotients `M / I ^ n M` are finite: the support of `M / I ^ n M` is
contained in that of `M / IM`, which consists of closed points. The length of each quotient
is the sum of the lengths of the successive layers of the `I`-adic filtration.

## Main definitions

* `Ideal.generalizedHilbertFunction` is the length of `M / I ^ n M`.

## Main results

* `Ideal.generalizedHilbertFunction_lt_top` gives finite values under the finite-length
  condition of Tag 0B00.
* `Ideal.generalizedHilbertFunction_eq_sum` expresses each value as a sum of lengths of the
  successive quotients.

## Implementation notes

The function takes values in `ℕ∞`, Mathlib's type of module lengths. Under the stated
finite-length condition, every value lies below `⊤` and therefore represents an ordinary
natural number. The filtration identity itself holds without finiteness hypotheses. The
generalized multiplicities referred to in the source are
`Ideal.generalizedHilbertSamuelMultiplicity`.

## References

* [Stacks Project, Tag 0B00](https://stacks.math.columbia.edu/tag/0B00)
-/

@[expose] public section

namespace Ideal

/-- A prime lies in the support of `R ⧸ I` exactly when it contains `I`. -/
private lemma mem_support_quotient_iff_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (q : PrimeSpectrum R) : q ∈ Module.support R (R ⧸ I) ↔ I ≤ q.asIdeal := by
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  exact PrimeSpectrum.mem_zeroLocus _ _

/-- A module of finite length over a Noetherian ring has support contained in the closed
points. -/
private lemma support_subset_closedPoints_of_isFiniteLength
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    Module.support R M ⊆ closedPoints (PrimeSpectrum R) := by
  induction h with
  | of_subsingleton =>
      rw [Module.support_eq_empty_iff.mpr inferInstance]
      exact Set.empty_subset _
  | @of_simple_quotient N _ _ S _ _ ih =>
      obtain ⟨p, hp, ⟨e⟩⟩ :=
        isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule R (N ⧸ S))
      have hquot : Module.support R (R ⧸ p) = {⟨p, hp.isPrime⟩} := by
        ext q
        rw [mem_support_quotient_iff_le, Set.mem_singleton_iff]
        exact ⟨fun hq => PrimeSpectrum.ext (hp.eq_of_le q.isPrime.ne_top hq).symm,
          fun hq => hq ▸ le_rfl⟩
      have hsupp : Module.support R N = Module.support R S ∪ {⟨p, hp.isPrime⟩} := by
        rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ S)
          (Submodule.subtype_injective S) (Submodule.mkQ_surjective S),
          e.support_eq, hquot]
      rw [hsupp]
      exact Set.union_subset ih (by
        rintro q rfl
        exact mem_closedPoints_iff.mpr
          ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hp))

/-- A finite module over a Noetherian ring whose support consists of closed points has finite
length: a prime filtration of it has only simple factors. -/
@[sga "6 X 1.1.2" "affine case"]
private lemma isFiniteLength_of_support_subset_closedPoints
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : Module.support R M ⊆ closedPoints (PrimeSpectrum R)) : IsFiniteLength R M := by
  obtain ⟨s, hhead, hlast⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  have key : ∀ (t : RelSeries {(N₁, N₂) : Submodule R M × Submodule R M |
      N₁.IsQuotientEquivQuotientPrime N₂}),
      t.head = ⊥ → IsFiniteLength R ↥t.last := by
    intro t
    induction t using RelSeries.inductionOn' with
    | singleton x =>
        intro hx
        rw [RelSeries.head_singleton] at hx
        rw [RelSeries.last_singleton, hx]
        exact IsFiniteLength.of_subsingleton
    | snoc t' x htx ih =>
        intro hhd
        rw [RelSeries.head_snoc] at hhd
        rw [RelSeries.last_snoc]
        obtain ⟨hle, q, ⟨e⟩⟩ := htx
        have hqmem : q ∈ Module.support R M := by
          have hquot : q ∈ Module.support R (↥x ⧸ t'.last.submoduleOf x) := by
            rw [e.support_eq, mem_support_quotient_iff_le]
          exact Module.support_subset_of_injective x.subtype x.subtype_injective
            (Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _) hquot)
        have hmax : q.asIdeal.IsMaximal :=
          (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
            (mem_closedPoints_iff.mp (h hqmem))
        have : IsSimpleModule R (R ⧸ q.asIdeal) :=
          isSimpleModule_iff_quot_maximal.mpr
            ⟨q.asIdeal, hmax, ⟨LinearEquiv.refl R (R ⧸ q.asIdeal)⟩⟩
        have : IsSimpleModule R (↥x ⧸ t'.last.submoduleOf x) := IsSimpleModule.congr e
        exact IsFiniteLength.of_simple_quotient
          ((Submodule.submoduleOfEquivOfLe hle).symm.isFiniteLength (ih hhd))
  exact Submodule.topEquiv.isFiniteLength (hlast ▸ key s hhead)

/-- If `M / IM` has finite length, so does every `M / I ^ n M`: their supports agree, because
a prime containing `I ^ n` contains `I`. -/
private lemma finite_length_quotient_pow_smul_top
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (I : Ideal R)
    (hIM : Module.length R (M ⧸ I • (⊤ : Submodule R M)) < ⊤)
    (n : ℕ) : IsFiniteLength R (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by simp
    exact IsFiniteLength.of_subsingleton
  · have hpow : I ^ n ≤ I := Ideal.pow_le_self hn
    have hsupp : Module.support R (M ⧸ (I ^ n • (⊤ : Submodule R M))) ⊆
        Module.support R (M ⧸ (I • (⊤ : Submodule R M))) := by
      rw [Module.support_quotient, Module.support_quotient]
      rintro q ⟨hqM, hqpow⟩
      exact ⟨hqM, q.isPrime.le_of_pow_le hqpow⟩
    exact isFiniteLength_of_support_subset_closedPoints (hsupp.trans
      (support_subset_closedPoints_of_isFiniteLength
        (Module.length_ne_top_iff.mp (ne_of_lt hIM))))

/-- The generalized Hilbert function `χ_{I,M}(n) = length_R(M / I^n M)`. -/
@[stacks 0B00 "generalized_hilbert_function"]
noncomputable def generalizedHilbertFunction
    {R : Type*} [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ∞ :=
  Module.length R (M ⧸ (I ^ n • (⊤ : Submodule R M)))

/-- If `M / IM` has finite length, then so does `M / I^n M` for every `n`. -/
@[stacks 0B00 "generalized_hilbert_function"]
theorem generalizedHilbertFunction_lt_top
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R)
    (hIM : Module.length R (M ⧸ I • (⊤ : Submodule R M)) < ⊤)
    (n : ℕ) : Ideal.generalizedHilbertFunction I M n < ⊤ := by
  rw [Ideal.generalizedHilbertFunction]
  exact (Module.length_ne_top_iff.mpr (finite_length_quotient_pow_smul_top I hIM n)).lt_top

/-- The length of `M / I^n M` is the sum of the lengths of its successive `I`-adic layers,
including the empty sum when `n = 0`. -/
@[stacks 0B00 "generalized_hilbert_function"]
theorem generalizedHilbertFunction_eq_sum
    {R : Type*} [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Ideal.generalizedHilbertFunction I M n =
      ∑ p ∈ Finset.range n,
        Module.length R
          (↥(I ^ p • (⊤ : Submodule R M)) ⧸
            (I ^ (p + 1) • (⊤ : Submodule R M)).submoduleOf
              (I ^ p • (⊤ : Submodule R M))) := by
  induction n with
  | zero => simp [Ideal.generalizedHilbertFunction]
  | succ n ih =>
      have hUV : I ^ (n + 1) • (⊤ : Submodule R M) ≤ I ^ n • (⊤ : Submodule R M) :=
        Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl
      rw [Ideal.generalizedHilbertFunction]
      rw [show Module.length R (M ⧸ I ^ (n + 1) • (⊤ : Submodule R M)) =
          Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
            (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf _) +
          Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M)) from
        length_quotient_add_of_le hUV,
        ← Ideal.generalizedHilbertFunction, ih, Finset.sum_range_succ]
      rw [add_comm]

end Ideal
