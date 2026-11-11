module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksCore.RingTheory.Localization.Ideal
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Relative height and catenary rings and spaces

For prime ideals `q ≤ p` of a commutative ring `A`, the *relative height* of `p` over `q` is
the height of `p/q` in `A/q`. It is computed by two localizations: it is the Krull dimension of
`Aₚ/qAₚ`, which is proved below, and it is the Krull dimension of `(A/q)_(p/q)`, which is
Mathlib's `IsLocalization.AtPrime.ringKrullDim_eq_height`. The two localizations of `A/q`
appearing in the source are the same localization, because localizing at `p` inverts the image
of `A \ p`, the complement of `p/q`.

A Noetherian ring is *catenary* in the sense of the source when relative heights are additive
along chains `p₁ ≤ p₂ ≤ p₃` of primes; this is `Ring.IsHeightCatenary`, stated with Mathlib's
`Ideal.height` of the images `p.map (Ideal.Quotient.mk q)`. The chain form of catenarity,
Stacks' other definition, is `Ring.IsCatenary`; the two agree for Noetherian rings
(`Ring.isHeightCatenary_iff_isCatenary`), which is the exercise following the definition in the
source. A topological space is catenary when saturated chains of irreducible closed subsets
between two of them exist and all have the same length; this is
`TopologicalSpace.IsTopologicallyCatenary`.

The comparison goes through the order `Set.Ici q` of primes containing `q`: the height of `p/q`
in `A/q` is the height of `p` in `Set.Ici q` (`Ideal.height_map_mk_eq_height_Ici`), and the
height of `p` there is the supremum of the lengths of the chains of primes from `q` to `p`.

## Main results

* `Ideal.ringKrullDim_quotient_localization_eq_height_map`: the Krull dimension of `Aₚ/qAₚ` is
  the height of `p/q`.
* `Ring.IsHeightCatenary`: catenarity of a ring by additivity of relative heights.
* `Ring.isHeightCatenary_iff_isCatenary`: for a Noetherian ring this is `Ring.IsCatenary`.

## References

* [Stacks Project, Tag 027O](https://stacks.math.columbia.edu/tag/027O)
-/

@[expose] public section

add_to_stacks 027O "relative_height" IsLocalization.AtPrime.ringKrullDim_eq_height
add_to_ega "0 16.1.3" "dim(A_p) = ht(p)" IsLocalization.AtPrime.ringKrullDim_eq_height
add_to_ega "0 16.3.1" "more general" IsLocalization.AtPrime.ringKrullDim_eq_height
add_to_stacks 027O "space_catenary" TopologicalSpace.IsTopologicallyCatenary

namespace Ideal

/-- For `q ≤ p` with `p` prime, the Krull dimension of `Aₚ/qAₚ` is the height of the prime
ideal `p/q` of `A/q`. -/
@[stacks 027O "relative_height", ega "0 16.1.3" "(16.1.3.2)", ega "0 16.3.1" "more general"]
theorem ringKrullDim_quotient_localization_eq_height_map
    {A : Type*} [CommRing A] (q p : Ideal A) [p.IsPrime] (hqp : q ≤ p) :
    ringKrullDim
        (Localization.AtPrime p ⧸ q.map (algebraMap A (Localization.AtPrime p))) =
      ((p.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) := by
  let pbar := p.map (Ideal.Quotient.mk q)
  let : pbar.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  let : pbar.LiesOver p := ⟨by
    change p = pbar.comap (algebraMap A (A ⧸ q))
    simp [pbar, Ideal.Quotient.algebraMap_eq, Ideal.comap_map_mk hqp]⟩
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (A ⧸ q) p.primeCompl) (Localization.AtPrime pbar) := by
    rw [Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective pbar p
      Ideal.Quotient.mk_surjective]
    infer_instance
  rw [← ringKrullDim_eq_of_ringEquiv (IsLocalization.quotientEquiv p.primeCompl q
    (Localization.AtPrime p) (Localization.AtPrime pbar)).toRingEquiv]
  simpa [pbar] using
    (IsLocalization.AtPrime.ringKrullDim_eq_height pbar (Localization.AtPrime pbar))

end Ideal


namespace Stacks.Exercises.Catenary

open Order

variable {α : Type*} [PartialOrder α]

/-- A chain from `q` to `p` has length at most the height of `p` in `Set.Ici q`. -/
theorem length_le_height_Ici {q p : α} (h : q ≤ p) (s : LTSeries α) (hs : s.head = q)
    (hl : s.last = p) : (s.length : ℕ∞) ≤ height (⟨p, h⟩ : Set.Ici q) := by
  subst hs hl
  exact length_le_height_last
    (p := (⟨s.length, fun i => ⟨s i, s.head_le i⟩, fun i => s.step i⟩ : LTSeries (Set.Ici s.head)))

/-- If the height of `p` in `Set.Ici q` is `n`, some chain from `q` to `p` has length `n`. -/
theorem exists_series_of_height_Ici_eq {q p : α} (h : q ≤ p) {n : ℕ}
    (hn : height (⟨p, h⟩ : Set.Ici q) = n) :
    ∃ s : LTSeries α, s.head = q ∧ s.last = p ∧ s.length = n := by
  obtain ⟨t, ht, hl⟩ := exists_series_of_height_eq_coe _ hn
  refine ⟨t.map Subtype.val (Subtype.strictMono_coe _), ?_, by simp [ht], by simp [hl]⟩
  have h0 : t.toFun 0 = ⊥ := by
    simpa using height_eq_index_of_length_eq_height_last (p := t) (by rw [ht, hn, hl]) 0
  change ((t.toFun 0 : Set.Ici q) : α) = q
  rw [h0]
  rfl

/-- The least element `q` of `Set.Ici q` has height `0`. -/
theorem height_Ici_self (q : α) : height (⟨q, le_rfl⟩ : Set.Ici q) = 0 :=
  height_eq_zero.mpr fun y _ => y.2

/-- If `p` covers `q`, then `p` has height `1` in `Set.Ici q`. -/
theorem height_Ici_of_covBy {q p : α} (h : q ⋖ p) : height (⟨p, h.le⟩ : Set.Ici q) = 1 := by
  apply le_antisymm
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, height_le_coe_iff]
    intro y hy
    have hyq : (y : α) = q := by
      by_contra hne
      exact h.2 (lt_of_le_of_ne y.2 (Ne.symm hne)) hy
    have : height y = 0 := height_eq_zero.mpr fun z _ => by
      change (y : α) ≤ z
      rw [hyq]
      exact z.2
    rw [this]
    exact zero_lt_one
  · have := height_add_one_le (show (⟨q, le_rfl⟩ : Set.Ici q) < ⟨p, h.le⟩ from h.lt)
    simpa [height_Ici_self] using this

/-- A chain from `q` to `p` whose length is the height of `p` in `Set.Ici q` is saturated. -/
theorem covBy_of_length_eq_height_Ici {q p : α} (h : q ≤ p) (s : LTSeries α) (hs : s.head = q)
    (hl : s.last = p) (hlen : (s.length : ℕ∞) = height (⟨p, h⟩ : Set.Ici q))
    (i : Fin s.length) : s i.castSucc ⋖ s i.succ := by
  refine ⟨s.step i, fun c hc₁ hc₂ => ?_⟩
  let t := s.insertNth i c hc₁ hc₂
  have ht₀ : t.head = q := by
    rw [← hs]
    change Fin.insertNth (α := fun _ => α) (Fin.castSucc i.succ) c s.toFun 0 = s.toFun 0
    rw [← Fin.succAbove_ne_zero_zero (Fin.castSucc_pos (Fin.succ_pos i)).ne',
      Fin.insertNth_apply_succAbove]
  have ht₁ : t.last = p := by
    rw [← hl]
    change Fin.insertNth (α := fun _ => α) (Fin.castSucc i.succ) c s.toFun
      (Fin.last (s.length + 1)) = s.toFun (Fin.last s.length)
    rw [← Fin.succAbove_ne_last_last (Fin.castSucc_lt_last _).ne,
      Fin.insertNth_apply_succAbove]
  have := length_le_height_Ici h t ht₀ ht₁
  rw [← hlen] at this
  have htl : t.length = s.length + 1 := rfl
  rw [htl] at this
  norm_cast at this
  omega

/-- In a partial order in which every height in an upper interval `Set.Ici q` is finite, the
heights in upper intervals are additive along chains `p₁ ≤ p₂ ≤ p₃` if and only if every pair
`p ≤ q` has bounded chains between them and all saturated chains from `p` to `q` have the same
length. -/
theorem height_Ici_add_iff {α : Type*} [PartialOrder α]
    (hfin : ∀ (q p : α) (h : q ≤ p), height (⟨p, h⟩ : Set.Ici q) ≠ ⊤) :
    (∀ (p₁ p₂ p₃ : α) (h₁₂ : p₁ ≤ p₂) (h₂₃ : p₂ ≤ p₃),
        height (⟨p₃, h₁₂.trans h₂₃⟩ : Set.Ici p₁) =
          height (⟨p₃, h₂₃⟩ : Set.Ici p₂) + height (⟨p₂, h₁₂⟩ : Set.Ici p₁)) ↔
      ∀ p q : α, p ≤ q →
        (∃ N : ℕ, ∀ s : LTSeries α, s.head = p → s.last = q → s.length ≤ N) ∧
        ∃ n : ℕ, ∀ s : LTSeries α, s.head = p → s.last = q →
          (∀ i : Fin s.length, s i.castSucc ⋖ s i.succ) → s.length = n := by
  constructor
  · intro hadd p q hpq
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfin p q hpq)
    refine ⟨⟨m, fun s hs hl => ?_⟩, m, fun s hs hl hsat => ?_⟩
    · exact_mod_cast (length_le_height_Ici hpq s hs hl).trans hm.symm.le
    · subst hs hl
      have key : ∀ (k : ℕ) (hk : k < s.length + 1),
          height (⟨s ⟨k, hk⟩, s.head_le _⟩ : Set.Ici s.head) = k := by
        intro k
        induction k with
        | zero => intro hk; exact height_Ici_self s.head
        | succ k ih =>
          intro hk
          have e₁ : height (⟨s ⟨k + 1, hk⟩, (hsat ⟨k, by omega⟩).le⟩ :
              Set.Ici (s ⟨k, by omega⟩)) = 1 := height_Ici_of_covBy (hsat ⟨k, by omega⟩)
          rw [hadd s.head (s ⟨k, by omega⟩) (s ⟨k + 1, hk⟩) (s.head_le _)
            (hsat ⟨k, by omega⟩).le, e₁, ih (by omega)]
          push_cast
          ring
      have hm' : (m : ℕ∞) = s.length := hm.trans (key s.length (by omega))
      exact_mod_cast hm'.symm
  · intro hcat p₁ p₂ p₃ h₁₂ h₂₃
    have hsat : ∀ (q p : α) (h : q ≤ p), ∃ s : LTSeries α, s.head = q ∧ s.last = p ∧
        (s.length : ℕ∞) = height (⟨p, h⟩ : Set.Ici q) ∧
        ∀ i : Fin s.length, s i.castSucc ⋖ s i.succ := by
      intro q p h
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfin q p h)
      obtain ⟨s, hs, hl, hlen⟩ := exists_series_of_height_Ici_eq h hm.symm
      have hlen' : (s.length : ℕ∞) = height (⟨p, h⟩ : Set.Ici q) := by rw [hlen, hm]
      exact ⟨s, hs, hl, hlen', covBy_of_length_eq_height_Ici h s hs hl hlen'⟩
    obtain ⟨a, ha₀, ha₁, ha, hasat⟩ := hsat p₁ p₂ h₁₂
    obtain ⟨b, hb₀, hb₁, hb, hbsat⟩ := hsat p₂ p₃ h₂₃
    obtain ⟨c, hc₀, hc₁, hc, hcsat⟩ := hsat p₁ p₃ (h₁₂.trans h₂₃)
    obtain ⟨n, hn⟩ := (hcat p₁ p₃ (h₁₂.trans h₂₃)).2
    let a' : RelSeries {(x, y) : α × α | x ⋖ y} := ⟨a.length, a, hasat⟩
    let b' : RelSeries {(x, y) : α × α | x ⋖ y} := ⟨b.length, b, hbsat⟩
    have hcon : a'.last = b'.head := ha₁.trans hb₀.symm
    let t := covToLT (a'.smash b' hcon)
    have ht₀ : t.head = p₁ := by
      rw [covToLT_head, RelSeries.head_smash]
      exact ha₀
    have ht₁ : t.last = p₃ := by
      change (a'.smash b' hcon).last = p₃
      rw [RelSeries.last_smash]
      exact hb₁
    have hstep : ∀ i : Fin t.length, t i.castSucc ⋖ t i.succ := fun i =>
      (a'.smash b' hcon).step i
    have ht : t.length = n := hn t ht₀ ht₁ hstep
    have htlen : t.length = a.length + b.length := rfl
    have hcn : c.length = n := hn c hc₀ hc₁ hcsat
    rw [← hc, ← ha, ← hb, hcn, ← ht, htlen]
    push_cast
    exact add_comm _ _

end Stacks.Exercises.Catenary

namespace Ideal

open Order

/-- For primes `q ≤ p` of `A`, the height of `p/q` in `A/q` is the height of `p` in the order
`Set.Ici q` of primes containing `q`. -/
theorem height_map_mk_eq_height_Ici {A : Type*} [CommRing A] {q p : PrimeSpectrum A}
    (h : q ≤ p) :
    (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).height = Order.height (⟨p, h⟩ : Set.Ici q) := by
  let e : PrimeSpectrum (A ⧸ q.asIdeal) ≃o Set.Ici q :=
    q.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.trans
      (Set.orderIsoOfEq _ _ (Set.ext fun _ => Iff.rfl))
  rw [← height_orderIso e.symm]
  exact PrimeSpectrum.height_eq_orderHeight (e.symm ⟨p, h⟩)

end Ideal

namespace Ring

/-- A ring `A` is **catenary** in the sense of relative heights if for all primes
`p₁ ⊆ p₂ ⊆ p₃` the height of `p₃/p₁` in `A/p₁` is the sum of the height of `p₃/p₂` in `A/p₂`
and the height of `p₂/p₁` in `A/p₁`. The source defines this for Noetherian rings; the condition
is stated here for any commutative ring, and for Noetherian rings it agrees with the chain
condition `Ring.IsCatenary` (`Ring.isHeightCatenary_iff_isCatenary`). -/
@[stacks 027O "ring_catenary"]
def IsHeightCatenary (A : Type*) [CommRing A] : Prop :=
  ∀ p₁ p₂ p₃ : Ideal A, p₁.IsPrime → p₂.IsPrime → p₃.IsPrime → p₁ ≤ p₂ → p₂ ≤ p₃ →
    (p₃.map (Ideal.Quotient.mk p₁)).height =
      (p₃.map (Ideal.Quotient.mk p₂)).height + (p₂.map (Ideal.Quotient.mk p₁)).height

open Order in
/-- For a Noetherian ring, catenarity by additivity of relative heights agrees with catenarity
by chains of primes: chains between two primes are bounded and all saturated ones have the same
length. -/
@[stacks 0CT5]
theorem isHeightCatenary_iff_isCatenary (A : Type*) [CommRing A] [IsNoetherianRing A] :
    IsHeightCatenary A ↔ IsCatenary A := by
  have hfin : ∀ (q p : PrimeSpectrum A) (h : q ≤ p), height (⟨p, h⟩ : Set.Ici q) ≠ ⊤ := by
    intro q p h
    have h₁ := height_le_height_apply_of_strictMono _ (Subtype.strictMono_coe _)
      ⟨p, h⟩
    have h₂ : height p ≠ ⊤ := by
      rw [← PrimeSpectrum.height_eq_orderHeight]
      exact Ideal.height_ne_top_of_isPrime
    exact ne_top_of_le_ne_top h₂ h₁
  rw [IsCatenary, ← Stacks.Exercises.Catenary.height_Ici_add_iff hfin]
  constructor
  · intro hA p₁ p₂ p₃ h₁₂ h₂₃
    have := hA _ _ _ p₁.2 p₂.2 p₃.2 h₁₂ h₂₃
    rwa [Ideal.height_map_mk_eq_height_Ici (h₁₂.trans h₂₃), Ideal.height_map_mk_eq_height_Ici h₂₃,
      Ideal.height_map_mk_eq_height_Ici h₁₂] at this
  · intro hA p₁ p₂ p₃ hp₁ hp₂ hp₃ h₁₂ h₂₃
    let P₁ : PrimeSpectrum A := ⟨p₁, hp₁⟩
    let P₂ : PrimeSpectrum A := ⟨p₂, hp₂⟩
    let P₃ : PrimeSpectrum A := ⟨p₃, hp₃⟩
    have H₁₂ : P₁ ≤ P₂ := h₁₂
    have H₂₃ : P₂ ≤ P₃ := h₂₃
    have := hA P₁ P₂ P₃ H₁₂ H₂₃
    rw [← Ideal.height_map_mk_eq_height_Ici (H₁₂.trans H₂₃),
      ← Ideal.height_map_mk_eq_height_Ici H₂₃, ← Ideal.height_map_mk_eq_height_Ici H₁₂] at this
    exact this

end Ring

end
