module

public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.RingTheory.Sequence.Powers

/-!
# Colon ideals of powers of a regular sequence

Let `R` be a Noetherian local ring, `M` a finite `R`-module and `x₁, …, x_c` an `M`-regular
sequence in the maximal ideal of `R`. For every `e ≥ 0`,

`(x₁^{e+1}, …, x_c^{e+1})M :_M (x₁ ⋯ x_c)^e = (x₁, …, x_c)M`,

the inclusion `⊇` being clear. This is the injectivity of the transition maps
`M/(x^{e+1})M ⟶ M/(x^{e+2})M`, multiplication by `x₁ ⋯ x_c`, in the direct system whose colimit
is the top local cohomology `H^c_{(x)}(M)`; equivalently, the class of `m/(x₁ ⋯ x_c)` in the
top cohomology of the extended alternating Čech complex vanishes only when `m ∈ (x)M`.

## Main results

* `RingTheory.Sequence.IsWeaklyRegular.mem_ofList_smul_top_of_prod_pow_smul_mem`: the inclusion
  `⊆` above.

## Implementation notes

The proof is by induction on the sequence, peeling off its first member `r`. Over a Noetherian
local ring a regular sequence in the maximal ideal stays regular after any permutation, so
`rs, r` is regular; raising the members of `rs` to the power `e + 1` keeps it regular
([Stacks, Tag 07DV]), so `r` is a nonzerodivisor modulo `N = (rs^{e+1})M`. From
`r^e y ∈ r^{e+1}M + N` this gives `y ∈ rM + N`, and the induction hypothesis applies to `M/rM`.

## References

* [Stacks Project, Tag 07DV](https://stacks.math.columbia.edu/tag/07DV)
-/

@[expose] public section

open RingTheory.Sequence IsLocalRing
open scoped Pointwise

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R]

/-- Raising the members of a list to the same power is taking powers member by member against a
constant list of exponents. -/
private theorem zipWith_pow_replicate (rs : List R) (k : ℕ) :
    rs.zipWith (· ^ ·) (List.replicate rs.length k) = rs.map (· ^ k) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [List.replicate_succ, ih]

/-- In a Noetherian local ring, if `r :: rs` is a regular sequence in the maximal ideal on a
finite module `M`, then `r` is a nonzerodivisor on `M` modulo the `(e + 1)`-st powers of `rs`. -/
private theorem isSMulRegular_quot_pow [IsLocalRing R] [IsNoetherianRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] {r : R} {rs : List R}
    (h : IsRegular M (r :: rs)) (e : ℕ) :
    IsSMulRegular (M ⧸ (Ideal.ofList (rs.map (· ^ (e + 1))) • ⊤ : Submodule R M)) r := by
  have hperm : IsRegular M (rs ++ [r]) :=
    IsLocalRing.isRegular_of_perm h (List.perm_append_singleton r rs).symm
  have hpow : IsRegular M ((rs ++ [r]).zipWith (· ^ ·)
      (List.replicate rs.length (e + 1) ++ [1])) :=
    (isRegular_zipWith_pow_iff M (by simp) (by
      intro k hk
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hk
      omega)).2 hperm
  rw [List.zipWith_append (by simp), zipWith_pow_replicate] at hpow
  have h2 := ((isWeaklyRegular_append_iff M _ _).1 hpow.toIsWeaklyRegular).2
  simpa using (isWeaklyRegular_singleton_iff _ _).1 (by simpa using h2)

/-- **The colon ideal of the powers of a regular sequence by the power of its product.** Let
`R` be a Noetherian local ring, `M` a finite `R`-module, and `x₁, …, x_c` an `M`-regular
sequence in the maximal ideal. If `(x₁ ⋯ x_c)^e • m ∈ (x₁^{e+1}, …, x_c^{e+1})M` then
`m ∈ (x₁, …, x_c)M`. -/
theorem IsWeaklyRegular.mem_ofList_smul_top_of_prod_pow_smul_mem [IsLocalRing R]
    [IsNoetherianRing R] {rs : List R} (hmax : ∀ r ∈ rs, r ∈ maximalIdeal R) (e : ℕ) :
    ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M], IsWeaklyRegular M rs →
      ∀ {x : M}, rs.prod ^ e • x ∈ (Ideal.ofList (rs.map (· ^ (e + 1))) • ⊤ : Submodule R M) →
        x ∈ (Ideal.ofList rs • ⊤ : Submodule R M) := by
  induction rs with
  | nil =>
    intro M _ _ _ _ x hx
    simpa using hx
  | cons r rs ih =>
    intro M _ _ _ hreg x hx
    rcases subsingleton_or_nontrivial M with hM | hM
    · rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
    have hmax' : ∀ a ∈ rs, a ∈ maximalIdeal R := fun a ha => hmax a (List.mem_cons_of_mem r ha)
    have hregS : IsRegular M (r :: rs) :=
      (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmax).2 hreg
    set N : Submodule R M := Ideal.ofList (rs.map (· ^ (e + 1))) • ⊤ with hN
    have hr : IsSMulRegular (M ⧸ N) r := isSMulRegular_quot_pow hregS e
    obtain ⟨y, hy⟩ : ∃ y : M, y = rs.prod ^ e • x := ⟨_, rfl⟩
    -- `r ^ e • y ∈ r ^ (e + 1) • M + N`
    have hy1 : r ^ e • y ∈ r ^ (e + 1) • (⊤ : Submodule R M) ⊔ N := by
      have : (r :: rs).prod ^ e • x = r ^ e • y := by
        rw [hy, List.prod_cons, mul_pow, mul_smul]
      rw [List.map_cons, Ideal.ofList_cons_smul] at hx
      rw [← this, hN]
      exact hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy1
    obtain ⟨z, -, rfl⟩ : ∃ z ∈ (⊤ : Submodule R M), r ^ (e + 1) • z = a := by
      simpa [Submodule.mem_smul_pointwise_iff_exists] using ha
    -- hence `y - r • z ∈ N`
    have hyz : y - r • z ∈ N := by
      have hq : r ^ e • (Submodule.Quotient.mk (p := N) (y - r • z)) = r ^ e • 0 := by
        rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        have : r ^ e • (y - r • z) = b := by
          rw [smul_sub, smul_smul, ← pow_succ, ← hab]
          abel
        rwa [this]
      exact (Submodule.Quotient.mk_eq_zero N).1 ((hr.pow e) hq)
    -- pass to `M ⧸ r M`
    have hreg' : IsWeaklyRegular (QuotSMulTop r M) rs :=
      ((isWeaklyRegular_cons_iff M r rs).1 hreg).2
    set π := (r • (⊤ : Submodule R M)).mkQ with hπ
    have hmapN : N.map π ≤ (Ideal.ofList (rs.map (· ^ (e + 1))) • ⊤ :
        Submodule R (QuotSMulTop r M)) := by
      rw [hN, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    have hxq : rs.prod ^ e • π x ∈ (Ideal.ofList (rs.map (· ^ (e + 1))) • ⊤ :
        Submodule R (QuotSMulTop r M)) := by
      refine hmapN ⟨y - r • z, hyz, ?_⟩
      have hz0 : π (r • z) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_pointwise_smul z r ⊤ trivial)
      rw [map_sub, hz0, sub_zero, hy, map_smul]
    have hx' := ih hmax' hreg' hxq
    -- lift back to `M`
    have hle : (Ideal.ofList rs • ⊤ : Submodule R (QuotSMulTop r M)).comap π ≤
        Ideal.ofList (r :: rs) • (⊤ : Submodule R M) := by
      intro w hw
      have hw' : π w ∈ (Ideal.ofList rs • ⊤ : Submodule R M).map π := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hw
      obtain ⟨v, hv, hvw⟩ := hw'
      have hdiff : w - v ∈ r • (⊤ : Submodule R M) := by
        rw [← Submodule.ker_mkQ (r • (⊤ : Submodule R M)), LinearMap.mem_ker, map_sub, ← hπ,
          hvw, sub_self]
      rw [Ideal.ofList_cons_smul]
      have : w = (w - v) + v := by abel
      rw [this]
      exact Submodule.add_mem_sup (by
        simpa [Submodule.ideal_span_singleton_smul] using hdiff) hv
    exact hle hx'

end RingTheory.Sequence

end
