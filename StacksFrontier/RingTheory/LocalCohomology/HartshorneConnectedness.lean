module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
import all StacksFrontier.RingTheory.Branches.Completion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hartshorne's connectedness lemma

Let `A` be a Noetherian local ring whose depth is at least two. Then the punctured spectrum
`Spec(A) ∖ {𝔪}` is connected.

The argument here is algebraic and uses the depth hypothesis through a single `A`-regular
sequence `x, y` of length two in `𝔪`. A disconnection of the punctured spectrum is cut out by
two ideals `I`, `J` with `I * J = 0` whose zero loci meet only at the closed point; both are
nonzero, and `√(I + J) = 𝔪`, so some power `𝔪 ^ n` lies in `I + J`. Writing `x ^ n = a + b` and
`y ^ n = c + d` along that decomposition, the vanishing of the cross terms `a * d` and `c * b`
gives `a * y ^ n = c * x ^ n`. Because `y` is a nonzerodivisor modulo `x`, that equation forces
`a ∈ x ^ n A`, say `a = x ^ n * e`; and `a ^ 2 = a * x ^ n`, which after cancelling the
nonzerodivisor `x ^ (2 * n)` says exactly that `e` is idempotent. A local ring has no
idempotents besides `0` and `1`, so `a = 0` or `b = 0`, i.e. `x ^ n` lies in `J` or in `I`.
Either way it annihilates the other ideal, which is therefore zero — a contradiction.

This is the first assertion of [Stacks, Lemma 0BLR]. That lemma also asserts the connectedness
of the punctured spectra of the henselization `A^h` and of the strict henselization `A^{sh}`,
which are separate statements.

## Main results

* `Stacks.PuncturedSpectrum.isPreconnected_of_two_le_depth` — the punctured spectrum of a
  Noetherian local ring of depth at least two is preconnected.
* `Stacks.PuncturedSpectrum.isConnected_of_two_le_depth` — it is connected, i.e. also nonempty.
* `Stacks.PuncturedSpectrum.isConnected_puncturedSpectrum_of_two_le_depth` — the same, in the
  complement-of-the-closed-point spelling the source uses.

## Implementation notes

The punctured spectrum is spelled
`{p : PrimeSpectrum A | p.asIdeal ≠ IsLocalRing.maximalIdeal A}`, the spelling used by
`not_isConnected_puncturedSpectrum_adicCompletion_iff_henselization`, so that the two compose
directly.

The extraction of the two ideals from a disconnection is the private
`exists_ideals_of_not_isPreconnected_puncturedSpectrum`, reached by `import all` rather than
re-proved. Divisibility by `x` is expressed as membership in `x • ⊤` via `mem_smul_top_iff`.

## References

* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR)
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

universe u

namespace Stacks.PuncturedSpectrum

variable {A : Type u} [CommRing A]

/-- A nonzerodivisor modulo `x` cancels out of an equation whose right-hand side is divisible by
a power of `x`: if `z` is a nonzerodivisor on `A / xA` and `a * z = c * x ^ k`, then
`a ∈ x ^ k A`.

This is where the second element of the regular sequence is used, and it is used for the whole
power `z = y ^ n` at once. -/
private theorem dvd_pow_of_mul_eq_mul_pow {x z : A} (hx : IsSMulRegular A x)
    (hz : IsSMulRegular (QuotSMulTop x A) z) :
    ∀ (k : ℕ) (a c : A), a * z = c * x ^ k → ∃ e, a = x ^ k * e := by
  intro k
  induction k with
  | zero => exact fun a c _ => ⟨a, by rw [pow_zero, one_mul]⟩
  | succ k ih =>
    intro a c h
    have hdvd : z * a ∈ x • (⊤ : Submodule A A) :=
      (mem_smul_top_iff x (z * a)).mpr ⟨c * x ^ k, by
        simp only [smul_eq_mul]
        rw [mul_comm z a, h]; ring⟩
    have hzero : (Submodule.Quotient.mk a : QuotSMulTop x A) = 0 := by
      refine hz ?_
      change z • (Submodule.Quotient.mk a : QuotSMulTop x A) = z • (0 : QuotSMulTop x A)
      rw [smul_zero, ← Submodule.Quotient.mk_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using hdvd)
    obtain ⟨a₁, ha₁⟩ := (mem_smul_top_iff x a).mp ((Submodule.Quotient.mk_eq_zero _).mp hzero)
    simp only [smul_eq_mul] at ha₁
    subst ha₁
    have h₁ : a₁ * z = c * x ^ k := by
      refine hx ?_
      change x • (a₁ * z) = x • (c * x ^ k)
      simp only [smul_eq_mul]
      linear_combination h
    obtain ⟨e, he⟩ := ih a₁ c h₁
    exact ⟨e, by rw [he]; ring⟩

/-- In a local ring the only idempotents are `0` and `1`. -/
private theorem eq_zero_or_one_of_mul_self_eq [IsLocalRing A] {e : A} (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  have key : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · obtain ⟨v, hv⟩ := h.exists_left_inv
    exact Or.inr (by linear_combination (1 - e) * hv - v * key)
  · obtain ⟨v, hv⟩ := h.exists_left_inv
    exact Or.inl (by linear_combination -e * hv + v * key)

variable (A) in
/-- A length-two `A`-regular sequence in the maximal ideal, extracted from the depth
hypothesis. -/
private theorem exists_isSMulRegular_of_two_le_depth [IsLocalRing A]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A) :
    ∃ x y : A, x ∈ maximalIdeal A ∧ y ∈ maximalIdeal A ∧
      IsSMulRegular A x ∧ IsSMulRegular (QuotSMulTop x A) y := by
  classical
  have hsmul : maximalIdeal A • (⊤ : Submodule A A) = maximalIdeal A := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have htop : ¬ maximalIdeal A • (⊤ : Submodule A A) = ⊤ := by
    rw [hsmul]; exact (maximalIdeal.isMaximal A).ne_top
  rw [Module.depth, ite_eq_right htop] at hdepth
  have hex : ∃ rs : List A,
      ((∀ r ∈ rs, r ∈ maximalIdeal A) ∧ IsRegular A rs) ∧ 2 ≤ rs.length := by
    by_contra hcon
    push Not at hcon
    have hle : (⨆ rs ∈ {rs : List A | (∀ r ∈ rs, r ∈ maximalIdeal A) ∧ IsRegular A rs},
        (rs.length : ℕ∞)) ≤ 1 := by
      refine iSup_le fun rs => iSup_le fun hrs => ?_
      have : rs.length ≤ 1 := Nat.lt_succ_iff.mp (hcon rs hrs)
      exact_mod_cast this
    have : (2 : ℕ∞) ≤ 1 := hdepth.trans hle
    simp at this
  obtain ⟨rs, ⟨hmem, hreg⟩, hlen⟩ := hex
  rcases rs with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at hlen
  · simp at hlen
  · obtain ⟨hx, hreg'⟩ := (isRegular_cons_iff A x (y :: t)).mp hreg
    obtain ⟨hy, -⟩ := (isRegular_cons_iff (QuotSMulTop x A) y t).mp hreg'
    exact ⟨x, y, hmem x (by simp), hmem y (by simp), hx, hy⟩

/-- **Stacks Project, Tag 0BLR (first assertion).** The punctured spectrum of a Noetherian local
ring of depth at least two is preconnected. -/
@[ega "IV 5.10.7" "Affine local case"]
theorem isPreconnected_of_two_le_depth (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A) :
    IsPreconnected {p : PrimeSpectrum A | p.asIdeal ≠ maximalIdeal A} := by
  obtain ⟨x, y, hxm, hym, hx, hy⟩ := exists_isSMulRegular_of_two_le_depth A hdepth
  by_contra hcon
  obtain ⟨I, J, hmul, hclosed, ⟨p, hp, hpI⟩, ⟨q, hq, hqJ⟩⟩ :=
    exists_ideals_of_not_isPreconnected_puncturedSpectrum A hcon
  have mulzero : ∀ {s t : A}, s ∈ I → t ∈ J → s * t = 0 := fun hs ht => by
    simpa [hmul] using Ideal.mul_mem_mul hs ht
  have hIne : I ≠ ⊥ := fun h => hq (hclosed q (h ▸ bot_le) hqJ)
  have hJne : J ≠ ⊥ := fun h => hp (hclosed p hpI (h ▸ bot_le))
  -- `√(I + J) = 𝔪`, hence `𝔪 ^ n ≤ I + J` for some `n`.
  have hrad : maximalIdeal A ≤ (I + J).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro K ⟨hK, hKp⟩
    rw [Ideal.add_eq_sup, sup_le_iff] at hK
    exact (hclosed ⟨K, hKp⟩ hK.1 hK.2).ge
  obtain ⟨n, hn⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hrad (maximalIdeal A).fg_of_isNoetherianRing
  have hxn : x ^ n ∈ I + J := hn (Ideal.pow_mem_pow hxm n)
  have hyn : y ^ n ∈ I + J := hn (Ideal.pow_mem_pow hym n)
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hxn hyn
  obtain ⟨a, ha, b, hb, hab⟩ := hxn
  obtain ⟨c, hc, d, hd, hcd⟩ := hyn
  have key : a * y ^ n = c * x ^ n := by
    linear_combination -a * hcd + c * hab + mulzero ha hd - mulzero hc hb
  obtain ⟨e, he⟩ := dvd_pow_of_mul_eq_mul_pow hx (hy.pow n) n a c key
  have hsq : a * a = a * x ^ n := by linear_combination a * hab - mulzero ha hb
  have hidem : e * e = e := by
    refine hx.pow (2 * n) ?_
    change x ^ (2 * n) • (e * e) = x ^ (2 * n) • e
    simp only [smul_eq_mul]
    linear_combination hsq - (a + x ^ n * e) * he + x ^ n * he
  have cancel : ∀ {t : A}, x ^ n * t = 0 → t = 0 := fun ht => by
    refine hx.pow n ?_
    change x ^ n • _ = x ^ n • (0 : A)
    simpa using ht
  rcases eq_zero_or_one_of_mul_self_eq hidem with h | h
  · refine hIne (le_bot_iff.mp fun t ht => ?_)
    have ha0 : a = 0 := by rw [he, h, mul_zero]
    have hbxn : x ^ n ∈ J := by rwa [← hab, ha0, zero_add]
    simpa using cancel (by rw [mul_comm]; exact mulzero ht hbxn)
  · refine hJne (le_bot_iff.mp fun t ht => ?_)
    have ha1 : a = x ^ n := by rw [he, h, mul_one]
    simpa using cancel (mulzero (ha1 ▸ ha) ht)

/-- **Stacks Project, Tag 0BLR (first assertion).** The punctured spectrum of a Noetherian local
ring of depth at least two is connected. -/
@[ega "IV 5.10.7" "Affine local case", sga "2 XII 4.6" "more general"]
theorem isConnected_of_two_le_depth (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A) :
    IsConnected {p : PrimeSpectrum A | p.asIdeal ≠ maximalIdeal A} := by
  refine ⟨?_, isPreconnected_of_two_le_depth A hdepth⟩
  obtain ⟨x, -, hxm, -, hx, -⟩ := exists_isSMulRegular_of_two_le_depth A hdepth
  have hxnil : ¬ IsNilpotent x := by
    rintro ⟨k, hk⟩
    refine one_ne_zero (α := A) ?_
    refine hx.pow k ?_
    change x ^ k • (1 : A) = x ^ k • (0 : A)
    simp [hk]
  obtain ⟨P, hP, hxP⟩ : ∃ P : Ideal A, P.IsPrime ∧ x ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hxnil (nilpotent_iff_mem_prime.mpr fun K hK => hcon K hK)
  exact ⟨⟨P, hP⟩, fun hEq => hxP (by rw [show P = maximalIdeal A from hEq]; exact hxm)⟩

/-- **Stacks Project, Tag 0BLR (first assertion).** The same statement in the
complement-of-the-closed-point spelling, which is the one the source uses. -/
@[stacks 0BLR "the punctured spectrum of `A`",
  ega "IV 5.10.7" "local ring case",
  sga "2 XII 4.6" "more general"]
theorem isConnected_puncturedSpectrum_of_two_le_depth (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A) :
    IsConnected ({closedPoint A}ᶜ : Set (PrimeSpectrum A)) := by
  have hset : ({closedPoint A}ᶜ : Set (PrimeSpectrum A)) =
      {p : PrimeSpectrum A | p.asIdeal ≠ maximalIdeal A} := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact ⟨fun h hp => h (PrimeSpectrum.ext hp), fun h hp => h (by rw [hp]; rfl)⟩
  rw [hset]
  exact isConnected_of_two_le_depth A hdepth

end Stacks.PuncturedSpectrum

end
