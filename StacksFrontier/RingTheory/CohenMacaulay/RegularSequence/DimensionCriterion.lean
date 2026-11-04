module

import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Criteria
import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.Serre.Reduced
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Depth.Nakayama

@[expose] public section

/-!
# Regular sequences in a Cohen–Macaulay local ring

Proof of `Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim`
(Stacks 02JN). Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring and `x₁, …, x_c ∈ 𝔪`.

The implication `→` of the equivalence is Mathlib's
`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` and uses nothing about `R`. For `←` we run
the induction of Proposition 00N6 at `M = R`: in the chain
`Supp(M) ⊇ Supp(M) ∩ V(x₁) ⊇ … ⊇ Supp(M) ∩ V(x₁, …, x_c)` each step drops the dimension by at
most one (Lemma 00KW, `Module.supportDim_le_supportDim_quotSMulTop_succ`), so a total drop of `c`
forces the first step to drop by exactly one, and Lemma 00N5 then makes `x₁` a nonzerodivisor on
`M` and `M/x₁M` again Cohen–Macaulay, carrying the induction.

Both consequences of "if so" are read off from the depth. Because `R` is Cohen–Macaulay,
`depth_𝔪(R) = dim(R)`, and a regular sequence in `𝔪` extends to one of length `depth_𝔪(R)`
(Lemma 090R), which is the extension of `x₁, …, x_c` to a regular sequence `x₁, …, x_d` of length
`d = dim(R)` — the source instead extends one element at a time by prime avoidance (Lemma 00DS).
Writing `S = R/(x₁, …, x_i)`, the images of `x_{i+1}, …, x_d` in `S` form an `S`-regular sequence
in `𝔪_S` of length `d - i`, and `dim(S) + i = dim(R)` because an initial segment of a regular
sequence is again one; so `S` has a regular sequence in `𝔪_S` as long as its dimension, which
forces `depth_{𝔪_S}(S) = dim(S)`, the reverse inequality being Lemma 00LK.

## Main results

* `Stacks.CohenMacaulay.RegularSequence.solution`: `x₁, …, x_c ∈ 𝔪` is a regular sequence if and
  only if `dim(R/(x₁, …, x_c)) + c = dim(R)`, and then it extends to a regular sequence of length
  `dim(R)` and each `R/(x₁, …, x_i)` is a Cohen–Macaulay local ring with
  `dim(R/(x₁, …, x_i)) + i = dim(R)`.

## Implementation notes

The implication `←` is proved in the generality of Proposition 00N6, as
`isRegular_of_isCohenMacaulayAtMaximalIdeal`: a finite Cohen–Macaulay module `M` over a Noetherian
local ring and elements `x₁, …, x_c ∈ 𝔪` with `dim Supp(M/(x₁, …, x_c)M) + c ≤ dim Supp(M)`.
Specialising to `M = R` costs only `Module.supportDim_self_eq_ringKrullDim` and
`supportDim_quot_smul_top_eq_ringKrullDim`, the dictionary between the dimension of the support of
`R/I` as an `R`-module and the Krull dimension of the ring `R/I`. The induction step is Lemma
00N5, which delivers the Cohen–Macaulayness of `M/x₁M` along with the regularity of `x₁` and so
carries itself; its hypothesis is stated for `Supp(M) ∩ V(x₁)`, which is
`supportDim_quotSMulTop_eq_krullDim_inter`.

The two consequences meet in `isMaximalCohenMacaulay_quotient_ofList`: if `ts ++ us` is an
`R`-regular sequence with `us ⊆ 𝔪` and `(ts ++ us).length = dim(R)`, then `R/(ts)` is a
Cohen–Macaulay local ring with `dim(R/(ts)) + ts.length = dim(R)`. Its two halves are
`isRegular_map_quotient_of_isRegular_append`, that the images of `us` in `R/(ts)` form a regular
sequence over the quotient *ring* — Cohen–Macaulayness of the quotients is asserted over that ring
(Definition 00N8), so the witnessing sequence has to be transported from `R`, which is Mathlib's
`RingTheory.Sequence.isWeaklyRegular_append_iff` and `isWeaklyRegular_map_algebraMap_iff` followed
by `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal` — and
`isMaximalCohenMacaulay_of_ringKrullDim_le_length`, that a Noetherian local ring carrying a
regular sequence in its maximal ideal at least as long as its dimension is Cohen–Macaulay.

Four further steps of the general theory are used that Mathlib does not name, and they are proved
here as private helpers: that a regular sequence of length `n` in `I` bounds `depth_I` below by `n`
(`Module.le_depth_of_isRegular`, the supremum branch of Definition 00LI), that cutting a module by
`c` elements of the maximal ideal drops the dimension of its support by at most `c`
(`supportDim_le_supportDim_quot_ofList_smul_top_add_length`, the iterate of Lemma 00KW), that
cutting by `x :: xs` is cutting by `x` and then by `xs` (`supportDim_quot_ofList_cons_smul_top`),
which is what lets the iterate and the induction of 00N6 be read on `M/xM`, and that a prefix of a
regular sequence is again one (`isRegular_prefix`), which is what makes `dim(R/(x₁, …, x_i))` a
value the equivalence already computes.

Arithmetic in `WithBot ℕ∞` is done with `ENat.WithBot.add_le_add_natCast_right_iff`: adding a
natural number on the right reflects the order, which is how "each step drops by at most one" plus
"the total drop is `c`" become "the first step drops by exactly one", and how the length of the
transported sequence is compared with `dim(R/(ts))`.

## References

* [StacksProject 02JN](https://stacks.math.columbia.edu/tag/02JN)
-/

namespace Stacks.CohenMacaulay.RegularSequence

open IsLocalRing RingTheory.Sequence Ideal Pointwise

/-- The dimension of the support of `R/I` as an `R`-module is the Krull dimension of the ring
`R/I`. -/
private lemma supportDim_quot_smul_top_eq_ringKrullDim {R : Type*} [CommRing R] (I : Ideal R) :
    Module.supportDim R (R ⧸ (I • ⊤ : Submodule R R)) = ringKrullDim (R ⧸ I) :=
  (Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ I (by simp))).trans
    (Module.supportDim_quotient_eq_ringKrullDim I)

/-- Cutting `M` by `x :: xs` is cutting it by `x` and then by `xs`, read on the dimension of the
support. -/
private lemma supportDim_quot_ofList_cons_smul_top {R : Type*} [CommRing R] (M : Type*)
    [AddCommGroup M] [Module R M] (x : R) (xs : List R) :
    Module.supportDim R (M ⧸ (Ideal.ofList (x :: xs) • ⊤ : Submodule R M)) =
      Module.supportDim R
        (QuotSMulTop x M ⧸ (Ideal.ofList xs • ⊤ : Submodule R (QuotSMulTop x M))) :=
  Module.supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs)

/-- The dimension of the support of `M/xM` is the dimension of `Supp(M) ∩ V(x)`. This is the shape
in which Lemma 00N5 states its hypothesis. -/
private lemma supportDim_quotSMulTop_eq_krullDim_inter {R : Type*} [CommRing R] (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R) :
    Module.supportDim R (QuotSMulTop x M) =
      Order.krullDim (Module.support R M ∩ PrimeSpectrum.zeroLocus {x} :
        Set (PrimeSpectrum R)) := by
  rw [Module.supportDim, Module.support_quotSMulTop]

/-- Cutting a finite module by `c` elements of the maximal ideal drops the dimension of its
support by at most `c`. This is the iterate of Lemma 00KW,
`Module.supportDim_le_supportDim_quotSMulTop_succ`. -/
private lemma supportDim_le_supportDim_quot_ofList_smul_top_add_length
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R) :
    Module.supportDim R M ≤
      Module.supportDim R (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) + xs.length := by
  induction xs generalizing M with
  | nil =>
    have h := Module.supportDim_eq_of_equiv
      (Submodule.quotEquivOfEqBot (Ideal.ofList ([] : List R) • ⊤ : Submodule R M) (by simp))
    simp [h]
  | cons x xs ih =>
    calc Module.supportDim R M
        ≤ Module.supportDim R (QuotSMulTop x M) + 1 :=
          Module.supportDim_le_supportDim_quotSMulTop_succ (hxs x (by simp))
      _ ≤ (Module.supportDim R
            (QuotSMulTop x M ⧸ (Ideal.ofList xs • ⊤ : Submodule R (QuotSMulTop x M)))
              + xs.length) + 1 := by
          gcongr
          exact ih _ fun y hy => hxs y (by simp [hy])
      _ = Module.supportDim R (M ⧸ (Ideal.ofList (x :: xs) • ⊤ : Submodule R M))
            + ((x :: xs).length : ℕ) := by
          rw [supportDim_quot_ofList_cons_smul_top, List.length_cons]; push_cast; ring

/-- Adding `1` is injective on `WithBot ℕ∞`: it fixes `⊥` and `⊤` and shifts the finite values. -/
private lemma add_one_left_injective {x y : WithBot ℕ∞} (h : x + 1 = y + 1) : x = y := by
  rcases eq_or_ne x ⊥ with hx | hx
  · subst hx
    simp only [WithBot.bot_add] at h
    rcases eq_or_ne y ⊥ with hy | hy
    · exact hy.symm
    · exact absurd h.symm (by simp [WithBot.add_eq_bot, hy])
  · rcases eq_or_ne y ⊥ with hy | hy
    · subst hy
      simp only [WithBot.bot_add] at h
      exact absurd h (by simp [WithBot.add_eq_bot, hx])
    · lift x to ℕ∞ using hx
      lift y to ℕ∞ using hy
      rw [show ((1 : WithBot ℕ∞)) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add,
        ← WithBot.coe_add, WithBot.coe_eq_coe] at h
      rcases eq_or_ne x ⊤ with hxt | hxt
      · subst hxt
        simp only [top_add] at h
        rcases eq_or_ne y ⊤ with hyt | hyt
        · rw [hyt]
        · lift y to ℕ using hyt
          exact absurd h.symm (by simp)
      · lift x to ℕ using hxt
        rcases eq_or_ne y ⊤ with hyt | hyt
        · subst hyt; simp only [top_add] at h; exact absurd h (by simp)
        · lift y to ℕ using hyt
          norm_cast at h ⊢
          omega

/-- In `ℕ∞` the inequality `y + 1 ≤ y` forces `y = ⊤`. -/
private lemma enat_eq_top_of_add_one_le {y : ℕ∞} (h : y + 1 ≤ y) : y = ⊤ := by
  rcases eq_or_ne y ⊤ with h1 | h1
  · exact h1
  · lift y to ℕ using h1
    exfalso
    rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, ← Nat.cast_add, Nat.cast_le] at h
    omega

/-- The Krull dimension of a subset of a preorder is monotone in the subset. -/
private lemma krullDim_mono {α : Type*} [Preorder α] {s t : Set α} (h : s ⊆ t) :
    Order.krullDim s ≤ Order.krullDim t :=
  Order.krullDim_le_of_strictMono (Set.inclusion h) (fun _ _ hab => hab)

/-- Part (a) of Stacks 00N5, and the whole content of the lemma: if `M` is a finite
Cohen-Macaulay module over a Noetherian local ring and `g ∈ R` cuts the dimension of the support
of `M` down by exactly one, then `g` is a nonzerodivisor on `M`. Membership of `g` in the maximal
ideal is not needed. -/
@[ega "0 16.5.6" "b⇒a for r = 1"]
private lemma isSMulRegular_of_krullDim_inter_zeroLocus_succ_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hM : Module.IsCohenMacaulayAtMaximalIdeal R M) {g : R}
    (hdim : Order.krullDim
        (Module.support R M ∩ PrimeSpectrum.zeroLocus {g} : Set (PrimeSpectrum R)) + 1 =
      Module.supportDim R M) :
    IsSMulRegular M g := by
  by_contra hreg
  -- An element that is not a nonzerodivisor lies in some associated prime `p` of `M`.
  have hmem : g ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]; exact hreg
  obtain ⟨p, hp, hgp⟩ := Set.mem_iUnion₂.mp hmem
  have hpP : p.IsPrime := hp.isPrime
  have hann : Module.annihilator R M ≤ p := by
    rw [← Submodule.annihilator_top]; exact hp.annihilator_le
  set S : Set (PrimeSpectrum R) := Module.support R M ∩ PrimeSpectrum.zeroLocus {g} with hS
  -- `V(p)` sits inside `Supp(M) ∩ V(g)`, and contains `p` itself.
  have hsub : (PrimeSpectrum.zeroLocus (p : Set R) : Set (PrimeSpectrum R)) ⊆ S := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus] at hq
    refine ⟨?_, ?_⟩
    · rw [Module.support_eq_zeroLocus]
      exact fun r hr => hq (hann hr)
    · exact fun r hr => by rw [Set.mem_singleton_iff.mp hr]; exact hq hgp
  have hmemS : (⟨p, hpP⟩ : PrimeSpectrum R) ∈ S := hsub (by simp)
  have hnonempty : Nonempty S := ⟨⟨_, hmemS⟩⟩
  have hbot : Order.krullDim S ≠ ⊥ := by
    have h0 := Order.krullDim_nonneg (α := S)
    intro h; rw [h] at h0; simp at h0
  -- Ischebeck's bound, transported along `V(p) ⊆ Supp(M) ∩ V(g)`.
  have hle : (Module.depth R (maximalIdeal R) M : WithBot ℕ∞) ≤ Order.krullDim S := by
    refine le_trans (Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes hp) ?_
    rw [ringKrullDim_quotient]
    exact krullDim_mono hsub
  have hMeq : (Module.depth R (maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M := hM
  rw [← hdim] at hMeq
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rw [← hx] at hle hMeq
  have hx1 : x + 1 ≤ x := by
    rw [hMeq, show ((1 : WithBot ℕ∞)) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add,
      WithBot.coe_le_coe] at hle
    exact hle
  -- So `dim(Supp(M) ∩ V(g)) = ⊤`, forcing `depth_𝔪(M) = ⊤`, which Nakayama and 0AUJ forbid.
  have hxtop : x = ⊤ := enat_eq_top_of_add_one_le hx1
  have hnt : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with hs | hs
    · exact absurd hp not_isAssociatedPrime_of_subsingleton
    · exact hs
  have hsm : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := fun h =>
    Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _) h.symm
  have hlt := Module.depth_lt_top R (maximalIdeal R) M hsm
  rw [hxtop] at hMeq
  have htop : Module.depth R (maximalIdeal R) M = ⊤ := by
    apply WithBot.coe_injective (α := ℕ∞)
    rw [hMeq, show ((1 : WithBot ℕ∞)) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add]
    norm_num
  exact absurd htop hlt.ne

/-- **Stacks 00N5.** Let `R` be a Noetherian local ring with maximal ideal `𝔪`, let `M` be a
finite Cohen-Macaulay `R`-module (Definition 00N3) and let `g ∈ 𝔪` be such that
`dim(Supp(M) ∩ V(g)) = dim Supp(M) - 1`. Then `g` is a nonzerodivisor on `M`, the module `M/gM` is
again Cohen-Macaulay, and `depth_𝔪(M/gM) + 1 = depth_𝔪(M)`.

The whole content is the regularity of `g`, which is
`isSMulRegular_of_krullDim_inter_zeroLocus_succ_eq`; given it, the depth drops by one by Lemma
090R(1) and the dimension of the support drops by one by
`Module.supportDim_quotSMulTop_succ_eq_supportDim`, and cancelling the `+ 1`s turns
Cohen-Macaulayness of `M` into Cohen-Macaulayness of `M/gM`. -/
@[ega "0 16.5.5" "partial", ega "0 16.5.6" "special case"]
private theorem isSMulRegular_and_quotSMulTop_and_depth_succ_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hM : Module.IsCohenMacaulayAtMaximalIdeal R M) {g : R}
    (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdim : Order.krullDim
        (Module.support R M ∩ PrimeSpectrum.zeroLocus {g} : Set (PrimeSpectrum R)) + 1 =
      Module.supportDim R M) :
    IsSMulRegular M g ∧ Module.IsCohenMacaulayAtMaximalIdeal R (QuotSMulTop g M) ∧
      Module.depth R (IsLocalRing.maximalIdeal R) (QuotSMulTop g M) + 1 =
        Module.depth R (IsLocalRing.maximalIdeal R) M := by
  have hreg : IsSMulRegular M g := isSMulRegular_of_krullDim_inter_zeroLocus_succ_eq hM hdim
  have hdepth : Module.depth R (maximalIdeal R) (QuotSMulTop g M) + 1 =
      Module.depth R (maximalIdeal R) M :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
      (maximalIdeal R) M).1 g hg hreg
  refine ⟨hreg, ?_, hdepth⟩
  have hsupp : Module.supportDim R (QuotSMulTop g M) + 1 = Module.supportDim R M :=
    Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hg
  have hM' : (Module.depth R (maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M := hM
  change ((Module.depth R (maximalIdeal R) (QuotSMulTop g M) : ℕ∞) : WithBot ℕ∞) =
    Module.supportDim R (QuotSMulTop g M)
  refine add_one_left_injective ?_
  rw [hsupp, ← hM', ← hdepth]
  norm_cast

/-- **Proposition 00N6 at `M` a Cohen–Macaulay module, the implication `←` of Lemma 02JN.** If
`M` is Cohen–Macaulay and `x₁, …, x_c ∈ 𝔪` cut the dimension of its support down by `c`, then
`x₁, …, x_c` is an `M`-regular sequence. -/
@[ega "0 16.5.7" "partial"]
private theorem isRegular_of_isCohenMacaulayAtMaximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : Module.IsCohenMacaulayAtMaximalIdeal R M) {xs : List R}
    (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R)
    (hdim : Module.supportDim R (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) + xs.length ≤
      Module.supportDim R M) :
    IsRegular M xs := by
  induction xs generalizing M with
  | nil => exact IsRegular.nil R M
  | cons x xs ih =>
    have hx : x ∈ maximalIdeal R := hxs x (by simp)
    have hxs' : ∀ y ∈ xs, y ∈ maximalIdeal R := fun y hy => hxs y (by simp [hy])
    have hnt : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
    -- the total drop, read on `M/xM`
    have hlast : Module.supportDim R
          (QuotSMulTop x M ⧸ (Ideal.ofList xs • ⊤ : Submodule R (QuotSMulTop x M)))
            + (xs.length : WithBot ℕ∞) + 1 ≤ Module.supportDim R M := by
      refine le_trans (le_of_eq ?_) hdim
      rw [supportDim_quot_ofList_cons_smul_top, List.length_cons]; push_cast; ring
    -- the remaining `c - 1` elements drop the dimension by at most `c - 1`, so the first step
    -- drops it by exactly one
    have hstep : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
      refine le_antisymm (le_trans ?_ hlast)
        (Module.supportDim_le_supportDim_quotSMulTop_succ hx)
      gcongr
      exact supportDim_le_supportDim_quot_ofList_smul_top_add_length _ xs hxs'
    -- Lemma 00N5 applied to `M` and `x`
    obtain ⟨hreg, hCM, -⟩ :=
      isSMulRegular_and_quotSMulTop_and_depth_succ_eq hM hx
        (by rw [← supportDim_quotSMulTop_eq_krullDim_inter M x]; exact hstep)
    refine IsRegular.cons hreg (ih hCM hxs' ?_)
    exact (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
      (by simpa using hlast.trans_eq hstep.symm)

/-- A prefix of an `M`-regular sequence is an `M`-regular sequence: weak regularity is inherited
by `isWeaklyRegular_append_iff`, and the quotient stays nonzero because a larger ideal cuts more
away. -/
private lemma isRegular_prefix {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (ts us : List R) (h : IsRegular M (ts ++ us)) : IsRegular M ts := by
  rw [isRegular_iff] at h ⊢
  refine ⟨((isWeaklyRegular_append_iff M ts us).mp h.1).1, fun hts => h.2 (le_antisymm ?_ le_top)⟩
  exact hts.le.trans (Submodule.smul_mono_left (Ideal.span_mono (by simp +contextual)))

/-- The quotient of a local ring `R` by the ideal generated by an `R`-regular sequence is local,
and the quotient map is a local homomorphism. -/
private lemma isLocalRing_isLocalHom_quotient_ofList {R : Type*} [CommRing R] [IsLocalRing R]
    {ts : List R} (h : IsRegular R ts) :
    ∃ _ : IsLocalRing (R ⧸ Ideal.ofList ts), IsLocalHom (Ideal.Quotient.mk (Ideal.ofList ts)) := by
  have : Nontrivial (R ⧸ Ideal.ofList ts) :=
    Submodule.Quotient.nontrivial_iff.mpr fun hI => h.top_ne_smul (by simp [hI])
  have hloc : IsLocalRing (R ⧸ Ideal.ofList ts) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  exact ⟨hloc, IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective⟩

/-- **A Noetherian local ring with a long enough regular sequence is Cohen–Macaulay.** If `rs` is
an `S`-regular sequence in the maximal ideal of `S` with `dim(S) ≤ rs.length`, then `S` is
Cohen–Macaulay; the reverse inequality `depth ≤ dim` is Lemma 00LK. -/
private lemma isMaximalCohenMacaulay_of_ringKrullDim_le_length {S : Type*} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] {rs : List S} (hmem : ∀ r ∈ rs, r ∈ maximalIdeal S)
    (hreg : IsRegular S rs) (hle : ringKrullDim S ≤ (rs.length : WithBot ℕ∞)) :
    Module.IsMaximalCohenMacaulay S S := by
  change (Module.depth S (maximalIdeal S) S : WithBot ℕ∞) = ringKrullDim S
  refine le_antisymm ((Module.depth_le_supportDim S _ S
    (Module.maximalIdeal_smul_top_ne_top S)).trans_eq (Module.supportDim_self_eq_ringKrullDim S))
    (hle.trans ?_)
  exact_mod_cast Module.le_depth_of_isRegular (maximalIdeal S) hmem hreg

/-- **The tail of a regular sequence is regular over the quotient by its initial segment.** If
`ts ++ us` is an `R`-regular sequence and `us` lies in the maximal ideal of the local ring `R`,
then the images of `us` in `R/(ts)` form a regular sequence over that ring. -/
private lemma isRegular_map_quotient_of_isRegular_append {R : Type*} [CommRing R] [IsLocalRing R]
    (ts us : List R) (hus : ∀ r ∈ us, r ∈ maximalIdeal R) (h : IsRegular R (ts ++ us)) :
    IsRegular (R ⧸ Ideal.ofList ts) (us.map (Ideal.Quotient.mk (Ideal.ofList ts))) := by
  obtain ⟨_, _⟩ := isLocalRing_isLocalHom_quotient_ofList (isRegular_prefix ts us h)
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (List.forall_mem_map.mpr fun r hr => map_nonunit _ r (hus r hr))).mpr ?_
  rw [← Ideal.Quotient.algebraMap_eq]
  refine (isWeaklyRegular_map_algebraMap_iff _ _ _).mpr ?_
  refine (LinearEquiv.isWeaklyRegular_congr
    (Submodule.quotEquivOfEq (Ideal.ofList ts • ⊤) (Ideal.ofList ts) (by simp)) _).mp ?_
  exact ((isWeaklyRegular_append_iff R ts us).mp h.toIsWeaklyRegular).2

/-- **The quotients of a maximal regular sequence are Cohen–Macaulay.** Let `ts ++ us` be an
`R`-regular sequence with `us` in the maximal ideal of the Noetherian local ring `R` and with
`(ts ++ us).length = dim(R)`. Then `R/(ts)` is a Cohen–Macaulay local ring of dimension
`dim(R) - ts.length`. -/
private theorem isMaximalCohenMacaulay_quotient_ofList {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (ts us : List R)
    (hus : ∀ r ∈ us, r ∈ maximalIdeal R) (h : IsRegular R (ts ++ us))
    (hlen : ((ts ++ us).length : WithBot ℕ∞) = ringKrullDim R) :
    ∃ _ : IsLocalRing (R ⧸ Ideal.ofList ts),
      Module.IsMaximalCohenMacaulay (R ⧸ Ideal.ofList ts) (R ⧸ Ideal.ofList ts) ∧
        ringKrullDim (R ⧸ Ideal.ofList ts) + ts.length = ringKrullDim R := by
  obtain ⟨hloc, _⟩ := isLocalRing_isLocalHom_quotient_ofList (isRegular_prefix ts us h)
  have hdim : ringKrullDim (R ⧸ Ideal.ofList ts) + ts.length = ringKrullDim R :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ts (isRegular_prefix ts us h)
  refine ⟨hloc, isMaximalCohenMacaulay_of_ringKrullDim_le_length
    (List.forall_mem_map.mpr fun r hr => map_nonunit _ r (hus r hr))
    (isRegular_map_quotient_of_isRegular_append ts us hus h) ?_, hdim⟩
  rw [List.length_map]
  refine (ENat.WithBot.add_le_add_natCast_right_iff (c := ts.length)).mp (le_of_eq ?_)
  rw [hdim, ← hlen, List.length_append]
  push_cast
  ring

/-- Lemma 02JN for a Noetherian local Cohen–Macaulay ring `R`: a list `xs` of elements of `𝔪` is a
regular sequence if and only if `dim(R/(xs)) + length xs = dim(R)`, and then `xs` extends by
elements of `𝔪` to a regular sequence of length `dim(R)` and each `R/(x₁, …, x_i)` is a
Cohen–Macaulay local ring with `dim(R/(x₁, …, x_i)) + i = dim(R)`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R) :
    (RingTheory.Sequence.IsRegular R xs ↔
        ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R) ∧
      (RingTheory.Sequence.IsRegular R xs →
        (∃ ys : List R, (∀ y ∈ ys, y ∈ maximalIdeal R) ∧
            RingTheory.Sequence.IsRegular R (xs ++ ys) ∧
            ((xs ++ ys).length : WithBot ℕ∞) = ringKrullDim R) ∧
        ∀ i ≤ xs.length, ∃ _ : IsLocalRing (R ⧸ Ideal.ofList (xs.take i)),
          Module.IsMaximalCohenMacaulay (R ⧸ Ideal.ofList (xs.take i))
              (R ⧸ Ideal.ofList (xs.take i)) ∧
            ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) + i = ringKrullDim R) := by
  have hdepthR : (Module.depth R (maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R := hR
  have hCM : Module.IsCohenMacaulayAtMaximalIdeal R R := by
    change (Module.depth R (maximalIdeal R) R : WithBot ℕ∞) = Module.supportDim R R
    rw [Module.supportDim_self_eq_ringKrullDim]
    exact hdepthR
  refine ⟨⟨ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs, fun h => ?_⟩, fun hreg => ?_⟩
  · refine isRegular_of_isCohenMacaulayAtMaximalIdeal hCM hxs (le_of_eq ?_)
    rw [supportDim_quot_smul_top_eq_ringKrullDim, Module.supportDim_self_eq_ringKrullDim]
    exact h
  -- extend `xs` to a regular sequence of length `depth_𝔪(R) = dim(R)` (Lemma 090R)
  obtain ⟨ss, hssmem, hssreg, hsslen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append (maximalIdeal R) R).2
      (Module.maximalIdeal_smul_top_ne_top R) xs hxs hreg
  have hsslen' : ((xs ++ ss).length : WithBot ℕ∞) = ringKrullDim R := by
    rw [← hdepthR]; exact_mod_cast hsslen
  refine ⟨⟨ss, hssmem, hssreg, hsslen'⟩, fun i hi => ?_⟩
  -- `xs.take i` and the tail `xs.drop i ++ ss` of the extension
  have hsplit : xs ++ ss = xs.take i ++ (xs.drop i ++ ss) := by
    rw [← List.append_assoc, List.take_append_drop]
  obtain ⟨hloc, hCMS, hdimS⟩ := isMaximalCohenMacaulay_quotient_ofList (xs.take i)
    (xs.drop i ++ ss)
    (fun r hr => (List.mem_append.mp hr).elim (fun h => hxs r (List.mem_of_mem_drop h)) (hssmem r))
    (hsplit ▸ hssreg) (by rw [← hsplit]; exact hsslen')
  exact ⟨hloc, hCMS, by rwa [List.length_take, min_eq_left hi] at hdimS⟩

end Stacks.CohenMacaulay.RegularSequence

/-!
# Regular sequences in a Cohen–Macaulay local ring

Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring and let `x₁, …, x_c ∈ 𝔪`. Then

`x₁, …, x_c is a regular sequence  ↔  dim(R/(x₁, …, x_c)) = dim(R) - c`,

and when this holds the sequence extends to a regular sequence of length `dim(R)` and every
initial quotient `R/(x₁, …, x_i)` is again a Cohen–Macaulay local ring, of dimension
`dim(R) - i`. So in a Cohen–Macaulay ring regularity of a sequence in `𝔪` is detected by
dimension alone: cutting by `c` elements can drop the dimension by at most `c`
(`Ideal.height_le_card_of_mem_minimalPrimes_span_finset`), and dropping it by exactly `c` forces
each successive element to be a nonzerodivisor.

The implication `→` is Mathlib's `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` and needs
no Cohen–Macaulay hypothesis; the content of the lemma is `←` together with the two consequences,
and it is the case `M = R` of Proposition 00N6.

## Main results

* `Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim`:
  the equivalence above, together with the extension to a regular sequence of length `dim(R)`
  and the Cohen–Macaulayness of the initial quotients.

## Implementation notes

Faithfulness to [StacksProject 02JN]:

1. No dead hypothesis. `hR` (Cohen–Macaulayness of `R`) is used by the implication `←` of the
   equivalence — it fails without it, see the witness below — and by the conjunct asserting that
   the quotients are Cohen–Macaulay; `hxs`, the source's `x_i ∈ 𝔪`, is spent by a proof of that
   same implication and of the extension conjunct, whose extra elements are again taken in `𝔪`.
   It is not needed for the statement to be *true*, though: each side of the equivalence implies
   it on its own, since a proper ideal of a local ring lies in `𝔪` and `Ideal.ofList xs ≠ ⊤`
   follows both from regularity (the quotient is nonzero) and from the dimension equation
   (`⊥ + c = ⊥`). So on the lists `hxs` excludes, both sides of the equivalence are false and the
   second conjunct is vacuous: it narrows nothing, and is retained as the source's own hypothesis,
   which both call sites have in hand. `[IsNoetherianRing R]` and `[IsLocalRing R]` are the
   source's hypotheses on `R` and are used throughout. The implication `→` alone would not use
   `hR`, but the lemma asserts the equivalence, which does.
2. The scalars and the base are the source's. Regularity is `RingTheory.Sequence.IsRegular R xs`,
   regularity of `xs` on `R` viewed as a module over itself, with the elements of `R` acting on
   `R`; the ideal divided out is `Ideal.ofList xs`, the ideal of `R` generated by `xs`; and each
   `R/(x₁, …, x_i)` is asserted Cohen–Macaulay *as a ring in its own right* — the depth is taken
   over the quotient at its own maximal ideal, not over `R` at `𝔪` — which is Definition 00N8,
   the source's meaning of "each quotient is a Cohen–Macaulay ring".
3. The ideals and the extension are pinned. The source's `(x₁, …, x_i)` is
   `Ideal.ofList (xs.take i)`, the ideal generated by the initial segment of `xs` in the given
   order, not by an arbitrary sub-list; and "`x₁, …, x_c` can be extended to a regular sequence
   of length `dim(R)`" is a regular sequence of the form `xs ++ ys`, so `xs` is an initial
   segment of the extension — the mere existence of a regular sequence of length `dim(R)`
   (equivalently, Cohen–Macaulayness of `R`) is not the assertion. The dimensions are
   `ringKrullDim` of the quotient rings, not `Module.supportDim R` of them.
4. The instantiation is not degenerate. For `R = k[[x, y]]` (regular, hence Cohen–Macaulay, of
   dimension `2`) and `xs = [x]`: `x` is a nonzerodivisor, `dim(R/xR) + 1 = 1 + 1 = 2`, the
   sequence extends to `[x, y]` of length `2 = dim(R)`, and `R/xR ≅ k[[y]]` is Cohen–Macaulay of
   dimension `1`. Both directions have content: for `xs = [x, x]` the sequence is not regular and
   `dim(R/(x, x)) + 2 = 1 + 2 = 3 ≠ 2`, so the equivalence is not the constantly-true statement.
   The Cohen–Macaulay hypothesis cannot be dropped from `←`: in `R = k[[x, y]]/(x², xy)`, which
   is local of dimension `1` and not Cohen–Macaulay, the element `y ∈ 𝔪` has
   `R/yR ≅ k[x]/(x²)` of dimension `0 = 1 - 1`, yet `y · x = 0` with `x ≠ 0`, so `[y]` is not a
   regular sequence.

Departures from the source's form, none of them weakening it.

*Subtraction is moved to the other side.* `dim(R/(x₁, …, x_c)) = dim(R) - c` is stated as
`ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R`. Krull dimensions live in
`WithBot ℕ∞`, where subtraction is truncated and would make the source's equation both weaker
and harder to use; the additive form is the one Mathlib states
(`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`) and the one already used by tag 00NQ,
so this rewrites against both without a bridge. The same is done for the initial quotients and
for the length of the extension, `((xs ++ ys).length : WithBot ℕ∞) = ringKrullDim R`. The additive
form also carries the source's requirement that the quotient be nonzero, which the subtractive
one loses: `⊥ + c = ⊥` in `WithBot ℕ∞` and `ringKrullDim` of the zero ring is `⊥`
(`ringKrullDim_eq_bot_of_subsingleton`), so the equation forces `R/(x₁, …, x_c) ≠ 0`, exactly the
nondegeneracy condition contained in `RingTheory.Sequence.IsRegular` on the other side.

*"`R` is a Cohen–Macaulay local ring" is `Module.IsMaximalCohenMacaulay R R`.* Definition 00N8
reads `Module.IsCohenMacaulayAtMaximalIdeal R R`, `depth_𝔪(R) = dim Supp(R)`; for a local ring
`Supp(R) = Spec(R)` (`Module.supportDim_self_eq_ringKrullDim`), so the two predicates agree, and
`Module.IsMaximalCohenMacaulay R R` (Definition 00NF at `M = R`) is the spelling used by tags
00NA, 00NB, 00ND, 00NQ, 00R4 and 00R5.

*The sequence is a `List R`.* The source's `x₁, …, x_c` is `xs : List R` and its `c` is
`xs.length`, as in `RingTheory.Sequence.IsRegular` and `Ideal.ofList`; the initial segments are
`xs.take i` for `i ≤ xs.length`.

*The local ring structure on the quotients is existentially bound.* `Ideal.ofList (xs.take i)` is
contained in `𝔪`, hence proper, hence `R/(x₁, …, x_i)` is local; but that instance is not
available to instance resolution before the lemma is proved, and `Module.IsMaximalCohenMacaulay`
takes it as an instance argument, so it is bound by `∃ (_ : IsLocalRing …)` inside the
conclusion, as in the statements of Lemmas 04GN and 05WQ. It is a `Prop`, so no data is chosen.

*All three assertions are one theorem.* The equivalence and the two consequences of the source's
"if so" are conjuncts of a single statement, the two consequences under the hypothesis
`RingTheory.Sequence.IsRegular R xs`; the name records the equivalence.

## References

* [StacksProject 02JN](https://stacks.math.columbia.edu/tag/02JN)

## Tags

Cohen-Macaulay ring, regular sequence, Krull dimension, local ring
-/

@[expose] public section

open IsLocalRing in
/-- **Regular sequences in a Cohen–Macaulay local ring are those cutting out the right
dimension.** Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring and let `xs = x₁, …, x_c` be
a list of elements of `𝔪`. Then `xs` is a regular sequence if and only if
`dim(R/(x₁, …, x_c)) + c = dim(R)`, and in that case `xs` extends by elements of `𝔪` to a regular
sequence of length `dim(R)` and each `R/(x₁, …, x_i)` is a Cohen–Macaulay local ring of dimension
`dim(R) - i`. The source's subtraction is moved to the other side of the equations, Krull
dimensions being valued in `WithBot ℕ∞`; see the module docstring. -/
@[stacks 02JN "`R` Cohen–Macaulay is `Module.IsMaximalCohenMacaulay R R` (Definition 00NF at \
  `M = R`, equal to Definition 00N8 by `Module.supportDim_self_eq_ringKrullDim`); the source's \
  `dim(R/(x₁, …, x_i)) = dim(R) - i` is stated additively, as in \
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`; the extension is an append, and the \
  local ring structures on the quotients are existentially bound. See the module docstring.",
  ega "0 16.5.6" "M = R (CM local ring)",
  ega "0 16.5.5" "M = R; a) ⇔ b)",
  ega "0 16.5.7" "case M = R", sga "2 III 2.6" "M = R, CM local", ega "0 16.5.9" "special case"]
public theorem Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R) :
    (RingTheory.Sequence.IsRegular R xs ↔
        ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R) ∧
      (RingTheory.Sequence.IsRegular R xs →
        (∃ ys : List R, (∀ y ∈ ys, y ∈ maximalIdeal R) ∧
            RingTheory.Sequence.IsRegular R (xs ++ ys) ∧
            ((xs ++ ys).length : WithBot ℕ∞) = ringKrullDim R) ∧
        ∀ i ≤ xs.length, ∃ _ : IsLocalRing (R ⧸ Ideal.ofList (xs.take i)),
          Module.IsMaximalCohenMacaulay (R ⧸ Ideal.ofList (xs.take i))
              (R ⧸ Ideal.ofList (xs.take i)) ∧
            ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) + i = ringKrullDim R) :=
  Stacks.CohenMacaulay.RegularSequence.solution hR xs hxs

end

end
