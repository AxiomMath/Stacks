module

public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Module.GoodElement
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.Serre.Reduced
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cutting a Cohen-Macaulay module by a dimension-dropping element

Throughout, `R` is a Noetherian local ring with maximal ideal `m` and `M` is a finite `R`-module.
This file contains the lemmas on quotients `M / gM` and `M / (g₁, …, g_c) M` that underlie
Stacks 00N5 and 00N6 (Stacks Proposition 10.103.4):

* unmixedness of a Cohen-Macaulay module: an element lying in an associated prime does not drop
  the support dimension (`cohenMacaulay_supportDim_quotient_ge_of_associatedPrime`);
* depth of `M / gM` for an `M`-regular `g ∈ m`: `depth M = depth (M / gM) + 1`
  (`depthSup_eq_depthSup_quotSMulTop_add_one`, `depth_quotSMulTop_eq_of_isSMulRegular`);
* Cohen-Macaulayness of `M / gM` and `M / (g₁, …, g_c) M` when the support dimension drops,
  and regularity of a dimension-dropping family (`cohenMacaulay_quotSMulTop_of_dimDrop`,
  `cohenMacaulay_dimDrop_isRegular`);
* a regular sequence of length `depth M` is maximal (`maximal_of_length_eq_depth`);
* strict dimension drop by an element avoiding the minimal primes of `Ann M`
  (`supportDim_quotSMulTop_le_of_avoid_minimalPrimes`).
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

/-- An element is `X`-regular iff it lies in no associated prime of `X`. -/
private theorem isSMulRegular_iff_forall_notMem_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {X : Type*} [AddCommGroup X] [Module R X] {d : R} :
    IsSMulRegular X d ↔ ∀ p ∈ associatedPrimes R X, d ∉ p := by
  have h := biUnion_associatedPrimes_eq_compl_regular R X
  have h' : d ∈ ⋃ p ∈ associatedPrimes R X, (p : Set R) ↔ ¬ IsSMulRegular X d := by
    rw [h]; rfl
  simp only [Set.mem_iUnion₂, exists_prop, SetLike.mem_coe] at h'
  rw [← not_iff_not, ← h']
  simp

/-- A prime `p` associated to `N` has `V(p) ⊆ Supp N`. -/
private theorem zeroLocus_subset_support_of_mem_associatedPrimes
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {p : Ideal R} (hp : p ∈ associatedPrimes R N) :
    PrimeSpectrum.zeroLocus (p : Set R) ⊆ Module.support R N := by
  intro q hq
  rw [PrimeSpectrum.mem_zeroLocus] at hq
  rw [Module.mem_support_iff_of_finite]
  have h2 : (⊤ : Submodule R N).annihilator ≤ p := IsAssociatedPrime.annihilator_le hp
  rw [Submodule.annihilator_top] at h2
  exact le_trans h2 hq

/-- If `p ∈ Ass N` and `V(p) ⊆ Supp X`, then `depth N ≤ krullDim Supp X`. -/
private theorem depthSup_le_krullDim_support_of_zeroLocus_subset
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    {X : Type*} [AddCommGroup X] [Module R X] {p : Ideal R} (hp : p ∈ associatedPrimes R N)
    (hsub : PrimeSpectrum.zeroLocus (p : Set R) ⊆ Module.support R X) :
    (Module.depthSup R (maximalIdeal R) N : WithBot ℕ∞) ≤ Order.krullDim (Module.support R X) :=
  (depth_le_krullDim_zeroLocus_of_mem_associatedPrimes p hp).trans
    (Order.krullDim_le_of_strictMono (Set.inclusion hsub) (Subtype.strictMono_coe _))

/-- The depth of a Cohen-Macaulay module of support dimension `e` is `e`. -/
private theorem depthSup_eq_natCast_of_isCohenMacaulay
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (hCM : IsCohenMacaulay R N) {e : ℕ} (he : Module.supportDim R N = (e : WithBot ℕ∞)) :
    Module.depthSup R (maximalIdeal R) N = (e : ℕ∞) := by
  have h : (Module.depthSup R (maximalIdeal R) N : WithBot ℕ∞) = (e : WithBot ℕ∞) := by
    rw [← he]; exact hCM.symm
  exact_mod_cast h

/-- `e = (e - 1) + 1` when `1 ≤ e`, in any additive monoid with one. -/
private theorem natCast_eq_natCast_sub_one_add_one {α : Type*} [AddMonoidWithOne α] {e : ℕ}
    (hpos : 1 ≤ e) : (e : α) = ((e - 1 : ℕ) : α) + 1 := by
  have := congrArg (Nat.cast : ℕ → α) (Nat.sub_add_cancel hpos).symm
  rwa [Nat.cast_add, Nat.cast_one] at this

/-- **Unmixedness consequence — Stacks 00N4 (10.103.2), the analytic heart of 00N5.**
For a finite, nonzero, Cohen-Macaulay module `N` of support dimension `e`, if `p` is an
associated prime of `N` containing `g`, then the quotient `N/gN` still has support
dimension at least `e`. (Equivalently: cutting `N` by an element `g` lying in an
associated prime does not drop the support dimension below `e`, because — by
unmixedness of CM modules — every associated prime `p` of `N` has full coheight
`dim(R/p) = e`, and `V(p) ⊆ Supp(N) ∩ V(g) = Supp(N/gN)` whenever `g ∈ p`.)

The argument (Stacks 00N4 + the geometric bridge).
1. **Unmixedness (Stacks 00N4 / Matsumura Thm 17.2, via Stacks 00LK).** For CM `N`,
   every `p ∈ Ass(N)` has `dim(R/p) = e = dim Supp(N)`. This rests on the depth–coheight
   bound (Stacks 00LK): for any finite nonzero `M` and `p ∈ Ass(M)`,
   `depth M ≤ dim(R/p)`. Specialised to CM `N` (`depth N = dim Supp N = e`) and combined
   with `dim(R/p) ≤ sup_{q ∈ Ass N} dim(R/q) = dim Supp N = e` (= `Module.supportDim` as
   `krullDim` of the support), this forces `dim(R/p) = e`.
   The proof of 00LK iterates "lifting an associated prime strictly upward along an
   `M`-regular element" (using `biUnion_associatedPrimes_eq_compl_regular` + prime
   avoidance to pick an `M`-regular `x ∈ m \ p`, then Krull's intersection theorem
   `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` to find `p ⊊ p* ∈ Ass(M/xM)`) along a
   maximal `M`-regular sequence of length `depth M`, yielding a length-`depth M` chain of
   primes above `p`.
2. **Geometric bridge.** Since `g ∈ p` and `p ∈ Ass(N) ⊆ Supp(N)`,
   `V(p) = zeroLocus p ⊆ Supp(N) ∩ zeroLocus {g} = Supp(N ⧸ span{g}•⊤)`
   (`Module.support_quotient`, `Module.support_eq_zeroLocus`, `PrimeSpectrum.mem_zeroLocus`).
   Hence `supportDim(N/gN) = krullDim Supp(N/gN) ≥ krullDim V(p) = dim(R/p) = e`
   (`krullDim` monotone under `Set.inclusion`: `Order.krullDim_le_of_strictMono`).
-/
@[ega "0 16.3.4" "special case"]
theorem cohenMacaulay_supportDim_quotient_ge_of_associatedPrime
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (hCM : IsCohenMacaulay R N)
    (e : ℕ) (he : Module.supportDim R N = (e : WithBot ℕ∞))
    (g : R) (p : Ideal R) (hp : p ∈ associatedPrimes R N) (hgp : g ∈ p) :
    (e : WithBot ℕ∞) ≤
      Module.supportDim R (N ⧸ (Ideal.span {g} • (⊤ : Submodule R N))) := by
  -- Geometric bridge: `V(p) ⊆ Supp(N) ∩ V(g) = Supp(N/gN)` (since `ann N ≤ p` and `g ∈ p`).
  have hsub : PrimeSpectrum.zeroLocus (p : Set R) ⊆
      Module.support R (N ⧸ (Ideal.span {g} • (⊤ : Submodule R N))) := by
    rw [Module.support_quotient]
    intro q hq
    refine ⟨zeroLocus_subset_support_of_mem_associatedPrimes hp hq, ?_⟩
    rw [PrimeSpectrum.mem_zeroLocus] at hq ⊢
    exact le_trans (Ideal.span_le.2 (Set.singleton_subset_iff.2 hgp)) hq
  -- Cohen–Macaulayness identifies `e` with `depth N`, and then
  -- `e = depth N ≤ krullDim V(p) ≤ krullDim Supp(N/gN) = supportDim(N/gN)`.
  have := depthSup_le_krullDim_support_of_zeroLocus_subset hp hsub
  rw [depthSup_eq_natCast_of_isCohenMacaulay hCM he] at this
  exact_mod_cast this

/-- A module whose support dimension is a natural number is nontrivial. -/
theorem nontrivial_of_supportDim_eq_natCast {R : Type*} [CommRing R]
    {X : Type*} [AddCommGroup X] [Module R X] {k : ℕ}
    (h : Module.supportDim R X = (k : WithBot ℕ∞)) : Nontrivial X := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hs
  have hsupp : Module.support R X = ∅ := (Module.support_eq_empty_iff (R := R) (M := X)).mpr hs
  have hbot : Module.supportDim R X = ⊥ := by
    rw [show Module.supportDim R X = Order.krullDim (Module.support R X) from rfl, hsupp]
    exact Order.krullDim_eq_bot_iff.mpr (Set.isEmpty_coe_sort.mpr rfl)
  rw [hbot] at h
  exact absurd h.symm (by simp)

/-- **Kernel lemma — Stacks 00N5 / Lemma 10.103.3 (single-element step).**
For a finite, nonzero, Cohen-Macaulay module `N` of support dimension `e ≥ 1` over a
Noetherian local ring, if `g ∈ m` cuts the support dimension down by exactly one
(`dim Supp(N/gN) = e - 1`), then `g` is a nonzerodivisor on `N` and the quotient
`N/gN` is again nonzero and Cohen-Macaulay with `dim Supp(N/gN) = e - 1`.

The argument (Stacks 00N5).
Let `p ∈ Supp(N)` be a minimal prime of the support. Since `N` is CM, every associated
prime of `N` is a minimal prime of `Supp(N)`, and `dim(R/p) = dim Supp(N) = e` for each
such `p` (unmixedness of CM modules; in the Stacks development this is the content of
Lemma 10.103.2 / 00N4). Because `dim Supp(N/gN) = e - 1 < e`, the element `g` cannot lie
in any minimal/associated prime `p` of `N` (if it did, then `V(g) ⊇ {q : q ⊇ p}` would
contain a length-`e` chain inside `Supp(N) ∩ V(g) = Supp(N/gN)`, forcing
`dim Supp(N/gN) ≥ e`, contradiction). An element of `R` avoiding all associated primes of
`N` is a nonzerodivisor on `N` (`g ∉ ⋃ Ass(N)` ⇔ `IsSMulRegular N g`; the set of
zerodivisors on a module over a Noetherian ring is the union of its associated primes).
Hence `g` is `N`-regular. The short exact sequence `0 → N --g--> N → N/gN → 0` then shows
`depth(N/gN) = depth(N) - 1` (a nonzerodivisor in `m` drops depth by exactly one;
Stacks 00LE / `Module.depthSup` and the depth–regular-sequence relation). Combined with the
dimension drop `dim Supp(N/gN) = e - 1 = dim Supp(N) - 1` and CM-ness of `N`
(`dim Supp N = depth N = e`), we get `dim Supp(N/gN) = depth(N/gN)`, i.e. `N/gN` is CM.
Nontriviality of `N/gN` is immediate from `dim Supp(N/gN) = e - 1 ≥ 0 ≠ ⊥`
(`supportDim = ⊥ ⇔ module is zero`).
-/
@[ega "0 16.3.4" "necessity, special case",
  ega "0 16.5.5" "Implication b) ⇒ a)",
  ega "0 16.5.6" "b⇒a for r = 1"]
theorem stacks00N5_step
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (hCM : IsCohenMacaulay R N)
    (e : ℕ) (he : Module.supportDim R N = (e : WithBot ℕ∞)) (hpos : 1 ≤ e)
    (g : R)
    (hdrop : Module.supportDim R (N ⧸ (Ideal.span {g} • (⊤ : Submodule R N)))
      = ((e - 1 : ℕ) : WithBot ℕ∞)) :
    IsSMulRegular N g ∧
      Nontrivial (N ⧸ (Ideal.span {g} • (⊤ : Submodule R N))) := by
  refine ⟨?_, nontrivial_of_supportDim_eq_natCast hdrop⟩
  -- Regularity: by `biUnion_associatedPrimes_eq_compl_regular`, `g` is regular iff `g`
  -- avoids every associated prime. If `g ∈ p ∈ Ass(N)`, the unmixedness consequence
  -- `cohenMacaulay_supportDim_quotient_ge_of_associatedPrime` gives
  -- `supportDim(N/gN) ≥ e`, contradicting `supportDim(N/gN) = e-1 < e` (since `e ≥ 1`).
  rw [isSMulRegular_iff_forall_notMem_associatedPrimes]
  intro p hp hgp
  have hge := cohenMacaulay_supportDim_quotient_ge_of_associatedPrime hCM e he g p hp hgp
  rw [hdrop] at hge
  exact absurd hge (not_le.mpr (by exact_mod_cast Nat.sub_lt (by omega) (by omega)))

/- **Part (1) — `gs` is an `M`-regular sequence.**
Under the hypotheses of 00N6, the sequence `gs` is `M`-regular.

The argument.
Write `N_i = M/(g_1,…,g_i)M`. By Stacks 00KW
(`ringKrullDim_le_ringKrullDim_quotSMulTop_succ`), each one-element quotient drops the
support dimension by at most one, so along
`Supp(M) ⊇ Supp(N_1) ⊇ … ⊇ Supp(N_c)` the dimension drops by at most `1` per step;
the total drop is `d - (d - c) = c` over `c` steps, hence **each step drops by exactly
one**: `dim Supp(N_{i+1}) = dim Supp(N_i) - 1` for `i = 0,…,c-1` (a telescoping
`≤`-chain whose endpoints force every inequality to be an equality).
Now induct on `i` with `stacks00N5_step` (the kernel): `N_0 = M` is CM of dim `d`, and if
`N_i` is CM of dim `d - i ≥ 1` then `g_{i+1} ∈ m` with the exact-one-step drop makes
`g_{i+1}` a nonzerodivisor on `N_i` (so `IsSMulRegular (N_i) g_{i+1}`, which is exactly the
`regular_mod_prev` condition at index `i`) and `N_{i+1}` CM of dim `d - (i+1)`. Collecting
the nonzerodivisor conditions for all `i < c` gives `IsWeaklyRegular M gs`; together with
`top_ne_smul` — which holds because `N_c = M/(gs)M` is nonzero (its support dimension is
`d - c ≥ 0 ≠ ⊥`) — this is exactly `IsRegular M gs`.
-/
/- **The Rees depth-drop direction.**
If `g ∈ m` is a nonzerodivisor on a finite nonzero module `M` with `M/gM ≠ 0`, then
`depth M ≤ depth(M/gM) + 1`. (Combined with the easy direction this gives equality, but
only this inequality is needed for CM-propagation.)

The argument. Via the
Rees / Ext characterization of depth `depth X = inf { i | Ext^i_R(R/m, X) ≠ 0 }` and the
short exact sequence `0 → M --·g--> M → M/gM → 0` (injective since `IsSMulRegular M g`):
applying `Ext^•(k,-)` (`k = R/m`), every `Ext^i(k,M)` is killed by `m ∋ g`, so `·g = 0`
on them and the long exact sequence breaks into
`0 → Ext^i(k,M) → Ext^i(k,M/gM) → Ext^{i+1}(k,M) → 0`. Reading off the least nonvanishing
index gives `depth(M/gM) = depth M − 1`, in particular `depth M ≤ depth(M/gM)+1`.
-/
/- **Exchange lemma for depth under a regular element (depth well-definedness).**
If `a, b ∈ m` are *both* nonzerodivisors on a finite nonzero module `M`, then quotienting
by either drops the depth by the same amount:
`depth(QuotSMulTop a M) = depth(QuotSMulTop b M)`.

This is the substantive "depth is well-defined / all maximal regular sequences have the
same length" content (Stacks 00LH).

The argument. The key step: if `a ∈ m` is `M`-regular and there exists an `M`-regular *pair*
`(r₁, r₂)` in `m`, then `m ∉ Ass(M/aM)`, i.e. there is an element of `m` regular on `M/aM` (a
relation-chase using only `isRegular_cons_iff` and `IsSMulRegular M a`; this is
`maximalIdeal_notMem_associatedPrimes_quotSMulTop_of_isSMulRegular_pair`). Combined with prime
avoidance (`Ideal.subset_union_prime`) over `Ass(M) ∪ Ass(M/aM)` and the permutation lemma
`IsLocalRing.isRegular_of_perm`, one runs the standard Rees exchange induction to show the two
depths agree. -/
open scoped Pointwise in
/-- Quotienting by `x` and then `y` is the same as quotienting by `y` and then `x`. -/
theorem nonempty_quotSMulTop_quotSMulTop_linearEquiv {R : Type*} [CommRing R] (x y : R)
    (X : Type*) [AddCommGroup X] [Module R X] :
    Nonempty (QuotSMulTop y (QuotSMulTop x X) ≃ₗ[R] QuotSMulTop x (QuotSMulTop y X)) := by
  have key : ∀ (u v : R),
      Nonempty (QuotSMulTop v (QuotSMulTop u X) ≃ₗ[R]
        (X ⧸ (u • (⊤ : Submodule R X) ⊔ v • (⊤ : Submodule R X)))) := by
    intro u v
    set S : Submodule R X := u • ⊤ with hS
    set T : Submodule R X := u • ⊤ ⊔ v • ⊤ with hT
    have hST : S ≤ T := le_sup_left
    have hmap : Submodule.map S.mkQ T = v • (⊤ : Submodule R (QuotSMulTop u X)) := by
      rw [hT, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
        ← Submodule.ideal_span_singleton_smul v ⊤, Submodule.map_smul'',
        Submodule.ideal_span_singleton_smul, Submodule.map_top, Submodule.range_mkQ]
    have e := Submodule.quotientQuotientEquivQuotient S T hST
    rw [hmap] at e
    exact ⟨e⟩
  obtain ⟨e1⟩ := key x y
  obtain ⟨e2⟩ := key y x
  have hcomm : x • (⊤ : Submodule R X) ⊔ y • ⊤ = y • (⊤ : Submodule R X) ⊔ x • ⊤ := sup_comm _ _
  exact ⟨e1.trans ((Submodule.quotEquivOfEq _ _ hcomm).trans e2.symm)⟩

/-- An `X`-regular element of `m` shows `m ∉ Ass(X)`. -/
theorem maximalIdeal_notMem_associatedPrimes_of_isSMulRegular_mem
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Type*} [AddCommGroup X] [Module R X] {s : R} (hs : s ∈ maximalIdeal R)
    (hsreg : IsSMulRegular X s) : maximalIdeal R ∉ associatedPrimes R X := by
  intro hmem
  exact isSMulRegular_iff_forall_notMem_associatedPrimes.1 hsreg _ hmem hs

/-- Prime avoidance over three finite modules none of which has `m` as associated prime. -/
theorem exists_mem_maximalIdeal_isSMulRegular₃
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (X₁ X₂ X₃ : Type*) [AddCommGroup X₁] [Module R X₁] [Module.Finite R X₁]
    [AddCommGroup X₂] [Module R X₂] [Module.Finite R X₂]
    [AddCommGroup X₃] [Module R X₃] [Module.Finite R X₃]
    (h₁ : maximalIdeal R ∉ associatedPrimes R X₁) (h₂ : maximalIdeal R ∉ associatedPrimes R X₂)
    (h₃ : maximalIdeal R ∉ associatedPrimes R X₃) :
    ∃ d ∈ maximalIdeal R, IsSMulRegular X₁ d ∧ IsSMulRegular X₂ d ∧ IsSMulRegular X₃ d := by
  classical
  set P : Finset (Ideal R) :=
    (associatedPrimes.finite R X₁).toFinset ∪ (associatedPrimes.finite R X₂).toFinset
      ∪ (associatedPrimes.finite R X₃).toFinset with hP
  have hmem_iff : ∀ p, p ∈ P ↔ p ∈ associatedPrimes R X₁ ∨ p ∈ associatedPrimes R X₂
      ∨ p ∈ associatedPrimes R X₃ := by
    intro p; rw [hP]; simp only [Finset.mem_union, Set.Finite.mem_toFinset]; tauto
  have hprime : ∀ p ∈ P, p.IsPrime := by
    intro p hp; rw [hmem_iff] at hp; rcases hp with hp | hp | hp <;> exact hp.isPrime
  have hnotle : ∀ p ∈ P, ¬ (maximalIdeal R ≤ p) := by
    intro p hp hle
    have hpm : p = maximalIdeal R :=
      (maximalIdeal.isMaximal R).eq_of_le (hprime p hp).ne_top hle |>.symm
    rw [hmem_iff, hpm] at hp
    rcases hp with hp | hp | hp
    · exact h₁ hp
    · exact h₂ hp
    · exact h₃ hp
  have hsub : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ p ∈ (P : Set (Ideal R)), (p : Set R)) := by
    rcases P.eq_empty_or_nonempty with hE | ⟨w, hw⟩
    · simp only [hE, Finset.coe_empty, Set.mem_empty_iff_false, Set.iUnion_of_empty,
        Set.iUnion_empty]
      intro hc; exact hc (Submodule.zero_mem _)
    · rw [Ideal.subset_union_prime w w (fun i hi _ _ => hprime i hi)]
      push Not; intro p hp; exact hnotle p hp
  rw [Set.not_subset] at hsub
  obtain ⟨d, hdm, hdnot⟩ := hsub
  simp only [Set.mem_iUnion₂, not_exists] at hdnot
  refine ⟨d, hdm, ?_, ?_, ?_⟩ <;> rw [isSMulRegular_iff_forall_notMem_associatedPrimes] <;>
    intro p hp <;> exact hdnot p (by rw [Finset.mem_coe, hmem_iff]; tauto)

open scoped Pointwise in
/-- If `c` is `X`-regular and `(r₁, r₂)` is an `X`-regular pair in `m`, then
`m ∉ Ass(X / cX)`. -/
theorem maximalIdeal_notMem_associatedPrimes_quotSMulTop_of_isSMulRegular_pair
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X]
    {c : R} (hareg' : IsSMulRegular X c) {r₁ r₂ : R} (hr₁m : r₁ ∈ maximalIdeal R)
    (hr₂m : r₂ ∈ maximalIdeal R) (hr₁ : IsSMulRegular X r₁)
    (hr₂ : IsSMulRegular (QuotSMulTop r₁ X) r₂) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop c X) := by
  intro hmem
  have hmem' : IsAssociatedPrime (maximalIdeal R) (QuotSMulTop c X) := hmem
  rw [isAssociatedPrime_iff] at hmem'
  obtain ⟨hprime, xb, hxb⟩ := hmem'
  obtain ⟨x, rfl⟩ := (c • (⊤ : Submodule R X)).mkQ_surjective xb
  set q := (c • (⊤ : Submodule R X)).mkQ with hq
  have hxne : q x ≠ 0 := by
    intro h; rw [h] at hxb; apply hprime.ne_top
    rw [hxb]; ext r; simp [Submodule.mem_colon_singleton]
  have key : ∀ r ∈ maximalIdeal R, ∃ y, c • y = r • x := by
    intro r hr
    have hkill : r • q x = 0 := by
      have : r ∈ (⊥ : Submodule R (QuotSMulTop c X)).colon {q x} := by rw [← hxb]; exact hr
      rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at this
    have hrx : r • x ∈ c • (⊤ : Submodule R X) := by
      have : q (r • x) = 0 := by rw [map_smul, hkill]
      rwa [hq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hrx
    exact ⟨y, hy⟩
  obtain ⟨y₁, hy₁⟩ := key r₁ hr₁m
  obtain ⟨y₂, hy₂⟩ := key r₂ hr₂m
  have hcross : c • (r₂ • y₁) = c • (r₁ • y₂) := by
    have : r₂ • (c • y₁) = r₁ • (c • y₂) := by rw [hy₁, hy₂, smul_comm r₂ r₁ x]
    rwa [smul_comm r₂ c y₁, smul_comm r₁ c y₂] at this
  have hrel : r₂ • y₁ = r₁ • y₂ := hareg' hcross
  set p := (r₁ • (⊤ : Submodule R X)).mkQ with hp
  have hkill2 : r₂ • p y₁ = 0 := by
    rw [hp, ← map_smul, hrel, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨y₂, trivial, rfl⟩
  have hpy₁ : p y₁ = 0 := hr₂ (hkill2.trans (smul_zero r₂).symm)
  rw [hp, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at hpy₁
  obtain ⟨w, -, hw⟩ := hpy₁
  apply hxne
  rw [hq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    hr₁ (show r₁ • x = r₁ • (c • w) by rw [← hy₁, ← hw, smul_comm c r₁ w]),
    Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨w, trivial, rfl⟩

/-- If `(x, y)` is `X`-regular (with `X / (x, y)X ≠ 0`), then `x` is regular on `X / yX`. -/
theorem isSMulRegular_quotSMulTop_of_isSMulRegular_quotSMulTop
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X] {x y : R}
    [Nontrivial (QuotSMulTop y (QuotSMulTop x X))] (hx : IsSMulRegular X x)
    (hy : IsSMulRegular (QuotSMulTop x X) y) : IsSMulRegular (QuotSMulTop y X) x := by
  have hxy : IsRegular X [x, y] :=
    (isRegular_cons_iff X x [y]).2 ⟨hx, (isRegular_cons_iff _ y []).2 ⟨hy, IsRegular.nil R _⟩⟩
  obtain ⟨_, h⟩ := (isRegular_cons_iff X y [x]).mp
    (IsLocalRing.isRegular_of_perm hxy (List.Perm.swap x y []).symm)
  exact ((isRegular_cons_iff (QuotSMulTop y X) x []).mp h).left

/-- If `X` has a regular sequence of length `n` in `m` and `c ∈ m` is `X`-regular, then
`X / cX` has a regular sequence of length `n - 1` in `m`. -/
theorem exists_isRegular_quotSMulTop_of_isRegular
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] [Nontrivial X]
    (c : R) (hcm : c ∈ maximalIdeal R) (hcreg : IsSMulRegular X c)
    (h : ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular X rs) :
    ∃ us : List R, us.length = n - 1 ∧ (∀ r ∈ us, r ∈ maximalIdeal R) ∧
      IsRegular (QuotSMulTop c X) us := by
  induction n using Nat.strong_induction_on generalizing X c with
  | _ n ih =>
    obtain ⟨rs, hrslen, hrsmem, hrsreg⟩ := h
    have hQc : Nontrivial (QuotSMulTop c X) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal X hcm
    by_cases hn : n ≤ 1
    · refine ⟨[], by simp; omega, by simp, ?_⟩
      exact IsRegular.nil R (QuotSMulTop c X)
    · push Not at hn
      -- n ≥ 2, so rs = r₁ :: r₂ :: rest
      rcases rs with _ | ⟨r₁, _ | ⟨r₂, rest⟩⟩
      · simp at hrslen; omega
      · simp at hrslen; omega
      · have hr₁m : r₁ ∈ maximalIdeal R := hrsmem r₁ (by simp)
        have hr₂m : r₂ ∈ maximalIdeal R := hrsmem r₂ (by simp)
        obtain ⟨hr₁reg, htail_reg⟩ := (isRegular_cons_iff X r₁ (r₂ :: rest)).mp hrsreg
        obtain ⟨hr₂reg, hrest_reg⟩ :=
          (isRegular_cons_iff (QuotSMulTop r₁ X) r₂ rest).mp htail_reg
        obtain ⟨bb, hbbm, -, hbbc, hbbr₁⟩ :=
          exists_mem_maximalIdeal_isSMulRegular₃ X (QuotSMulTop c X) (QuotSMulTop r₁ X)
            (maximalIdeal_notMem_associatedPrimes_of_isSMulRegular_mem hcm hcreg)
            (maximalIdeal_notMem_associatedPrimes_quotSMulTop_of_isSMulRegular_pair X hcreg hr₁m
              hr₂m hr₁reg hr₂reg)
            (maximalIdeal_notMem_associatedPrimes_of_isSMulRegular_mem hr₂m hr₂reg)
        have : Nontrivial (QuotSMulTop bb X) := nontrivial_quotSMulTop_of_mem_maximalIdeal X hbbm
        have : Nontrivial (QuotSMulTop r₁ X) := nontrivial_quotSMulTop_of_mem_maximalIdeal X hr₁m
        have : Nontrivial (QuotSMulTop bb (QuotSMulTop c X)) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal (QuotSMulTop c X) hbbm
        have : Nontrivial (QuotSMulTop bb (QuotSMulTop r₁ X)) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal (QuotSMulTop r₁ X) hbbm
        have htail_len : (r₂ :: rest).length = n - 1 := by simp at hrslen ⊢; omega
        obtain ⟨v, hvlen, hvmem, hvreg⟩ := ih (n - 1) (by omega) (QuotSMulTop r₁ X) bb hbbm hbbr₁
          ⟨r₂ :: rest, htail_len, fun r hr => hrsmem r (by simp [hr]), htail_reg⟩
        obtain ⟨esw1⟩ := nonempty_quotSMulTop_quotSMulTop_linearEquiv r₁ bb X
        obtain ⟨z, hzlen, hzmem, hzreg⟩ := ih (n - 1) (by omega) (QuotSMulTop bb X) c hcm
          (isSMulRegular_quotSMulTop_of_isSMulRegular_quotSMulTop hcreg hbbc)
          ⟨r₁ :: v, by simp [hvlen]; omega, List.forall_mem_cons.mpr ⟨hr₁m, hvmem⟩,
            (isRegular_cons_iff _ _ _).mpr
              ⟨isSMulRegular_quotSMulTop_of_isSMulRegular_quotSMulTop hr₁reg hbbr₁,
                (LinearEquiv.isRegular_congr esw1 v).mp hvreg⟩⟩
        obtain ⟨esw2⟩ := nonempty_quotSMulTop_quotSMulTop_linearEquiv bb c X
        exact ⟨bb :: z, by simp [hzlen]; omega, List.forall_mem_cons.mpr ⟨hbbm, hzmem⟩,
          (isRegular_cons_iff _ _ _).mpr ⟨hbbc, (LinearEquiv.isRegular_congr esw2 z).mp hzreg⟩⟩

/-- Quotienting by an `M`-regular element of `m` drops the depth by exactly one. -/
@[ega "0 16.4.6", sga "2 III 2.5" "special case", sga "2 XII 3.4" "more general"]
theorem depthSup_eq_depthSup_quotSMulTop_add_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {s : R} (hsm : s ∈ maximalIdeal R) (hsreg : IsSMulRegular M s) :
    Module.depthSup R (maximalIdeal R) M
      = Module.depthSup R (maximalIdeal R) (QuotSMulTop s M) + 1 := by
  have : Nontrivial (QuotSMulTop s M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hsm
  apply le_antisymm
  · rw [show Module.depthSup R (maximalIdeal R) M
        = sSup {n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R)
            ∧ RingTheory.Sequence.IsRegular M rs} from rfl]
    apply sSup_le
    rintro n ⟨rs, rfl, hmem, hreg⟩
    obtain ⟨u, hulen, humem, hureg⟩ :=
      exists_isRegular_quotSMulTop_of_isRegular rs.length M s hsm hsreg ⟨rs, rfl, hmem, hreg⟩
    have hle : (u.length : ℕ∞) ≤ Module.depthSup R (maximalIdeal R) (QuotSMulTop s M) := by
      apply le_sSup; exact ⟨u, rfl, humem, hureg⟩
    rw [hulen] at hle
    calc (rs.length : ℕ∞) ≤ ((rs.length - 1 : ℕ) : ℕ∞) + 1 := by
            rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, ← Nat.cast_add]
            exact_mod_cast (by omega : rs.length ≤ rs.length - 1 + 1)
      _ ≤ Module.depthSup R (maximalIdeal R) (QuotSMulTop s M) + 1 := by gcongr
  · rw [show Module.depthSup R (maximalIdeal R) (QuotSMulTop s M)
        = sSup {n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R)
            ∧ RingTheory.Sequence.IsRegular (QuotSMulTop s M) rs} from rfl]
    have hSne : {n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R)
            ∧ RingTheory.Sequence.IsRegular (QuotSMulTop s M) rs}.Nonempty :=
      ⟨0, [], by simp, by simp, IsRegular.nil R (QuotSMulTop s M)⟩
    rw [ENat.sSup_add hSne]
    apply iSup₂_le
    rintro n ⟨rs, rfl, hmem, hreg⟩
    have hsreg_cons : IsRegular M (s :: rs) := by
      rw [isRegular_cons_iff]; exact ⟨hsreg, hreg⟩
    have hmem' : ∀ r ∈ (s :: rs), r ∈ maximalIdeal R := by
      intro r hr; rcases List.mem_cons.mp hr with h | h
      · exact h ▸ hsm
      · exact hmem r h
    have hle : ((s :: rs).length : ℕ∞) ≤ Module.depthSup R (maximalIdeal R) M := by
      apply le_sSup; exact ⟨s :: rs, rfl, hmem', hsreg_cons⟩
    rw [List.length_cons, Nat.cast_add, Nat.cast_one] at hle
    exact hle

-- needed: `depth_quotSMulTop_eq_of_isSMulRegular` closes with
-- `WithTop.add_right_cancel (by simp)`, whose `simp` needs defeq to unfold `Module.depthSup`'s
-- `ℕ∞` wrapper.
set_option backward.isDefEq.respectTransparency false in
/-- Quotienting by either of two `M`-regular elements of `m` drops the depth by the same
amount, so `depth (M / aM) = depth (M / bM)`. -/
theorem depth_quotSMulTop_eq_of_isSMulRegular
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (a b : R) (ha : a ∈ maximalIdeal R) (hb : b ∈ maximalIdeal R)
    (hareg : IsSMulRegular M a) (hbreg : IsSMulRegular M b) :
    Module.depthSup R (maximalIdeal R) (QuotSMulTop a M)
      = Module.depthSup R (maximalIdeal R) (QuotSMulTop b M) := by
  have hfin : Module.depthSup R (maximalIdeal R) (QuotSMulTop a M) + 1
       = Module.depthSup R (maximalIdeal R) (QuotSMulTop b M) + 1 := by
    rw [← depthSup_eq_depthSup_quotSMulTop_add_one ha hareg,
      ← depthSup_eq_depthSup_quotSMulTop_add_one hb hbreg]
  exact WithTop.add_right_cancel (by simp) hfin

/-- The Rees depth-drop bound: for `g ∈ m` regular on a finite nonzero `M` with `M / gM ≠ 0`,
`depth M ≤ depth (M / gM) + 1`. -/
@[ega "0 16.4.6" "(ii)",
  sga "2 III 2.5" "partial",
  sga "2 X 2.1" "partial",
  sga "2 XII 3.4" "partial"]
theorem depth_le_depth_quotSMulTop_succ
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (g : R) (hg : g ∈ maximalIdeal R) (hreg : IsSMulRegular M g) :
    Module.depthSup R (maximalIdeal R) M
      ≤ Module.depthSup R (maximalIdeal R) (QuotSMulTop g M) + 1 := by
  -- `depth M = sSup {n | ∃ M-regular rs in m of length n}`. Reduce by `sSup_le`.
  rw [show Module.depthSup R (maximalIdeal R) M
      = sSup {n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R)
          ∧ RingTheory.Sequence.IsRegular M rs} from rfl]
  apply sSup_le
  rintro n ⟨rs, rfl, hmem, hreg_rs⟩
  -- If `rs = []` the bound is trivial. Otherwise `rs = r₁ :: rest`; `rest` is an
  -- `(QuotSMulTop r₁ M)`-regular sequence in `m` of length `rs.length - 1`, and `r₁` is
  -- `M`-regular. The exchange lemma transports the bound from `QuotSMulTop r₁ M` to
  -- `QuotSMulTop g M`.
  rcases rs with _ | ⟨r₁, rest⟩
  · simp
  · -- decompose `r₁ :: rest`.
    have hr₁mem : r₁ ∈ maximalIdeal R := hmem r₁ (by simp)
    have hrestmem : ∀ r ∈ rest, r ∈ maximalIdeal R := fun r hr => hmem r (by simp [hr])
    obtain ⟨hr₁reg, hrest_reg⟩ := (RingTheory.Sequence.isRegular_cons_iff M r₁ rest).mp hreg_rs
    -- `rest` is `(QuotSMulTop r₁ M)`-regular of length `rest.length`.
    have hrest_le : (rest.length : ℕ∞)
        ≤ Module.depthSup R (maximalIdeal R) (QuotSMulTop r₁ M) :=
      le_sSup ⟨rest, rfl, hrestmem, hrest_reg⟩
    -- exchange `r₁` for `g`.
    have hexch : Module.depthSup R (maximalIdeal R) (QuotSMulTop r₁ M)
        = Module.depthSup R (maximalIdeal R) (QuotSMulTop g M) :=
      depth_quotSMulTop_eq_of_isSMulRegular r₁ g hr₁mem hg hr₁reg hreg
    rw [hexch] at hrest_le
    -- conclude `(r₁ :: rest).length ≤ depth(QuotSMulTop g M) + 1`.
    calc ((r₁ :: rest).length : ℕ∞) = (rest.length : ℕ∞) + 1 := by
            push_cast [List.length_cons]; ring
      _ ≤ Module.depthSup R (maximalIdeal R) (QuotSMulTop g M) + 1 := by gcongr

/-- **Cohen–Macaulay propagation.**
If `N` is CM with `supportDim N = e ≥ 1`, `g ∈ m`, and `supportDim(QuotSMulTop g N) = e−1`,
then `QuotSMulTop g N` is again Cohen–Macaulay (necessarily of `supportDim = depth = e−1`).

The argument. By the kernel `stacks00N5_step` (via the
`Ideal.span {g} • ⊤ = g • ⊤` bridge `Submodule.ideal_span_singleton_smul`), `g` is regular
on `N` and `QuotSMulTop g N ≠ 0`. CM is `supportDim = depth`. We have
`supportDim(QuotSMulTop g N) = e−1` by hypothesis, so it suffices to show
`depth(QuotSMulTop g N) = e−1`:
• `≤`: the 00LK bound `depth_le_krullDim_zeroLocus_of_mem_associatedPrimes` ⇒
  `depth X ≤ supportDim X` for finite nonzero `X` (here `= e−1`).
• `≥`: `depth N = supportDim N = e` (CM of `N`); the Rees depth-drop bound gives
  `depth N ≤ depth(QuotSMulTop g N) + 1`, so `depth(QuotSMulTop g N) ≥ e−1`.
-/
theorem cohenMacaulay_quotSMulTop_of_dimDrop
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (hCM : IsCohenMacaulay R N)
    (e : ℕ) (he : Module.supportDim R N = (e : WithBot ℕ∞)) (hpos : 1 ≤ e)
    (g : R) (hg : g ∈ maximalIdeal R)
    [Nontrivial (QuotSMulTop g N)]
    (hdrop : Module.supportDim R (QuotSMulTop g N) = ((e - 1 : ℕ) : WithBot ℕ∞)) :
    IsCohenMacaulay R (QuotSMulTop g N) := by
  -- Bridge: convert `hdrop` into the `Ideal.span {g} • ⊤` form.
  have hdrop' : Module.supportDim R (N ⧸ (Ideal.span {g} • (⊤ : Submodule R N)))
      = ((e - 1 : ℕ) : WithBot ℕ∞) := by
    rw [Submodule.ideal_span_singleton_smul]; exact hdrop
  -- `g` is regular on `N` (kernel 00N5).
  obtain ⟨hreg, _⟩ := stacks00N5_step hCM e he hpos g hdrop'
  -- It suffices to prove the depth equation in `ℕ∞`.
  -- (A) depth(QuotSMulTop g N) ≤ ↑(e-1).
  have hle : (Module.depthSup R (maximalIdeal R) (QuotSMulTop g N) : WithBot ℕ∞)
      ≤ ((e - 1 : ℕ) : WithBot ℕ∞) := by
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R (QuotSMulTop g N)
    exact (depthSup_le_krullDim_support_of_zeroLocus_subset hp
      (zeroLocus_subset_support_of_mem_associatedPrimes hp)).trans hdrop.le
  -- (B) ↑(e-1) ≤ depth(QuotSMulTop g N).
  have hge : ((e - 1 : ℕ) : WithBot ℕ∞)
      ≤ (Module.depthSup R (maximalIdeal R) (QuotSMulTop g N) : WithBot ℕ∞) := by
    have hHA := depth_le_depth_quotSMulTop_succ g hg hreg
    -- depth N = e
    rw [depthSup_eq_natCast_of_isCohenMacaulay hCM he,
      natCast_eq_natCast_sub_one_add_one hpos] at hHA
    exact WithBot.coe_le_coe.mpr ((WithTop.add_le_add_iff_right WithTop.one_ne_top).mp hHA)
  -- Conclude.
  change Module.supportDim R (QuotSMulTop g N)
    = (Module.depthSup R (maximalIdeal R) (QuotSMulTop g N) : WithBot ℕ∞)
  rw [hdrop]
  exact le_antisymm hge hle

open scoped Pointwise in
/-- `(N / gN) / (gs)(N / gN)` is isomorphic to `N / (g :: gs)N`. -/
theorem nonempty_quotSMulTop_quotient_ofList_linearEquiv
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] (g : R) (gs : List R) :
    Nonempty (((QuotSMulTop g N) ⧸ (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N))))
      ≃ₗ[R] (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N)))) := by
  set S : Submodule R N := g • ⊤ with hS
  set T : Submodule R N := Ideal.ofList (g :: gs) • ⊤ with hT
  have hgbot : g • (⊤ : Submodule R (QuotSMulTop g N)) = ⊥ := by
    calc g • (⊤ : Submodule R (N ⧸ (g • ⊤ : Submodule R N)))
        = Ideal.span {g} • (⊤ : Submodule R (N ⧸ (g • ⊤ : Submodule R N))) := by
          rw [Submodule.ideal_span_singleton_smul]
      _ = Ideal.span {g} • Submodule.map (g • ⊤ : Submodule R N).mkQ ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]
      _ = Submodule.map (g • ⊤ : Submodule R N).mkQ (Ideal.span {g} • ⊤) := by
          rw [Submodule.map_smul'']
      _ = Submodule.map (g • ⊤ : Submodule R N).mkQ (g • ⊤) := by
          rw [Submodule.ideal_span_singleton_smul]
      _ = ⊥ := Submodule.mkQ_map_self _
  have hST : S ≤ T := by
    rw [hS, hT, Ideal.ofList_cons, Submodule.sup_smul, ← Submodule.ideal_span_singleton_smul g ⊤]
    exact le_sup_left
  have hmap : Submodule.map S.mkQ T = Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)) := by
    rw [hT, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
      Ideal.ofList_cons, Submodule.sup_smul, Submodule.ideal_span_singleton_smul, hgbot,
      bot_sup_eq]
  have e := Submodule.quotientQuotientEquivQuotient S T hST
  rw [hmap] at e
  exact ⟨e⟩

open scoped Pointwise in
/-- `(QuotSMulTop g N) ⧸ ofList gs • ⊤` and `N ⧸ ofList (g :: gs) • ⊤` have the same support
dimension. -/
theorem quotOfList_cons_supportDim_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (g : R) (gs : List R) :
    Module.supportDim R ((QuotSMulTop g N) ⧸ (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g
        N))))
      = Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N))) :=
  (nonempty_quotSMulTop_quotient_ofList_linearEquiv (N := N) g gs).elim
    Module.supportDim_eq_of_equiv

/-- Iterating `supportDim M ≤ supportDim (M / aM) + 1` over a list `l ⊆ m`:
`supportDim M ≤ supportDim (M / (l) M) + |l|`. -/
theorem supportDim_le_supportDim_quotient_ofList_add_length
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (l : List R) :
    (∀ x ∈ l, x ∈ maximalIdeal R) →
      Module.supportDim R M ≤
        Module.supportDim R (M ⧸ (Ideal.ofList l • (⊤ : Submodule R M)))
          + (l.length : WithBot ℕ∞) := by
  induction l generalizing M with
  | nil =>
    intro _
    simp only [List.length_nil, Nat.cast_zero, add_zero]
    rw [Ideal.ofList_nil, Submodule.bot_smul]
    exact (Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl).symm).le
  | cons a as ih =>
    intro hmem
    have hih := ih (QuotSMulTop a M) fun x hx => hmem x (by simp [hx])
    have hlen' : ((a :: as).length : WithBot ℕ∞) = (as.length : WithBot ℕ∞) + 1 := by
      push_cast [List.length_cons]
      ring
    calc Module.supportDim R M
        ≤ Module.supportDim R (QuotSMulTop a M) + 1 :=
          Module.supportDim_le_supportDim_quotSMulTop_succ (hmem a (by simp))
      _ ≤ (Module.supportDim R
            ((QuotSMulTop a M) ⧸ (Ideal.ofList as • (⊤ : Submodule R (QuotSMulTop a M))))
            + (as.length : WithBot ℕ∞)) + 1 := by gcongr
      _ = Module.supportDim R (M ⧸ (Ideal.ofList (a :: as) • (⊤ : Submodule R M)))
            + ((a :: as).length : WithBot ℕ∞) := by
            rw [quotOfList_cons_supportDim_eq (N := M) a as, hlen']; ring

/-- If `supportDim N = e ≥ 1`, `g ∈ m` and `supportDim (N / gN) ≤ e - 1`, then equality holds. -/
theorem supportDim_quotSMulTop_eq_sub_one_of_le
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] {e : ℕ}
    (he : Module.supportDim R N = (e : WithBot ℕ∞)) (hpos : 1 ≤ e) {g : R}
    (hg : g ∈ maximalIdeal R)
    (hup : Module.supportDim R (QuotSMulTop g N) ≤ ((e - 1 : ℕ) : WithBot ℕ∞)) :
    Module.supportDim R (QuotSMulTop g N) = ((e - 1 : ℕ) : WithBot ℕ∞) := by
  have hlow : (e : WithBot ℕ∞) ≤ Module.supportDim R (QuotSMulTop g N) + 1 := by
    rw [← he]; exact Module.supportDim_le_supportDim_quotSMulTop_succ hg
  rw [natCast_eq_natCast_sub_one_add_one hpos] at hlow
  exact le_antisymm hup (ENat.WithBot.add_le_add_natCast_right_iff.mp hlow)

/-- If `supportDim N = e` and the list `g :: gs ⊆ m` drops it by its length, then
`supportDim (N / gN) = e - 1`. -/
theorem supportDim_quotSMulTop_eq_sub_one_of_dimDrop
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] {e : ℕ}
    (he : Module.supportDim R N = (e : WithBot ℕ∞)) {g : R} (hg : g ∈ maximalIdeal R)
    {gs : List R} (hmem : ∀ x ∈ gs, x ∈ maximalIdeal R) (hk : gs.length + 1 ≤ e)
    (hdimQ : Module.supportDim R
          ((QuotSMulTop g N) ⧸ (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N))))
        = ((e - (gs.length + 1) : ℕ) : WithBot ℕ∞)) :
    Module.supportDim R (QuotSMulTop g N) = ((e - 1 : ℕ) : WithBot ℕ∞) := by
  have hup := supportDim_le_supportDim_quotient_ofList_add_length (QuotSMulTop g N) gs hmem
  have hsum : ((e - (gs.length + 1) : ℕ) : WithBot ℕ∞) + (gs.length : WithBot ℕ∞)
      = ((e - 1 : ℕ) : WithBot ℕ∞) := by
    rw [← Nat.cast_add]; congr 1; omega
  rw [hdimQ, hsum] at hup
  exact supportDim_quotSMulTop_eq_sub_one_of_le he (by omega) hg hup

open scoped Pointwise in
/-- **Regularity from dimension drop.**
General form of part (1): a CM module `N` of `supportDim = e`, a list `gs` of length `k ≤ e`
of elements of `m` such that `supportDim(N ⧸ ofList gs • ⊤) = e − k`, is `N`-regular.
Proved by induction on `gs` (with `N`, `e`, `k` generalizing), `isRegular_cons_iff` at each
step, the kernel `stacks00N5_step` for the head regularity, and Cohen–Macaulay propagation to
`QuotSMulTop g N` for the recursive call. The bridge identifying
`N ⧸ ofList (g :: gs) • ⊤` with `(QuotSMulTop g N) ⧸ ofList gs • ⊤` (and its `supportDim`)
is `quotOfList_cons_supportDim_eq`. The per-step exact-one-drop comes from the
00KW bound `Module.supportDim_le_supportDim_quotSMulTop_succ` pinching the telescoping
inequality. -/
@[ega "0 16.3.4" "necessity, special case",
  ega "0 16.5.5" "Implication b) ⇒ a)",
  ega "0 16.5.6" "b⇒a",
  ega "0 16.5.7" "partial"]
theorem isRegular_of_cm_dimDrop_engine
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (e : ℕ) (he : Module.supportDim R N = (e : WithBot ℕ∞))
    (hCM : IsCohenMacaulay R N)
    (gs : List R) (hlen : gs.length ≤ e)
    (hmem : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hdim : Module.supportDim R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N)))
      = ((e - gs.length : ℕ) : WithBot ℕ∞)) :
    IsRegular N gs := by
  -- Main induction.
  induction gs generalizing N e with
  | nil => exact RingTheory.Sequence.IsRegular.nil R N
  | cons g gs' ih =>
    rw [RingTheory.Sequence.isRegular_cons_iff]
    -- basic facts
    have hg : g ∈ maximalIdeal R := hmem g (by simp)
    have hlen₁ : gs'.length + 1 ≤ e := hlen
    have hmemtail : ∀ x ∈ gs', x ∈ maximalIdeal R := fun x hx => hmem x (by simp [hx])
    -- bridge for the head: supportDim((QuotSMulTop g N) ⧸ ofList gs' • ⊤)
    --   = supportDim(N ⧸ ofList (g::gs') • ⊤)
    have hbridgeN := quotOfList_cons_supportDim_eq (N := N) g gs'
    -- supportDim((QuotSMulTop g N) ⧸ ofList gs' • ⊤) = e - (gs'.length + 1)
    have hdimQ : Module.supportDim R
          ((QuotSMulTop g N) ⧸ (Ideal.ofList gs' • (⊤ : Submodule R (QuotSMulTop g N))))
        = ((e - (gs'.length + 1) : ℕ) : WithBot ℕ∞) := by
      rw [hbridgeN, hdim]
      simp only [List.length_cons]
    have hdrop : Module.supportDim R (QuotSMulTop g N) = ((e - 1 : ℕ) : WithBot ℕ∞) :=
      supportDim_quotSMulTop_eq_sub_one_of_dimDrop he hg hmemtail
        hlen₁ hdimQ
    -- head regularity via the kernel 00N5
    have hdrop' : Module.supportDim R (N ⧸ (Ideal.span {g} • (⊤ : Submodule R N)))
        = ((e - 1 : ℕ) : WithBot ℕ∞) := by
      rw [Submodule.ideal_span_singleton_smul]; exact hdrop
    obtain ⟨hreg, hnt'⟩ := stacks00N5_step hCM e he (by omega) g hdrop'
    refine ⟨hreg, ?_⟩
    -- recursive call on the tail
    have : Nontrivial (QuotSMulTop g N) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal N hg
    have hCMQ : IsCohenMacaulay R (QuotSMulTop g N) :=
      cohenMacaulay_quotSMulTop_of_dimDrop hCM e he (by omega) g hg hdrop
    have hdimtail : Module.supportDim R
          ((QuotSMulTop g N) ⧸ (Ideal.ofList gs' • (⊤ : Submodule R (QuotSMulTop g N))))
        = (((e - 1) - gs'.length : ℕ) : WithBot ℕ∞) := by
      rw [hdimQ]; congr 1; omega
    exact ih (e - 1) hdrop hCMQ (by omega) hmemtail hdimtail

/-- A family `gs ⊆ m` that drops the support dimension of a Cohen-Macaulay module by its own
length is an `M`-regular sequence. -/
@[ega "0 16.3.4" "necessity, special case",
  ega "0 16.5.5" "Implication b) ⇒ a)",
  ega "0 16.5.6" "b⇒a",
  ega "0 16.5.7" "partial"]
theorem cohenMacaulay_dimDrop_isRegular
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d c : ℕ) (hcd : c ≤ d) (hd : Module.supportDim R M = (d : WithBot ℕ∞))
    (hCM : IsCohenMacaulay R M)
    (gs : List R) (hgs_len : gs.length = c)
    (hgs_mem : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hdim : Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M)))
      = ((d - c : ℕ) : WithBot ℕ∞)) :
    IsRegular M gs := by
  -- Apply the general engine with `N = M`, `e = d`, `k = c`.
  refine isRegular_of_cm_dimDrop_engine d hd hCM gs (hgs_len ▸ hcd) hgs_mem ?_
  rw [hgs_len]; exact hdim

/-- **A length-`depth` regular sequence in `m` is maximal.**
If `gs` is an `M`-regular sequence with all entries in `m`, of length equal to
`depth M` (a finite value), then `gs` is a maximal `M`-regular sequence.

The argument.
`depth M = sSup { n | ∃ rs, |rs| = n ∧ rs ⊆ m ∧ IsRegular M rs }` (the Mathlib
definition of `Module.depthSup`). If some `g ∈ m` extended `gs` to a regular sequence
`gs ++ [g]`, that sequence would have length `depth M + 1` and lie in `m`, so
`depth M + 1 ≤ sSup(…) = depth M`, impossible for the finite cardinal `depth M`
(`hfin : depth M ≠ ⊤`). Hence no such `g` exists, which is exactly maximality. -/
theorem maximal_of_length_eq_depth
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (gs : List R) (hmem : ∀ g ∈ gs, g ∈ maximalIdeal R) (hreg : IsRegular M gs)
    (hlen : (gs.length : ℕ∞) = Module.depthSup R (maximalIdeal R) M)
    (hfin : Module.depthSup R (maximalIdeal R) M ≠ ⊤) :
    IsMaximalRegularSequence R M gs := by
  refine ⟨hmem, hreg, ?_⟩
  rintro ⟨g, hg, hgreg⟩
  -- `gs ++ [g]` is a regular sequence in `m`, so its length bounds the depth.
  have hmem' : ∀ r ∈ gs ++ [g], r ∈ maximalIdeal R := by
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact hmem r h
    · simpa using (List.mem_singleton.mp h) ▸ hg
  have hbound :
      ((gs ++ [g]).length : ℕ∞) ≤ Module.depthSup R (maximalIdeal R) M :=
    le_sSup ⟨gs ++ [g], rfl, hmem', hgreg⟩
  rw [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one,
    hlen] at hbound
  -- `depth M + 1 ≤ depth M` with `depth M ≠ ⊤` is impossible.
  rw [ENat.add_one_le_iff hfin] at hbound
  exact absurd hbound (lt_irrefl _)

open scoped Pointwise in
-- needed: `supportDim_quotSMulTop_le_of_avoid_minimalPrimes`'s `simp only [lN',
-- RelSeries.cons_length, ...]` needs defeq through the `Set.inclusion` coercion on
-- `Module.support` to see the `LTSeries` length.
set_option backward.isDefEq.respectTransparency false in
/-- **Strict dimension drop by a parameter avoiding the minimal primes.**
If `g` avoids every minimal prime of `Ann(N)` (equivalently, every generic point of
`Supp N`), then cutting by `g` drops the support dimension by at least one:
`supportDim(QuotSMulTop g N) ≤ e - 1` where `e = supportDim N ≥ 1`. The proof is the
chain argument: any prime in `Supp N ∩ V(g)` strictly dominates a minimal prime of `Ann N`
(which avoids `g`), so a length-`e` chain in the cut would prolong to a length-`(e+1)`
chain in `Supp N`, exceeding `dim Supp N = e`. -/
@[ega "0 16.1.2" "special case",
  ega "0 16.2.3.1" "clause (ii), local case",
  ega "0 16.3.4" "sufficiency"]
theorem supportDim_quotSMulTop_le_of_avoid_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (g : R) (e : ℕ)
    (he : Module.supportDim R N = (e : WithBot ℕ∞)) (hpos : 1 ≤ e)
    (hgmin : ∀ p ∈ (Module.annihilator R N).minimalPrimes, g ∉ p) :
    Module.supportDim R (QuotSMulTop g N) ≤ ((e - 1 : ℕ) : WithBot ℕ∞) := by
  have hTeq : Module.support R (QuotSMulTop g N)
      = Module.support R N ∩ PrimeSpectrum.zeroLocus {g} := Module.support_quotSMulTop g
  have hSdim : Order.krullDim (Module.support R N) = (e : WithBot ℕ∞) := he
  have hincl : Module.support R (QuotSMulTop g N) ⊆ Module.support R N := by
    rw [hTeq]; exact Set.inter_subset_left
  have hnoe : ¬ ((e : WithBot ℕ∞) ≤ Order.krullDim (Module.support R (QuotSMulTop g N))) := by
    rw [Order.le_krullDim_iff]
    rintro ⟨l, hl⟩
    have hqT2 : (l.head : PrimeSpectrum R)
        ∈ Module.support R N ∩ PrimeSpectrum.zeroLocus ({g} : Set R) := by
      rw [← hTeq]; exact l.head.property
    have hgq : g ∈ (l.head : PrimeSpectrum R).asIdeal := Set.singleton_subset_iff.mp hqT2.right
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
      (J := (l.head : PrimeSpectrum R).asIdeal) (Module.annihilator_le_of_mem_support hqT2.left)
    have hpprime : p.IsPrime := hp.isPrime
    have hplt : p < (l.head : PrimeSpectrum R).asIdeal :=
      lt_of_le_of_ne hpq (by rintro rfl; exact hgmin _ hp hgq)
    have hpS : (⟨p, hpprime⟩ : PrimeSpectrum R) ∈ Module.support R N :=
      Module.mem_support_iff_of_finite.mpr hp.le
    let lN : LTSeries (Module.support R N) := l.map (Set.inclusion hincl)
      (fun _ _ h => (Set.inclusion_lt_inclusion hincl).mpr h)
    have hnew : (⟨⟨p, hpprime⟩, hpS⟩ : Module.support R N) < lN.head := hplt
    let lN' := lN.cons ⟨⟨p, hpprime⟩, hpS⟩ hnew
    have hlen' : lN'.length = e + 1 := by
      simp only [lN', RelSeries.cons_length, lN, LTSeries.map_length, hl]
    have hk : ((e + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (Module.support R N) := by
      rw [Order.le_krullDim_iff]; exact ⟨lN', hlen'⟩
    rw [hSdim] at hk
    have hcontra : (e + 1 : ℕ) ≤ e := by exact_mod_cast hk
    omega
  have hlt : Order.krullDim (Module.support R (QuotSMulTop g N)) < (e : WithBot ℕ∞) :=
    lt_of_not_ge hnoe
  change Order.krullDim (Module.support R (QuotSMulTop g N)) ≤ ((e - 1 : ℕ) : WithBot ℕ∞)
  -- WithBot ℕ∞ arithmetic: `x < ↑e` with `e ≥ 1` gives `x ≤ ↑(e-1)`.
  set x := Order.krullDim (Module.support R (QuotSMulTop g N)) with hx
  clear_value x
  cases x with
  | bot => exact bot_le
  | coe a =>
    cases a with
    | top => simp at hlt
    | coe n =>
      have hn : (n : ℕ) < e := by
        have h3 : ((n : ℕ∞) : WithBot ℕ∞) < ((e : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hlt
        exact_mod_cast h3
      have hle : (n : ℕ) ≤ e - 1 := by omega
      have h4 : ((n : ℕ) : WithBot ℕ∞) ≤ ((e - 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hle
      simpa using h4

/-- A Cohen-Macaulay module of positive dimension does not have `m` as associated prime. -/
theorem not_maximalIdeal_le_of_mem_associatedPrimes_of_isCohenMacaulay
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (hCM : IsCohenMacaulay R N) {e : ℕ} (he : Module.supportDim R N = (e : WithBot ℕ∞))
    (hpos : 1 ≤ e) {p : Ideal R} (hp : p ∈ associatedPrimes R N) : ¬ maximalIdeal R ≤ p := by
  intro hpm
  have hdepthe := depthSup_eq_natCast_of_isCohenMacaulay hCM he
  -- `m ≤ p`, `p` prime ≠ ⊤, `m` maximal ⟹ `p = m`.
  have hpeq : p = maximalIdeal R :=
    ((maximalIdeal.isMaximal R).eq_of_le hp.isPrime.ne_top' hpm).symm
  have hle : (Module.depthSup R (maximalIdeal R) N : WithBot ℕ∞)
      ≤ Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) :=
    depth_le_krullDim_zeroLocus_of_mem_associatedPrimes p hp
  -- V(m) is a subsingleton, so its krullDim is 0.
  have hsub : Subsingleton (PrimeSpectrum.zeroLocus (p : Set R)) := by
    rw [hpeq]
    have key (q : PrimeSpectrum R) (hq : maximalIdeal R ≤ q.asIdeal) :
        q.asIdeal = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le q.isPrime.ne_top hq).symm
    exact ⟨fun ⟨q, hq⟩ ⟨q', hq'⟩ =>
      Subtype.ext (PrimeSpectrum.ext ((key q hq).trans (key q' hq').symm))⟩
  -- V(m) is nonempty (it contains `m` itself).
  have hnonempty : Nonempty (PrimeSpectrum.zeroLocus (p : Set R)) := by
    refine ⟨⟨⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩, ?_⟩⟩
    rw [PrimeSpectrum.mem_zeroLocus, hpeq]
  have hkd : Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) = 0 :=
    Order.krullDim_eq_zero
  rw [hkd, hdepthe] at hle
  have h0 : e ≤ 0 := by exact_mod_cast hle
  omega

/-- If `supportDim N ≥ 1`, then `m` is not a minimal prime over `Ann N`. -/
theorem not_maximalIdeal_le_of_mem_minimalPrimes_annihilator
    {R : Type*} [CommRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] {e : ℕ}
    (he : Module.supportDim R N = (e : WithBot ℕ∞)) (hpos : 1 ≤ e) {p : Ideal R}
    (hp : p ∈ (Module.annihilator R N).minimalPrimes) : ¬ maximalIdeal R ≤ p := by
  intro hpm
  have hpprime : p.IsPrime := hp.isPrime
  have hpeq : p = maximalIdeal R :=
    ((maximalIdeal.isMaximal R).eq_of_le hpprime.ne_top' hpm).symm
  -- `e ≥ 1` gives an LTSeries of length 1 in `Supp N`: `q₀ < q₁`.
  have h1le : ((1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (Module.support R N) := by
    have hkd : Order.krullDim (Module.support R N) = (e : WithBot ℕ∞) := he
    rw [hkd]; exact_mod_cast hpos
  rw [Order.le_krullDim_iff] at h1le
  obtain ⟨l, hl⟩ := h1le
  -- `l.head < l.last`, and `l.head ∈ Supp N` so `ann N ≤ l.head`.
  have hlt : l.head < l.last := by
    have hsm := l.strictMono (a := 0) (b := Fin.last l.length)
      (by simp [Fin.lt_def]; omega)
    simpa [RelSeries.head, RelSeries.last] using hsm
  have hheadS : (l.head : PrimeSpectrum R) ∈ Module.support R N := l.head.property
  have hannhead : Module.annihilator R N ≤ (l.head : PrimeSpectrum R).asIdeal :=
    Module.annihilator_le_of_mem_support hheadS
  -- `l.head.asIdeal < m` since `l.head < l.last ≤ m`.
  have hheadlt : (l.head : PrimeSpectrum R).asIdeal < maximalIdeal R := by
    have hlastm : (l.last : PrimeSpectrum R).asIdeal ≤ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal_of_isPrime _ (hp := (l.last : PrimeSpectrum R).isPrime)
    have hheadlt2 : (l.head : PrimeSpectrum R).asIdeal < (l.last : PrimeSpectrum R).asIdeal :=
      hlt
    exact lt_of_lt_of_le hheadlt2 hlastm
  -- contradiction with minimality of `m` over `ann N`.
  have hheadprime : (l.head : PrimeSpectrum R).asIdeal.IsPrime :=
    (l.head : PrimeSpectrum R).isPrime
  have : p ≤ (l.head : PrimeSpectrum R).asIdeal :=
    hp.2 ⟨hheadprime, hannhead⟩ (le_of_lt (hpeq ▸ hheadlt))
  rw [hpeq] at this
  exact absurd (lt_of_le_of_lt this hheadlt) (lt_irrefl _)

end
