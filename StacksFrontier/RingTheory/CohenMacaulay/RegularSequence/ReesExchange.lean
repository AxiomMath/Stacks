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
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.Depth

/-!
# Regular elements, associated primes and the Rees exchange

Second part of the proof of `exists_isRegular_map_length_eq_ringKrullDim` (Stacks 06LC): a
regular element of the maximal ideal exists exactly when the depth is positive, exactly when the
maximal ideal is not an associated prime, and maximal regular sequences bound the depth (the Rees
exchange).

## Main results

* `exists_smulRegular_of_depth_pos`, `depth_pos_of_exists_smulRegular`,
  `exists_smulRegular_iff_maximalIdeal_notMem_associatedPrimes`: positive depth, regular elements
  of `m_R` and `m_R ∉ Ass`.
* `maximalRegular_descend_step`, `maximalRegular_dominates_length`: the Rees exchange.
* `depth_le_length_of_maximalIdeal_mem_associatedPrimes_quot`: maximal regular sequences bound the
  depth.
* `depth_pos_quot_of_length_lt_depth`: the quotient by a regular sequence shorter than the depth
  has positive depth.
-/

@[expose] public section

/- **Sub-maximal regular sequences extend (Stacks 00LK / Rees).**
If `rs` is an `R`-regular sequence in `m_R` whose length is *strictly below*
`depth R m_R R`, then there is an element `x ∈ m_R` that is a non-zero-divisor on the
iterated quotient `R ⧸ ofList rs • ⊤` — i.e. `rs` can be extended by one more regular
element of `m_R` (`exists_smulRegular_of_regular_lt_depth`).

This is Rees' theorem (Stacks 00LK) that *every maximal `M`-regular sequence in `m` has
length equal to `depth`*, in the equivalent contrapositive "non-maximal ⇒ extends" form.
Standard proofs use the `Ext` characterization `depth = inf{i | Ext^i(R/m, M) ≠ 0}` (or
Koszul homology) plus the depth-zero ⇔ associated-prime equivalence; the proof below avoids
`Ext`.  It is stated in terms of depth on the single ring `R`, with no Cohen–Macaulay
hypothesis.  Cite Stacks 00LK / 00LF / 00N6. -/

/-- **Positive depth yields a regular element of `m_R`.**
If a module `Q` over a Noetherian local ring `R` has
`0 < depth R m_R Q`, then there is `x ∈ m_R` that is a non-zero-divisor on `Q`.
Proof: `depth = sSup` of regular-sequence lengths; `> 0` means the index set contains
a positive-length regular sequence, whose head (extracted via `isRegular_cons_iff`) is
a regular element of `m_R`. -/
theorem exists_smulRegular_of_depth_pos {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hpos : 0 < Module.depthSup R (IsLocalRing.maximalIdeal R) Q) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular Q x := by
  rw [Module.depthSup] at hpos
  set m := IsLocalRing.maximalIdeal R with hm
  set S :=
    {n : ℕ∞ |
      ∃ rs : List R, ↑rs.length = n ∧ (∀ r ∈ rs, r ∈ m) ∧ RingTheory.Sequence.IsRegular Q rs} with
    hS
  have hex : ∃ k ∈ S, (1 : ℕ∞) ≤ k := by
    by_contra hc
    push Not at hc
    have hub : ∀ k ∈ S, k ≤ 0 := by
      intro k hk
      have hlt := hc k hk
      rcases eq_or_ne k 0 with h0 | h0
      · simp [h0]
      · exact
          absurd hlt
            (by
              have : (1 : ℕ∞) ≤ k := Order.one_le_iff_ne_zero.mpr h0
              simp [not_lt.mpr this])
    have : sSup S ≤ 0 := sSup_le hub
    exact absurd (lt_of_lt_of_le hpos this) (by simp)
  obtain ⟨k, hkS, hk1⟩ := hex
  obtain ⟨rs, hlen, hmem, hreg⟩ := hkS
  have hne : rs ≠ [] := by
    rintro rfl; simp only [List.length_nil] at hlen; rw [← hlen] at hk1
    exact absurd hk1 (by norm_num)
  obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨r, hmem r (List.mem_cons_self), ?_⟩
  rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
  exact hreg.left

/- **Positive depth of short regular-sequence quotients, by Rees exchange.**
`depth_pos_quot_of_length_lt_depth` is assembled from the three lemmas
`exists_smulRegular_iff_maximalIdeal_notMem_associatedPrimes`,
`depth_pos_of_exists_smulRegular` and
`depth_le_length_of_maximalIdeal_mem_associatedPrimes_quot` below.  The route is the classical
*Rees exchange* proof of "all maximal regular sequences in `m` have the same length = depth",
which is elementary (no Ext/Koszul).  The substantial engine — *permutability of regular
sequences in `m`* — is `IsLocalRing.isRegular_of_perm` (Stacks 00LJ). -/

/-- An element is regular on `Q` iff it lies in no associated prime of `Q`. -/
private theorem isSMulRegular_iff_forall_notMem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {Q : Type*} [AddCommGroup Q] [Module R Q] {c : R} :
    IsSMulRegular Q c ↔ ∀ p ∈ associatedPrimes R Q, c ∉ p := by
  have := Set.ext_iff.mp (biUnion_associatedPrimes_eq_compl_regular R Q) c
  rw [← not_iff_not]
  simpa [and_comm] using this.symm

/-- **Existence of a regular element ⟺ `m ∉ Ass Q`.**
For a finite nontrivial module `Q` over the Noetherian local ring `R`, there is a
`Q`-regular element of `m_R` iff `m_R` is not an associated prime of `Q`.
Proof: zero-divisors on `Q` = `⋃ p ∈ Ass Q, p` (`biUnion_associatedPrimes_eq_compl_regular`);
prime avoidance (`Ideal.subset_union_prime`) over the finite `Ass Q` plus locality
(`p ≤ m`, so `m ⊆ p ⟺ m = p`) collapse `m ⊆ ⋃ Ass Q ⟺ m ∈ Ass Q`.  Mirrors STEP 5 of
`exists_mem_maximalIdeal_isSMulRegular_map`. -/
@[ega "0 17.3.1.2" "special case", sga "2 III 2.1" "(iv) ⇔ (v)"]
theorem exists_smulRegular_iff_maximalIdeal_notMem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {Q : Type*} [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Nontrivial Q] :
    (∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular Q x) ↔
      IsLocalRing.maximalIdeal R ∉ associatedPrimes R Q := by
  classical
  have hiff := fun {c : R} => isSMulRegular_iff_forall_notMem_associatedPrimes (Q := Q) (c := c)
  refine ⟨fun ⟨x, hxm, hxreg⟩ hmAss => hiff.mp hxreg _ hmAss hxm, fun hm => ?_⟩
  -- prime avoidance: some element of `m_R` lies in no associated prime of `Q`
  have hns : ¬((IsLocalRing.maximalIdeal R : Set R) ⊆ ⋃ p ∈ associatedPrimes R Q, (p : Set R)) :=
    (Ideal.subset_union_prime_finite (associatedPrimes.finite R Q) (f := fun p => p) ⊥ ⊥
      fun p hp _ _ => hp.isPrime).not.mpr fun ⟨p, hp, hle⟩ =>
        hm (le_antisymm hle (IsLocalRing.le_maximalIdeal hp.isPrime.ne_top) ▸ hp)
  obtain ⟨c, hcm, hc⟩ := Set.not_subset.mp hns
  exact ⟨c, hcm, hiff.mpr fun p hp hcp => hc (Set.mem_biUnion hp hcp)⟩

/-- **A regular element of `m_R` gives positive depth.**
If `Q` is finite nontrivial over the Noetherian local `R` and some `x ∈ m_R` is
`Q`-regular, then `0 < depth R m_R Q`.  Proof: `x ∈ m_R` ⇒ (Nakayama) `Q/xQ` nontrivial
⇒ `IsRegular Q [x]` (`isRegular_cons_iff` + `IsRegular.nil`); so `1` lies in the depth
index set, hence `depth ≥ 1 > 0`. -/
theorem depth_pos_of_exists_smulRegular {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Nontrivial Q]
    (h : ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular Q x) :
    0 < Module.depthSup R (IsLocalRing.maximalIdeal R) Q := by
  -- `[x]` is a length-1 regular sequence in m_R; `le_sSup` lands `1 ≤ depth`.  This needs
  -- `Nontrivial (QuotSMulTop x Q)` from `x ∈ m_R` (`nontrivial_quotSMulTop_of_mem_maximalIdeal`).
  obtain ⟨x, hxm, hxreg⟩ := h
  rw [Module.depthSup]
  have hntq : Nontrivial (QuotSMulTop x Q) := nontrivial_quotSMulTop_of_mem_maximalIdeal Q hxm
  have hreg : RingTheory.Sequence.IsRegular Q [x] := by
    rw [RingTheory.Sequence.isRegular_cons_iff]
    exact ⟨hxreg, RingTheory.Sequence.IsRegular.nil R (QuotSMulTop x Q)⟩
  have hmem :
    (1 : ℕ∞) ∈
      {n : ℕ∞ |
        ∃ rs : List R,
          ↑rs.length = n ∧
            (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧ RingTheory.Sequence.IsRegular Q rs} := by
    refine ⟨[x], by simp, ?_, hreg⟩
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact hxm
  calc
    (0 : ℕ∞) < 1 := by norm_num
    _ ≤ _ := le_sSup hmem

/- **Maximal regular sequences bound the depth (Rees exchange).**
`depth_le_length_of_maximalIdeal_mem_associatedPrimes_quot` is a corollary (via `sSup_le`)
of the generalized domination statement
`maximalRegular_dominates_length` (arbitrary finite nonzero module `M`).  The
base case of its induction is
`no_smulRegular_of_maximalIdeal_mem_associatedPrimes`; the induction itself is the
substantial Rees-exchange argument. -/

/-- **`m ∈ Ass M` ⇒ no regular element of `m`.**
If `m_R ∈ Ass_R(M)` (M finite) then every `M`-regular sequence with entries in `m_R`
is empty.  Proof: `biUnion_associatedPrimes_eq_compl_regular` says the zero-divisors of
`M` are `⋃ Ass M`; `m_R ∈ Ass M` puts every `a ∈ m_R` in a zero-divisor, contradicting
the head of a nonempty regular sequence (`isRegular_cons_iff`). -/
@[ega "0 16.4.2" "special case"]
theorem no_smulRegular_of_maximalIdeal_mem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hM : IsLocalRing.maximalIdeal R ∈ associatedPrimes R M) {ts : List R}
    (htsm : ∀ x ∈ ts, x ∈ IsLocalRing.maximalIdeal R) (htsR : RingTheory.Sequence.IsRegular M ts) :
    ts = [] := by
  rcases ts with _ | ⟨a, ts'⟩
  · rfl
  · exfalso
    rw [RingTheory.Sequence.isRegular_cons_iff] at htsR
    obtain ⟨ha, _⟩ := htsR
    have ham := htsm a (List.mem_cons_self)
    exact isSMulRegular_iff_forall_notMem_associatedPrimes.mp ha _ hM ham

open scoped Pointwise in
/-- **Maximality is independent of the chosen regular element.**
For a finite nonzero `R`-module `M` (R Noetherian local) and `a, b ∈ m_R` both `M`-regular,
if `m_R ∈ Ass_R(M/aM)` then `m_R ∈ Ass_R(M/bM)`.  Equivalent to
"depth(M/aM) = depth(M) − 1 independent of the regular element `a`" (Bruns–Herzog 1.2.10(d)). -/
theorem eLocal_swap {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] {a b : R}
    (hbm : b ∈ IsLocalRing.maximalIdeal R) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (h : IsLocalRing.maximalIdeal R ∈ associatedPrimes R (QuotSMulTop a M)) :
    IsLocalRing.maximalIdeal R ∈ associatedPrimes R (QuotSMulTop b M) := by
  -- Stacks 00LK / B-H 1.2.10(d).
  -- Direct Rees exchange: from `m ∈ Ass(M/aM)` pick `x` with `m = Ann(x̄)`;
  -- since `b ∈ m`, `b • x = a • y` for some `y`; then `m = Ann(ȳ)` in `M/bM`.
  set m := IsLocalRing.maximalIdeal R with hm
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at h
  obtain ⟨hprime, xb, hcol⟩ := h
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
  have hmem_iff : ∀ r : R, r ∈ m ↔ r • x ∈ a • (⊤ : Submodule R M) := by
    intro r
    rw [hcol, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  have hbx : b • x ∈ a • (⊤ : Submodule R M) := (hmem_iff b).mp hbm
  rw [Submodule.mem_smul_pointwise_iff_exists] at hbx
  obtain ⟨y, -, hy⟩ := hbx
  -- hy : a • y = b • x
  have hle : ∀ s ∈ m, s • (Submodule.Quotient.mk y : QuotSMulTop b M) = 0 := by
    intro s hs
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    have hsx : s • x ∈ a • (⊤ : Submodule R M) := (hmem_iff s).mp hs
    rw [Submodule.mem_smul_pointwise_iff_exists] at hsx
    obtain ⟨z, -, hz⟩ := hsx
    refine ⟨z, Submodule.mem_top, ?_⟩
    apply ha
    have : a • (b • z) = a • (s • y) := by
      rw [smul_comm a b z, hz, smul_comm a s y, hy, smul_comm s b x]
    exact this
  have hyne : (Submodule.Quotient.mk y : QuotSMulTop b M) ≠ 0 := by
    intro hc
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hc
    obtain ⟨w, -, hw⟩ := hc
    have hxin : x ∈ a • (⊤ : Submodule R M) := by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨w, Submodule.mem_top, ?_⟩
      apply hb
      have : b • (a • w) = b • x := by rw [smul_comm b a w, hw, hy]
      exact this
    have hx0 : (1 : R) ∈ m := by
      rw [hmem_iff]; simpa using hxin
    exact hprime.ne_top (by rwa [Ideal.eq_top_iff_one])
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  refine ⟨hprime, Submodule.Quotient.mk y, ?_⟩
  have hmle : m ≤ (⊥ : Submodule R (QuotSMulTop b M)).colon {Submodule.Quotient.mk y} := by
    intro s hs
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact hle s hs
  have hcolne : (⊥ : Submodule R (QuotSMulTop b M)).colon {Submodule.Quotient.mk y} ≠ ⊤ := by
    intro hc
    have h1 : (1 : R) ∈ (⊥ : Submodule R (QuotSMulTop b M)).colon {Submodule.Quotient.mk y} := by
      rw [hc]; trivial
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul] at h1
    exact hyne h1
  exact (le_antisymm (IsLocalRing.le_maximalIdeal hcolne) hmle).symm

open scoped Pointwise in
/-- Module-level snoc characterization of regular sequences. -/
theorem isRegular_snoc_iff_mod {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (rs : List R) (a : R) :
    RingTheory.Sequence.IsRegular M (rs ++ [a]) ↔
      RingTheory.Sequence.IsRegular M rs ∧
        RingTheory.Sequence.IsRegular (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) [a] := by
  have bridge :
    ∀ (I J : Ideal R),
      (⊤ : Submodule R (M ⧸ J • (⊤ : Submodule R M))) = I • ⊤ ↔
        I • (⊤ : Submodule R M) ⊔ J • ⊤ = ⊤ := by
    intro I J
    rw [show I • (⊤ : Submodule R (M ⧸ J • (⊤ : Submodule R M))) =
        Submodule.map (J • ⊤ : Submodule R M).mkQ (I • ⊤) by
          rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ],
      eq_comm, Submodule.map_mkQ_eq_top, sup_comm]
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isRegular_iff,
    RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isWeaklyRegular_append_iff]
  rw [Ideal.ofList_append, Submodule.sup_smul]
  have hb := bridge (Ideal.ofList [a]) (Ideal.ofList rs)
  constructor
  · rintro ⟨⟨hwr, hwq⟩, hne⟩
    refine ⟨⟨hwr, ?_⟩, hwq, ?_⟩
    · intro he
      exact hne (by rw [← he]; simp)
    · intro he
      rw [hb] at he
      rw [sup_comm] at hne
      exact hne he.symm
  · rintro ⟨⟨hwr, hne1⟩, hwq, hne2⟩
    refine ⟨⟨hwr, hwq⟩, fun he => hne2 ?_⟩
    rw [hb, sup_comm]
    exact he.symm

open scoped Pointwise in
/-- The `j`-th element of an `M`-regular sequence is regular on `M/(l.take j)·⊤`. -/
theorem isSMulRegular_take_get {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (l : List R) (hlR : RingTheory.Sequence.IsRegular M l) (j : ℕ) (hj : j < l.length) :
    IsSMulRegular (M ⧸ Ideal.ofList (l.take j) • (⊤ : Submodule R M)) l[j] := by
  have hcat : (l.take j) ++ [l[j]] = l.take (j + 1) := by
    rw [← List.concat_eq_append]; exact List.take_concat_get hj
  have hsnoc : RingTheory.Sequence.IsRegular M ((l.take j) ++ [l[j]]) := by
    rw [hcat]; exact isRegular_take l hlR (j + 1)
  rw [isRegular_snoc_iff_mod] at hsnoc
  rw [RingTheory.Sequence.isRegular_cons_iff] at hsnoc
  exact hsnoc.right.left

open scoped Pointwise in
/-- Build a singleton regular sequence from a regular element of `m_R`. -/
theorem isRegular_singleton_of_mem_maximalIdeal {R : Type*} [CommRing R] {Q : Type*}
    [AddCommGroup Q] [Module R Q] [IsLocalRing R] [Module.Finite R Q] [Nontrivial Q] {c : R}
    (hcm : c ∈ IsLocalRing.maximalIdeal R) (hc : IsSMulRegular Q c) :
    RingTheory.Sequence.IsRegular Q [c] := by
  rw [RingTheory.Sequence.isRegular_cons_iff]
  refine ⟨hc, ?_⟩
  have : Nontrivial (QuotSMulTop c Q) := nontrivial_quotSMulTop_of_mem_maximalIdeal Q hcm
  exact RingTheory.Sequence.IsRegular.nil R _

/-- The quotient of `M` by a regular sequence is nontrivial. -/
private theorem nontrivial_quot_ofList_of_isRegular {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {l : List R} (hlR : RingTheory.Sequence.IsRegular M l) :
    Nontrivial (M ⧸ Ideal.ofList l • (⊤ : Submodule R M)) := by
  rw [RingTheory.Sequence.isRegular_iff] at hlR
  rw [Submodule.Quotient.nontrivial_iff]
  exact fun h => hlR.2 h.symm

/-- The empty list of elements generates the zero submodule `ofList [] • ⊤ = ⊥`. -/
private theorem ofList_nil_smul_top {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] : Ideal.ofList ([] : List R) • (⊤ : Submodule R M) = ⊥ := by
  simp

open scoped Pointwise in
/-- Descent: if `l` is `M`-regular and `c ∈ m_R` is regular on `M/(l)·⊤`, then `l` is
regular over `QuotSMulTop c M`. -/
@[ega "IV 19.5.3" "c) ⇒ a), special case"]
theorem isRegular_quotSMulTop_of_isSMulRegular_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (l : List R)
    (hlR : RingTheory.Sequence.IsRegular M l) {c : R} (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (hc : IsSMulRegular (M ⧸ Ideal.ofList l • (⊤ : Submodule R M)) c) :
    RingTheory.Sequence.IsRegular (QuotSMulTop c M) l := by
  have := nontrivial_quot_ofList_of_isRegular hlR
  have hsnoc : RingTheory.Sequence.IsRegular M (l ++ [c]) := by
    rw [isRegular_snoc_iff_mod]
    exact ⟨hlR, isRegular_singleton_of_mem_maximalIdeal hcm hc⟩
  have hperm : RingTheory.Sequence.IsRegular M (c :: l) :=
    IsLocalRing.isRegular_of_perm hsnoc (by simp)
  rw [RingTheory.Sequence.isRegular_cons_iff] at hperm
  exact hperm.right

/-- Transfer `IsSMulRegular` along a linear equivalence. -/
theorem isSMulRegular_of_linearEquiv {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {c : R} (e : M ≃ₗ[R] N) (h : IsSMulRegular M c) :
    IsSMulRegular N c :=
  IsSMulRegular.of_injective e.symm e.symm.injective h

/-- `c` regular ⟺ `c` avoids every associated prime (`⟸` direction). -/
@[ega "IV 3.1.9" "affine sufficiency"]
theorem isSMulRegular_of_avoiding {R : Type*} [CommRing R] [IsNoetherianRing R] {Q : Type*}
    [AddCommGroup Q] [Module R Q] {c : R} (h : ∀ p ∈ associatedPrimes R Q, c ∉ p) :
    IsSMulRegular Q c :=
  isSMulRegular_iff_forall_notMem_associatedPrimes.mpr h

/-- `c` regular ⟹ `c` avoids every associated prime. -/
@[ega "IV 3.1.9" "affine necessity", sga "3 V 7.2" "partial"]
theorem avoiding_of_isSMulRegular {R : Type*} [CommRing R] [IsNoetherianRing R] {Q : Type*}
    [AddCommGroup Q] [Module R Q] {c : R} (h : IsSMulRegular Q c) :
    ∀ p ∈ associatedPrimes R Q, c ∉ p :=
  isSMulRegular_iff_forall_notMem_associatedPrimes.mp h

/-- Prime avoidance over a finite set of primes inside a local ring: if `m_R ⊄ p` for each
`p` in the finite family `S`, there is `c ∈ m_R` avoiding every member of `S`. -/
@[sga "3 V 4.1" "local ring, special case"]
theorem exists_mem_maximalIdeal_avoiding {R : Type*} [CommRing R] [IsLocalRing R]
    (S : Finset (Ideal R)) (hp : ∀ i ∈ S, (i : Ideal R).IsPrime)
    (hnle : ∀ i ∈ S, ¬(IsLocalRing.maximalIdeal R ≤ i)) :
    ∃ c ∈ IsLocalRing.maximalIdeal R, ∀ i ∈ S, c ∉ i := by
  rcases S.eq_empty_or_nonempty with hSe | hSe
  · subst hSe
    exact ⟨0, Submodule.zero_mem _, by simp⟩
  · obtain ⟨a, ha⟩ := hSe
    have hiff :=
      Ideal.subset_union_prime (s := S) (f := fun i => i) a a (fun i hi _ _ => hp i hi) (I :=
        IsLocalRing.maximalIdeal R)
    have hnotex : ¬(∃ i ∈ S, IsLocalRing.maximalIdeal R ≤ i) := by
      push Not; exact hnle
    have hnotsub := (hiff.not.mpr hnotex)
    rw [Set.not_subset] at hnotsub
    obtain ⟨c, hcm, hcni⟩ := hnotsub
    refine ⟨c, hcm, ?_⟩
    intro i hi hci
    apply hcni
    simp only [Set.mem_iUnion]
    exact ⟨i, by simpa using hi, hci⟩

open scoped Pointwise in
/-- The double-quotient by ideal-smul-top iso: `(M/(J·⊤))/(I·⊤) ≅ M/((I⊔J)·⊤)`. -/
noncomputable def quotQuotSMulTopEquivQuotSup {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (I J : Ideal R) :
    ((M ⧸ J • (⊤ : Submodule R M)) ⧸ I • (⊤ : Submodule R (M ⧸ J • (⊤ : Submodule R M)))) ≃ₗ[R]
      (M ⧸ (I ⊔ J) • (⊤ : Submodule R M)) := by
  have hsle : (J • (⊤ : Submodule R M)) ≤ (I ⊔ J) • ⊤ := Submodule.smul_mono le_sup_right le_rfl
  have key := Submodule.quotientQuotientEquivQuotient (J • (⊤ : Submodule R M)) ((I ⊔ J) • ⊤) hsle
  have hmapeq :
    Submodule.map (J • (⊤ : Submodule R M)).mkQ ((I ⊔ J) • ⊤) =
      I • (⊤ : Submodule R (M ⧸ J • (⊤ : Submodule R M))) := by
    rw [Submodule.sup_smul, Submodule.map_sup]
    rw [Submodule.mkQ_map_self, sup_bot_eq]
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [hmapeq] at key
  exact key

/-- Associated primes of `(M/(ys)·⊤)/w·⊤` are those of `M/(w :: ys)·⊤`. -/
private theorem mem_associatedPrimes_quotSMulTop_quot_iff {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (p : Ideal R) (w : R) (ys : List R) :
    p ∈ associatedPrimes R (QuotSMulTop w (M ⧸ Ideal.ofList ys • (⊤ : Submodule R M))) ↔
      p ∈ associatedPrimes R (M ⧸ Ideal.ofList (w :: ys) • (⊤ : Submodule R M)) := by
  have e1 : QuotSMulTop w (M ⧸ Ideal.ofList ys • (⊤ : Submodule R M)) ≃ₗ[R]
      _ ⧸ (Ideal.span {w}) • (⊤ : Submodule R (M ⧸ Ideal.ofList ys • (⊤ : Submodule R M))) :=
    Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul _ _).symm
  have e3 : (M ⧸ (Ideal.span {w} ⊔ Ideal.ofList ys) • (⊤ : Submodule R M)) ≃ₗ[R]
      (M ⧸ Ideal.ofList (w :: ys) • (⊤ : Submodule R M)) :=
    Submodule.quotEquivOfEq _ _ (by rw [Ideal.ofList_cons])
  rw [LinearEquiv.AssociatedPrimes.eq
    (e1.trans ((quotQuotSMulTopEquivQuotSup (Ideal.span {w}) (Ideal.ofList ys)).trans e3))]

/-- For a regular sequence `l` in `m_R`, there is a finite family `S` of primes not containing
`m_R` such that every element avoiding `S` is regular on all proper-prefix quotients of `l`. -/
private theorem exists_finset_isSMulRegular_take {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {l : List R}
    (hlR : RingTheory.Sequence.IsRegular M l) (hlm : ∀ x ∈ l, x ∈ IsLocalRing.maximalIdeal R) :
    ∃ S : Finset (Ideal R), (∀ i ∈ S, i.IsPrime ∧ ¬IsLocalRing.maximalIdeal R ≤ i) ∧
      ∀ c : R, (∀ i ∈ S, c ∉ i) → ∀ j < l.length,
        IsSMulRegular (M ⧸ Ideal.ofList (l.take j) • (⊤ : Submodule R M)) c := by
  classical
  refine ⟨(Finset.range l.length).biUnion fun j =>
    (associatedPrimes.finite R (M ⧸ Ideal.ofList (l.take j) • (⊤ : Submodule R M))).toFinset,
    fun i hi => ?_, fun c hc j hj => ?_⟩
  · obtain ⟨j, hj, hij⟩ := by simpa using hi
    refine ⟨hij.isPrime, fun hle => ?_⟩
    exact avoiding_of_isSMulRegular (isSMulRegular_take_get l hlR j hj) i hij
      (hle (hlm _ (List.getElem_mem _)))
  · exact isSMulRegular_of_avoiding fun p hp => hc p (by simpa using ⟨j, hj, hp⟩)

/-- **One level of the Rees-exchange induction.**
Given a finite nonzero `M`, a maximal `M`-regular sequence `xs ≠ []` in `m_R`
(`m_R ∈ Ass(M/(xs)·⊤)`), and a nonempty `M`-regular `ts` in `m_R`, there is a single
shared regular element `c ∈ m_R` (chosen by prime avoidance, regular on `M` and on all
proper-prefix quotients of `xs` and `ts`) such that, over `N := M/cM`:
- `xs.dropLast` is `N`-regular and still maximal (`m_R ∈ Ass(N/(xs.dropLast)·⊤)`),
  the maximality transferred from `xs.getLast` to `c` by `eLocal_swap` at the module
  `M/(xs.dropLast)·⊤`; and
- `ts.dropLast` is `N`-regular.
Both descents use `IsLocalRing.isRegular_of_perm` (perm `l ++ [c] ~ c :: l`) +
`isRegular_cons_iff`, and the cumulative-quotient iso
`Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner` + `LinearEquiv.AssociatedPrimes.eq`.
This is the prime-avoidance + permutability + `eLocal_swap` heart of the induction
(Stacks 00LK). -/
theorem maximalRegular_descend_step {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (xs : List R)
    (hxsm : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) (hxsR : RingTheory.Sequence.IsRegular M xs)
    (hxsmax :
      IsLocalRing.maximalIdeal R ∈ associatedPrimes R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)))
    (hxsne : xs ≠ []) (ts : List R) (htsm : ∀ x ∈ ts, x ∈ IsLocalRing.maximalIdeal R)
    (htsR : RingTheory.Sequence.IsRegular M ts) (htsne : ts ≠ []) :
    ∃ c ∈ IsLocalRing.maximalIdeal R,
      IsSMulRegular M c ∧
        (∀ x ∈ xs.dropLast, x ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular (QuotSMulTop c M) xs.dropLast ∧
        IsLocalRing.maximalIdeal R ∈
          associatedPrimes R
            ((QuotSMulTop c M) ⧸ Ideal.ofList xs.dropLast • (⊤ : Submodule R (QuotSMulTop c M))) ∧
        (∀ x ∈ ts.dropLast, x ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular (QuotSMulTop c M) ts.dropLast := by
  -- Prime avoidance, two permutability descents, and the maximality transfer by `eLocal_swap`.
  classical
  set m := IsLocalRing.maximalIdeal R with hm
  set n := xs.length with hndef
  set k := ts.length with hkdef
  have hnpos : 0 < n := List.length_pos_of_ne_nil hxsne
  have hkpos : 0 < k := List.length_pos_of_ne_nil htsne
  -- The avoided finite family of primes.
  obtain ⟨Sx, hSx, hcx⟩ := exists_finset_isSMulRegular_take hxsR hxsm
  obtain ⟨St, hSt, hct⟩ := exists_finset_isSMulRegular_take htsR htsm
  obtain ⟨c, hcm, hcavoid⟩ := exists_mem_maximalIdeal_avoiding (Sx ∪ St)
    (fun i hi => (Finset.mem_union.mp hi).elim (fun h => (hSx i h).1) fun h => (hSt i h).1)
    (fun i hi => (Finset.mem_union.mp hi).elim (fun h => (hSx i h).2) fun h => (hSt i h).2)
  -- c regular on each prefix quotient
  have creg_xs := hcx c fun i hi => hcavoid i (Finset.mem_union_left _ hi)
  have creg_ts := hct c fun i hi => hcavoid i (Finset.mem_union_right _ hi)
  -- IsSMulRegular M c (via j = 0)
  have hcM : IsSMulRegular M c := by
    have h0 := creg_xs 0 hnpos
    rw [List.take_zero] at h0
    exact isSMulRegular_of_linearEquiv (Submodule.quotEquivOfEqBot _ ofList_nil_smul_top) h0
  -- the two dropLast = take (len - 1)
  have hxdl : xs.dropLast = xs.take (n - 1) := by rw [List.dropLast_eq_take, hndef]
  have htdl : ts.dropLast = ts.take (k - 1) := by rw [List.dropLast_eq_take, hkdef]
  -- c regular on M/(xs.dropLast)·⊤  and  M/(ts.dropLast)·⊤
  have hcreg_ys : IsSMulRegular (M ⧸ Ideal.ofList xs.dropLast • (⊤ : Submodule R M)) c := by
    rw [hxdl]; exact creg_xs (n - 1) (by omega)
  have hcreg_tsdl : IsSMulRegular (M ⧸ Ideal.ofList ts.dropLast • (⊤ : Submodule R M)) c := by
    rw [htdl]; exact creg_ts (k - 1) (by omega)
  -- regularity of dropLast prefixes
  have hysR : RingTheory.Sequence.IsRegular M xs.dropLast := by
    rw [hxdl]; exact isRegular_take xs hxsR (n - 1)
  have htsdlR : RingTheory.Sequence.IsRegular M ts.dropLast := by
    rw [htdl]; exact isRegular_take ts htsR (k - 1)
  -- membership of dropLast entries
  have hysm : ∀ x ∈ xs.dropLast, x ∈ m := fun x hx => hxsm x (List.dropLast_subset _ hx)
  have htsdlm : ∀ x ∈ ts.dropLast, x ∈ m := fun x hx => htsm x (List.dropLast_subset _ hx)
  -- N-regularity descents
  have hysN : RingTheory.Sequence.IsRegular (QuotSMulTop c M) xs.dropLast :=
    isRegular_quotSMulTop_of_isSMulRegular_quot xs.dropLast hysR hcm hcreg_ys
  have htsN : RingTheory.Sequence.IsRegular (QuotSMulTop c M) ts.dropLast :=
    isRegular_quotSMulTop_of_isSMulRegular_quot ts.dropLast htsdlR hcm hcreg_tsdl
  -- maximality transfer (`eLocal_swap` at B = M/(xs.dropLast)·⊤)
  have hmaxN :
    m ∈
      associatedPrimes R
        ((QuotSMulTop c M) ⧸ Ideal.ofList xs.dropLast • (⊤ : Submodule R (QuotSMulTop c M))) := by
    set ys := xs.dropLast with hys
    set w := xs.getLast hxsne with hw
    set B := M ⧸ Ideal.ofList ys • (⊤ : Submodule R M) with hBdef
    have hwget : w = xs[n - 1]'(by omega) := by rw [hw, List.getLast_eq_getElem]
    have hwB0 := isSMulRegular_take_get xs hxsR (n - 1) (by omega)
    rw [← hxdl] at hwB0
    have hwB : IsSMulRegular B w := by
      rw [hwget]; exact hwB0
    have hcB : IsSMulRegular B c := hcreg_ys
    have hwm : w ∈ m :=
      hxsm _
        (by
          rw [hw]; exact List.getLast_mem hxsne)
    have hBnt : Nontrivial B := nontrivial_quot_ofList_of_isRegular hysR
    have : Module.Finite R B := inferInstanceAs (Module.Finite R (M ⧸ _))
    have hxdecomp : xs = ys ++ [w] := (List.dropLast_append_getLast hxsne).symm
    -- m ∈ Ass(QuotSMulTop w B)
    have hAssW : m ∈ associatedPrimes R (QuotSMulTop w B) := by
      rw [mem_associatedPrimes_quotSMulTop_quot_iff]
      have hofl : Ideal.ofList (w :: ys) = Ideal.ofList xs := by
        rw [hxdecomp, Ideal.ofList_append, Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil,
          sup_bot_eq, sup_comm]
      rwa [hofl]
    -- swap maximality to c via eLocal_swap
    have hAssC : m ∈ associatedPrimes R (QuotSMulTop c B) := eLocal_swap hcm hwB hcB hAssW
    rwa [mem_associatedPrimes_quotSMulTop_quot_iff,
      LinearEquiv.AssociatedPrimes.eq (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M c ys)]
      at hAssC
  exact ⟨c, hcm, hcM, hysm, hysN, hmaxN, htsdlm, htsN⟩

/-- **Generalized Rees domination: a maximal regular sequence dominates.**
For any finite nonzero `R`-module `M` (R Noetherian local), if `xs` is an `M`-regular
sequence in `m_R` that is maximal (`m_R ∈ Ass_R(M ⧸ ofList xs • ⊤)`), then every
`M`-regular sequence `ts` in `m_R` satisfies `ts.length ≤ xs.length`.

This is the elementary Rees-exchange content (Stacks 00LK / Bruns–Herzog 1.2.5,
the ≥-half of "all maximal regular sequences in `m` have common length = depth").  Its
proof is a strong induction on `xs.length` (generalizing `M`, `ts`):
- base `xs = []`: `m_R ∈ Ass M` (via `M/0 ≅ M`), so
  `no_smulRegular_of_maximalIdeal_mem_associatedPrimes` forces `ts = []`;
- step: `maximalRegular_descend_step` produces a shared `c`, descends both `xs.dropLast`
  (still maximal over `N = M/cM`) and `ts.dropLast` (regular over `N`) by one level, and
  the inductive hypothesis on `N` (length `xs.length − 1 < xs.length`) gives
  `ts.length − 1 ≤ xs.length − 1`, hence `ts.length ≤ xs.length`. -/
@[ega "0 16.4.2" "sufficiency", ega "0 16.4.4" "more general", sga "2 III 2.6" "Local case"]
theorem maximalRegular_dominates_length {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (xs : List R) (hxsm : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R)
    (hxsR : RingTheory.Sequence.IsRegular M xs)
    (hxsmax :
      IsLocalRing.maximalIdeal R ∈ associatedPrimes R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)))
    (ts : List R) (htsm : ∀ x ∈ ts, x ∈ IsLocalRing.maximalIdeal R)
    (htsR : RingTheory.Sequence.IsRegular M ts) : ts.length ≤ xs.length := by
  -- Strong induction on xs.length (generalizing M, ts); base =
  -- `no_smulRegular_of_maximalIdeal_mem_associatedPrimes`,
  -- step = `maximalRegular_descend_step` + IH on N = M/cM.
  set n := xs.length with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing M xs ts with
  | _ n IH =>
    rcases eq_or_ne xs [] with hxe | hxne
    · subst hxe
      have hMass : IsLocalRing.maximalIdeal R ∈ associatedPrimes R M := by
        rwa [LinearEquiv.AssociatedPrimes.eq (Submodule.quotEquivOfEqBot _ ofList_nil_smul_top)]
          at hxsmax
      have hts0 := no_smulRegular_of_maximalIdeal_mem_associatedPrimes hMass htsm htsR
      subst hts0
      exact Nat.zero_le _
    · rcases eq_or_ne ts [] with hte | htne
      · subst hte; exact Nat.zero_le _
      · obtain ⟨c, hcm, hcreg, hysm, hysR, hysmax, htsm', htsR'⟩ :=
          maximalRegular_descend_step xs hxsm hxsR hxsmax hxne ts htsm htsR htne
        have : Nontrivial (QuotSMulTop c M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hcm
        have hlen : xs.dropLast.length < n := by
          rw [List.length_dropLast, hn]
          have : 0 < xs.length := List.length_pos_of_ne_nil hxne
          omega
        have key :=
          IH xs.dropLast.length hlen xs.dropLast hysm hysR hysmax ts.dropLast htsm' htsR' rfl
        rw [List.length_dropLast, List.length_dropLast] at key
        have htspos : 0 < ts.length := List.length_pos_of_ne_nil htne
        have hxspos : 0 < xs.length := List.length_pos_of_ne_nil hxne
        omega

/-- **Maximal regular sequences bound the depth.**
If `rs` is an `R`-regular sequence in `m_R` and `m_R ∈ Ass(R ⧸ ofList rs • ⊤)` (i.e. `rs`
is a maximal regular sequence — it cannot be extended, by
`exists_smulRegular_iff_maximalIdeal_notMem_associatedPrimes`), then
`depth R m_R R ≤ rs.length`.  Corollary of the generalized domination statement
`maximalRegular_dominates_length` (with `M = R`) via `sSup_le`. -/
@[ega "0 16.4.2" "sufficiency for M = A", ega "0 16.4.4" "M = A", sga "2 III 2.6" "special case"]
theorem depth_le_length_of_maximalIdeal_mem_associatedPrimes_quot {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (rs : List R)
    (hrsm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) (hrsR : RingTheory.Sequence.IsRegular R rs)
    (hass :
      IsLocalRing.maximalIdeal R ∈
        associatedPrimes R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R))) :
    Module.depthSup R (IsLocalRing.maximalIdeal R) R ≤ (rs.length : ℕ∞) := by
  -- Assembly: bound every depth-index length by rs.length via the
  -- generalized domination statement `maximalRegular_dominates_length` (M = R).
  rw [Module.depthSup]
  apply sSup_le
  rintro n ⟨ts, rfl, htsm, htsR⟩
  have hdom : ts.length ≤ rs.length :=
    maximalRegular_dominates_length rs hrsm hrsR hass ts htsm htsR
  exact_mod_cast hdom

/-- **Depth-additivity positivity along a regular sequence.**
For an `R`-regular sequence `rs ⊆ m_R` whose length is strictly below `depth R m_R R`,
the iterated quotient `R ⧸ ofList rs • ⊤` has positive depth.

This is the positivity consequence of Rees depth-additivity (Stacks 00LK).  Its proof is
an assembly of the three lemmas above (the hard engine is `IsLocalRing.isRegular_of_perm`).
Cite Stacks 00LK / 00LF / 00N6. -/
theorem depth_pos_quot_of_length_lt_depth {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (rs : List R) (hrsm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R)
    (hrsR : RingTheory.Sequence.IsRegular R rs)
    (hlt : (rs.length : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) R) :
    0 <
      Module.depthSup R (IsLocalRing.maximalIdeal R)
        (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) := by
  -- Q := R/(rs) is finite (quotient of R) and nontrivial (ofList rs ⊆ m_R ≠ ⊤).
  set m := IsLocalRing.maximalIdeal R with hm
  set Q := R ⧸ Ideal.ofList rs • (⊤ : Submodule R R) with hQ
  -- `ofList rs ≤ m`, so the quotient is nontrivial.
  have hle : Ideal.ofList rs ≤ m := by
    rw [Ideal.ofList, Ideal.span_le]; intro x hx; exact hrsm x hx
  have hne : Ideal.ofList rs • (⊤ : Submodule R R) ≠ ⊤ := by
    rw [smul_eq_mul, Ideal.mul_top]
    intro h; rw [h] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)
  have : Nontrivial Q := by
    rw [hQ]
    exact (Submodule.Quotient.nontrivial_iff).mpr hne
  -- `m ∉ Ass Q`: otherwise `depth R ≤ rs.length`, contradicting `hlt`.
  have hnotass : m ∉ associatedPrimes R Q := by
    intro hass
    have hbound : Module.depthSup R m R ≤ (rs.length : ℕ∞) :=
      depth_le_length_of_maximalIdeal_mem_associatedPrimes_quot rs hrsm hrsR hass
    exact absurd (lt_of_lt_of_le hlt hbound) (lt_irrefl _)
  -- A regular element of m on Q exists, giving positive depth.
  have hreg : ∃ x ∈ m, IsSMulRegular Q x :=
    (exists_smulRegular_iff_maximalIdeal_notMem_associatedPrimes).mpr hnotass
  exact depth_pos_of_exists_smulRegular hreg

end
