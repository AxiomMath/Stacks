module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.LinearMap
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth and the vanishing of `Ext` groups
-/

/-!
# Depth and the vanishing of `Ext` groups

Stacks Tag 00LW (Lemma 10.72.5).

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪` and residue
field `κ = R/𝔪`, and let `M` be a nonzero finite (finitely generated) `R`-module.
Then
  `depth(M) = min { i ∈ ℕ | Ext^i_R(κ, M) ≠ 0 }`.

Equivalently, writing `i(M)` for the smallest integer `i ≥ 0` with
`Ext^i_R(κ, M)` nonzero, this minimum exists and `depth(M) = i(M)`.
-/

@[expose] public section

-- * `depth(M)` is the `𝔪`-depth of `M`, i.e. the supremum of the lengths of
--   `M`-regular sequences contained in `𝔪`. This is `Module.depthSup R 𝔪 M : ℕ∞`.
--
-- * `Ext^i_R(κ, M)` is the categorical Ext group
--   `CategoryTheory.Abelian.Ext (ModuleCat.of R κ) (ModuleCat.of R M) i`, an
--   abelian group. "Nonzero" means this group is `Nontrivial`.
--
-- * The residue field `κ = R/𝔪` is represented as the `R`-module
--   `R ⧸ IsLocalRing.maximalIdeal R`.
--
-- * The hypothesis "`M` is nonzero" is encoded as `Nontrivial M`.
--
-- * The statement is self-contained: it asserts that the set of indices `i` with
--   `Ext^i_R(κ, M) ≠ 0` has a least element `n` (so the minimum exists, capturing
--   that the depth is finite), and that `depth(M)` equals the cast of `n` into
--   `ℕ∞`.

open CategoryTheory CategoryTheory.Abelian
universe u

-- We reuse the Mathlib definitions `Module.depthSup` and `CategoryTheory.Abelian.Ext`.
-- No new definitions are required; we record the relevant data through the
-- statement below. `R` and `M` are taken in the same universe `u` so that
-- `ModuleCat.of R (R ⧸ 𝔪)` and `ModuleCat.of R M` live in the same category.

/-
## Proof outline (Stacks Tag 00LW) and decomposition into sub-lemmas

Write `𝔪 = IsLocalRing.maximalIdeal R`, `κ = R ⧸ 𝔪`, and for an `R`-module `N`
write `i(N)` for the least `i` with `Ext^i(κ, N) ≠ 0`. The theorem is
`depth(M) = i(M)`, including the assertion that both are finite.

The proof is decomposed into three named sub-lemmas, mirroring the three pieces
the assembly needs:

  (A) `Module.depthSup_eq_natCast` : the depth of a nonzero finite module over a
      Noetherian local ring is a finite natural number, `depth(M) = (d : ℕ∞)`.
      (Stacks Tag 0AUJ + Nakayama: `M ≠ 𝔪 M`, so every `M`-regular sequence in
      `𝔪` has length `≤ dim M < ∞`.)

  (B) `ext_nontrivial_of_depth_eq` : if `depth(M) = (d : ℕ∞)` then
      `Ext^d(κ, M) ≠ 0` (the membership `d ∈ S`).  This is the heart: induction
      on `d` using the smul short exact sequence and the Ext long exact sequence.

  (C) `ext_eq_zero_of_lt_depth` : if `depth(M) = (d : ℕ∞)` then for every `j < d`
      we have `Ext^j(κ, M) = 0` (the lower bound).  Same induction.

From (A) we obtain `d` with `depth(M) = d`; then `(B)` gives `d ∈ S` and `(C)`
gives `d ≤ i` for every `i ∈ S`, i.e. `IsLeast S d`.  Combined with `depth = d`
this is exactly the theorem.
-/

-- Abbreviation used throughout: the Ext group `Ext^i(κ, M)`.
-- We keep it inline in the statements below to avoid section-variable issues.

/-- **(A) Depth finiteness.** For a nonzero finite module `M` over a Noetherian
local ring `(R, 𝔪)`, the depth is a finite natural number.

*Argument.* Since `M ≠ 0` and `𝔪 ⊆ Jacobson radical`, Nakayama gives `M ≠ 𝔪 M`.
By Stacks Tag 0AUJ (Lemma 10.72.4) the depth `depth_𝔪(M)` is bounded above by
`dim(Supp M) < ∞`; concretely, no `M`-regular sequence in `𝔪` can have length
exceeding the dimension, so the supremum defining `Module.depthSup` is attained at
some natural number. Hence `Module.depthSup R 𝔪 M = (d : ℕ∞)` for some `d : ℕ`.

Implementation note: `Module.depthSup` is the `sSup` over lengths of `M`-regular
sequences in `𝔪`. Finiteness reduces to showing this set of lengths is bounded.
A regular sequence of length `n` strictly increases (e.g. via the codimension /
support dimension), bounded by `Module.support`/Krull-dimension finiteness for
finite modules over Noetherian rings (`Module.Finite` + `IsNoetherianRing`). -/
@[ega "0 16.4.5" "partial"]
theorem Module.depthSup_eq_natCast {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Nontrivial M) :
    ∃ d : ℕ, Module.depthSup R (IsLocalRing.maximalIdeal R) M = (d : ℕ∞) := by
  -- supportDim is finite and nonzero-bot
  have hne_bot : Module.supportDim R M ≠ ⊥ := Module.supportDim_ne_bot_of_nontrivial R M
  have hle_krull : Module.supportDim R M ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
  have hne_top : Module.supportDim R M ≠ ⊤ := by
    intro h
    rw [h] at hle_krull
    exact ringKrullDim_ne_top (top_le_iff.mp hle_krull)
  -- extract a finite D : ℕ with supportDim R M = D
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Module.supportDim R M = (D : WithBot ℕ∞) := by
    lift (Module.supportDim R M) to ℕ∞ using hne_bot with y hy
    have hy' : y ≠ ⊤ := by
      intro hc; apply hne_top; rw [hc]; rfl
    obtain ⟨D, rfl⟩ := WithTop.ne_top_iff_exists.mp hy'
    exact ⟨D, by norm_cast⟩
  -- bound the depth by D, hence finite.  Every M-regular sequence rs in 𝔪 has
  -- supportDim(M ⧸ rs•M) + |rs| = supportDim M = D, so |rs| ≤ D.
  have hdepth_le : Module.depthSup R (IsLocalRing.maximalIdeal R) M ≤ (D : ℕ∞) := by
    rw [Module.depthSup]
    apply sSup_le
    rintro n ⟨rs, hlen, hmem, hreg⟩
    subst hlen
    have heq := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
    rw [hD] at heq
    set a := Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) with ha
    rcases eq_or_ne a ⊥ with hab | hab
    · simp [hab] at heq
    · lift a to ℕ∞ using hab with b
      calc
        (rs.length : ℕ∞) ≤ b + rs.length := le_add_self
        _ = D := by exact_mod_cast heq
  -- depth ≠ ⊤, hence depth = ↑d for some d : ℕ
  have hne : Module.depthSup R (IsLocalRing.maximalIdeal R) M ≠ ⊤ := by
    intro h; rw [h] at hdepth_le
    exact absurd hdepth_le (by simp)
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hne
  exact ⟨d, hd.symm⟩

/- ============================================================================
   Helper lemmas feeding the simultaneous induction proving (B) and (C).
   These are the next-layer subgoals (left unproved below).  The crucial
   STRUCTURAL point: (B) and (C) are entangled — (B) at stage `d+1` needs the
   subsingleton `Ext^d(κ,M)=0` which is (C) at the SAME stage `d+1`, while (C)
   at `d+1` needs (B)/(C) at the strictly smaller stage `d` applied to the
   quotient `M/xM`.  We therefore prove the combined statement
   `ext_depth_combined` by ONE induction on `d`, and derive both (B) and (C)
   from it.  The analytic kernel is the depth recurrence (Stacks 090R). -/

/-- **(D) Nakayama:** for `M` nonzero finite and `x ∈ 𝔪`, `M/xM ≠ 0`.
Reduces to `x • ⊤ < ⊤` via `Submodule.Quotient.nontrivial_iff`; `x • ⊤ ≠ ⊤`
is Nakayama (`x ∈ 𝔪 ⊆ Jacobson radical`, `M` finitely generated).
Candidate Mathlib inputs: `Submodule.Quotient.nontrivial_iff`,
`Module.eq_top_of_smul_eq_top`/`Submodule.smul_top`/`top_ne_smul`. -/
@[ega "0 7.1.13" "(x), special case", ega "IV 2.5.5.4" "special case"]
theorem nontrivial_quotSMulTop {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Nontrivial M) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) : Nontrivial (QuotSMulTop x M) := by
  rw [QuotSMulTop, Submodule.Quotient.nontrivial_iff]
  intro htop
  refine top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) ⊤
    (Module.Finite.fg_top (R := R) (M := M)) ?_
    ((Ideal.span_singleton_le_iff_mem _).2 (IsLocalRing.maximalIdeal_le_jacobson ⊥ hx)))
  rw [Submodule.ideal_span_singleton_smul]
  exact htop.ge

/- ============================================================================
   Sub-lemmas for the HARD direction of the depth recurrence (`depth_recurrence`,
   Stacks 090R).  The genuinely non-circular kernel is:
   - (C) zero-divisors = ⋃ associated primes (`isSMulRegular_iff_forall_notMem_associatedPrimes`);
   - permutability of regular sequences in the local case
     (Mathlib's `IsLocalRing.isRegular_of_perm`);
   - the exchange induction on length producing a regular sequence with a
     prescribed regular head (`exists_isRegular_cons_of_isRegular`).
   NO use of the Ext characterization of depth (that is downstream of this lemma):
   all are module-theoretic / associated-prime statements, strictly smaller than
   `depth_recurrence`. -/

/-- **(C) Zero-divisors are the union of associated primes.** For a Noetherian
ring `R` and a nonzero finite `R`-module `N`, an element `a` is `N`-regular iff
it lies in no associated prime of `N`.

*Proof.* (⇒) if `a ∈ 𝔭 = Ann(z)` with `z ≠ 0` then `a • z = 0`, so `a` is not
regular. (⇐) if `a` is not regular, `a • z = 0` for some `z ≠ 0`; the cyclic
submodule `R • z ≅ R/Ann(z)` is nonzero hence has an associated prime `𝔭`, and
`𝔭 ∈ Ass(N)` (associated primes are monotone under submodule inclusion); since
`a ∈ Ann(z) ⊆ 𝔭`, `a` lies in an associated prime.
Mathlib inputs: `mem_associatedPrimes_iff`/`associatedPrimes`, `IsSMulRegular`,
the `R/Ann` description of cyclic submodules. -/
@[ega "IV 3.1.9" "affine case X = Spec R", sga "2 III 2.1" "(ii) ⇔ (iv)"]
theorem isSMulRegular_iff_forall_notMem_associatedPrimes {R : Type u} [CommRing R]
    [IsNoetherianRing R] {N : Type u} [AddCommGroup N] [Module R N] (a : R) :
    IsSMulRegular N a ↔ ∀ p ∈ associatedPrimes R N, a ∉ p := by
  constructor
  · -- (⇒) if `a` is regular it lies in no associated prime
    intro hreg p ⟨hprime, x, hx⟩ ha
    rw [hx, Ideal.mem_radical_iff] at ha
    obtain ⟨n, hn⟩ := ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hn
    have hxne : x ≠ 0 := by
      intro hx0
      apply hprime.ne_top
      rw [hx, hx0, Submodule.colon_singleton_zero, Ideal.radical_eq_top]
    exact hxne (hreg.pow n (hn.trans (smul_zero _).symm))
  · -- (⇐) contrapositive: if `a` is not regular it lies in some associated prime
    rw [← not_imp_not]
    intro hnreg
    push Not
    rw [IsSMulRegular, Function.not_injective_iff] at hnreg
    obtain ⟨x, y, hxy, hne⟩ := hnreg
    set z : N := x - y with hz
    have hzne : z ≠ 0 := sub_ne_zero.mpr hne
    have haz : a • z = 0 := by rw [hz, smul_sub, hxy, sub_self]
    set S : Submodule R N := Submodule.span R {z} with hS
    have hSne : S ≠ ⊥ := fun h => hzne (Submodule.span_singleton_eq_bot.mp h)
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hSne
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R S
    refine ⟨p, associatedPrimes.subset_of_injective (Submodule.injective_subtype S) hp, ?_⟩
    obtain ⟨hprime, w, hw⟩ := hp
    rw [hw]
    apply Ideal.le_radical
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp w.property
    apply Subtype.ext
    simp only [Submodule.coe_smul, ZeroMemClass.coe_zero]
    rw [← hr, smul_smul, mul_comm, ← smul_smul, haz, smul_zero]

open scoped Pointwise in
/-- **Kernel of the exchange (Bruns–Herzog 1.2.10 length-2 core).** If `c` is
`N`-regular, `r` is `N/cN`-regular (so `[c,r]`/`[r,c]` is a regular pair) and `x`
is `N`-regular, all in `𝔪`, then `𝔪` is not an associated prime of `N/xN`. The
elementary diagram chase: `𝔪 = Ann(z̄)` in `N/xN` gives `rz, cz ∈ xN`; commuting
`x` past `r,c` and using regularity of `r` on `N/cN` and of `c, x` on `N` forces
`z ∈ xN`, i.e. `z̄ = 0`, a contradiction. -/
theorem kernel_maximalIdeal_notMem_assoc {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {N : Type u} [AddCommGroup N] [Module R N] {x r c : R}
    (hc_N : IsSMulRegular N c) (hr_quotc : IsSMulRegular (QuotSMulTop c N) r)
    (hx : IsSMulRegular N x) (hr𝔪 : r ∈ IsLocalRing.maximalIdeal R)
    (hc𝔪 : c ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x N) := by
  intro hp
  have hp' : (⊥ : Submodule R (QuotSMulTop x N)).IsAssociatedPrime (IsLocalRing.maximalIdeal R) :=
    hp
  rw [Submodule.isAssociatedPrime_iff] at hp'
  obtain ⟨hprime, wq, hwq⟩ := hp'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ wq
  have hmem :
    ∀ a, a ∈ IsLocalRing.maximalIdeal R → a • (Submodule.Quotient.mk z : QuotSMulTop x N) = 0 := by
    intro a ha
    rw [hwq] at ha
    rw [Submodule.mem_colon_singleton] at ha
    simpa using ha
  have hrz : r • z ∈ x • (⊤ : Submodule R N) := by
    have := hmem r hr𝔪
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  have hcz : c • z ∈ x • (⊤ : Submodule R N) := by
    have := hmem c hc𝔪
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  have hznot : z ∉ x • (⊤ : Submodule R N) := by
    intro hz
    apply hprime.ne_top
    have hz0 : (Submodule.Quotient.mk z : QuotSMulTop x N) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]; exact hz
    rw [hwq, hz0]
    rw [Submodule.colon_singleton_zero]
  rw [Submodule.mem_smul_pointwise_iff_exists] at hrz hcz
  obtain ⟨a, -, ha⟩ := hrz
  obtain ⟨b, -, hb⟩ := hcz
  have hcarb : c • a = r • b := by
    apply hx
    show x • (c • a) = x • (r • b)
    rw [smul_comm x c a, ha, smul_comm x r b, hb, smul_comm c r z, smul_comm r c z]
  have hb_in_cN : b ∈ c • (⊤ : Submodule R N) := by
    have hrb_quot : r • (Submodule.Quotient.mk b : QuotSMulTop c N) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hcarb,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨a, trivial, rfl⟩
    have hb_quot0 : (Submodule.Quotient.mk b : QuotSMulTop c N) = 0 :=
      hr_quotc (hrb_quot.trans (smul_zero r).symm)
    rwa [Submodule.Quotient.mk_eq_zero] at hb_quot0
  rw [Submodule.mem_smul_pointwise_iff_exists] at hb_in_cN
  obtain ⟨b', -, hb'⟩ := hb_in_cN
  apply hznot
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨b', trivial, ?_⟩
  apply hc_N
  show c • (x • b') = c • z
  rw [smul_comm c x b', hb', hb]

/-- Prime avoidance: `𝔪` contains an element outside a finite set of primes not containing `𝔪`. -/
private theorem exists_mem_maximalIdeal_forall_notMem {R : Type u} [CommRing R] [IsLocalRing R]
    {P : Set (Ideal R)} (hfin : P.Finite) (hprime : ∀ p ∈ P, p.IsPrime)
    (h : IsLocalRing.maximalIdeal R ∉ P) :
    ∃ e ∈ IsLocalRing.maximalIdeal R, ∀ p ∈ P, e ∉ p := by
  classical
  have havoid :=
    Ideal.subset_union_prime (s := hfin.toFinset) (f := id) (⊥ : Ideal R) (⊥ : Ideal R)
      (fun p hp _ _ => hprime p (hfin.mem_toFinset.1 hp)) (I := IsLocalRing.maximalIdeal R)
  have hnsub : ¬(↑(IsLocalRing.maximalIdeal R) ⊆
      ⋃ i ∈ (↑hfin.toFinset : Set (Ideal R)), (↑(id i) : Set R)) := by
    rw [havoid]
    rintro ⟨p, hps, hle⟩
    have := hprime p (hfin.mem_toFinset.1 hps)
    exact h (le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime p) hle ▸ hfin.mem_toFinset.1 hps)
  rw [Set.not_subset] at hnsub
  obtain ⟨e, he𝔪, heU⟩ := hnsub
  refine ⟨e, he𝔪, fun p hp hpe => heU ?_⟩
  rw [Set.mem_iUnion₂]
  exact ⟨p, by simpa using hp, hpe⟩

/-- **Prime avoidance for a regular element.** If `𝔪` is not an associated prime
of the nonzero finite module `N`, then (as every associated prime of a local ring
is contained in `𝔪`, hence equals `𝔪` if it contains `𝔪`) `𝔪` is not contained in
the (finite) union of associated primes, so prime avoidance yields an `N`-regular
element of `𝔪`. -/
@[sga "2 III 2.1" "(v) ⇒ (iv)"]
theorem exists_regular_of_maximalIdeal_notMem {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : IsLocalRing.maximalIdeal R ∉ associatedPrimes R N) :
    ∃ e ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N e := by
  obtain ⟨e, he𝔪, he⟩ := exists_mem_maximalIdeal_forall_notMem (associatedPrimes.finite R N)
    (fun p hp => hp.isPrime) h
  exact ⟨e, he𝔪, (isSMulRegular_iff_forall_notMem_associatedPrimes e).2 he⟩

/-- **Common regular element (double prime avoidance).** Given `N₁`-regular `a₁`
and `N₂`-regular `a₂` in `𝔪`, prime avoidance over `Ass(N₁) ∪ Ass(N₂)` yields a
single element of `𝔪` regular on both `N₁` and `N₂`. -/
theorem exists_regular_both {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {N₁ : Type u} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] {N₂ : Type u}
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] {a₁ a₂ : R}
    (ha₁ : a₁ ∈ IsLocalRing.maximalIdeal R) (ha₂ : a₂ ∈ IsLocalRing.maximalIdeal R)
    (hr₁ : IsSMulRegular N₁ a₁) (hr₂ : IsSMulRegular N₂ a₂) :
    ∃ e ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N₁ e ∧ IsSMulRegular N₂ e := by
  obtain ⟨e, he𝔪, he⟩ := exists_mem_maximalIdeal_forall_notMem
    ((associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂))
    (fun p hp => hp.elim (·.isPrime) (·.isPrime)) (by
      rintro (hp | hp)
      · exact (isSMulRegular_iff_forall_notMem_associatedPrimes a₁).mp hr₁ _ hp ha₁
      · exact (isSMulRegular_iff_forall_notMem_associatedPrimes a₂).mp hr₂ _ hp ha₂)
  exact ⟨e, he𝔪, (isSMulRegular_iff_forall_notMem_associatedPrimes e).2 fun p hp => he p (.inl hp),
    (isSMulRegular_iff_forall_notMem_associatedPrimes e).2 fun p hp => he p (.inr hp)⟩

/-- Over a Noetherian local ring, if `N` is a nonzero finite module, `x ∈ 𝔪` is
`N`-regular and `rs ⊆ 𝔪` is an `N`-regular sequence of length `m ≥ 1`, then there is
`ys ⊆ 𝔪` with `x :: ys` an `N`-regular sequence and `ys.length + 1 = m`. -/
theorem exists_isRegular_cons_of_isRegular {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (m : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      Nontrivial N →
        ∀ {x : R},
          x ∈ IsLocalRing.maximalIdeal R →
            IsSMulRegular N x →
            ∀ {rs : List R},
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) →
                RingTheory.Sequence.IsRegular N rs →
                rs.length = m →
                1 ≤ m →
                ∃ ys : List R,
                  (∀ r ∈ ys, r ∈ IsLocalRing.maximalIdeal R) ∧
                    RingTheory.Sequence.IsRegular N (x :: ys) ∧ ys.length + 1 = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro N _ _ _ hN x hx hxreg rs hmem hrs hlen hm1
    match m, rs, hlen, hm1 with
    | 0, _, _, hm1 => exact absurd hm1 (by norm_num)
    | 1, rs, hlen, _ =>
      refine ⟨[], by simp, ?_, by simp⟩
      rw [RingTheory.Sequence.isRegular_cons_iff]
      refine ⟨hxreg, ?_⟩
      have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop hN hx
      exact RingTheory.Sequence.IsRegular.nil _ _
    | (k + 2), rs, hlen,
      _ =>
      obtain ⟨r, c, rest, rfl⟩ : ∃ r c rest, rs = r :: c :: rest := by
        match rs, hlen with
        | r :: c :: rest, _ => exact ⟨r, c, rest, rfl⟩
      have hr𝔪 : r ∈ IsLocalRing.maximalIdeal R := hmem r (by simp)
      have hc𝔪 : c ∈ IsLocalRing.maximalIdeal R := hmem c (by simp)
      have hrc_reg : RingTheory.Sequence.IsRegular N [r, c] := by
        have hwk : RingTheory.Sequence.IsWeaklyRegular N [r, c] := by
          have := hrs.toIsWeaklyRegular
          rw [show (r :: c :: rest) = [r, c] ++ rest from rfl,
            RingTheory.Sequence.isWeaklyRegular_append_iff] at this
          exact this.left
        exact
          RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal N
            (by
              intro a ha; simp only [List.mem_cons, List.not_mem_nil] at ha
              rcases ha with rfl | rfl | h
              · exact hr𝔪
              · exact hc𝔪
              · exact absurd h (by simp))
            hwk
      have hcr_reg : RingTheory.Sequence.IsRegular N [c, r] :=
        IsLocalRing.isRegular_of_perm hrc_reg (List.Perm.swap c r [])
      have hc_N : IsSMulRegular N c := by
        rw [RingTheory.Sequence.isRegular_cons_iff] at hcr_reg; exact hcr_reg.left
      have hr_quotc : IsSMulRegular (QuotSMulTop c N) r := by
        rw [RingTheory.Sequence.isRegular_cons_iff] at hcr_reg
        rw [RingTheory.Sequence.isRegular_cons_iff] at hcr_reg
        exact hcr_reg.right.left
      have hnotmem := kernel_maximalIdeal_notMem_assoc hc_N hr_quotc hxreg hr𝔪 hc𝔪
      obtain ⟨d, hd𝔪, hd_reg⟩ := exists_regular_of_maximalIdeal_notMem hnotmem
      set rs := r :: c :: rest with hrsdef
      have hrslen : rs.length = k + 2 := hlen
      have hrsne : rs ≠ [] := by simp [hrsdef]
      set pre := rs.dropLast with hpre
      set lst := rs.getLast hrsne with hlst
      have hpre_len : pre.length = k + 1 := by
        rw [hpre, List.length_dropLast, hrslen]; omega
      have hsplit : pre ++ [lst] = rs := List.dropLast_append_getLast hrsne
      have hpre_mem : ∀ a ∈ pre, a ∈ IsLocalRing.maximalIdeal R := by
        intro a ha
        exact hmem a (List.mem_of_mem_dropLast (hpre ▸ ha))
      have htake : rs.take (k + 1) = pre := by
        rw [hpre, List.dropLast_eq_take, hrslen, show k + 2 - 1 = k + 1 from by omega]
      have hlst_reg : IsSMulRegular (N ⧸ Ideal.ofList pre • (⊤ : Submodule R N)) lst := by
        have hidx : (k + 1) < rs.length := by
          rw [hrslen]; omega
        have hrm := hrs.toIsWeaklyRegular.regular_mod_prev (k + 1) hidx
        rw [htake] at hrm
        rw [show rs[k + 1] = lst by
            rw [hlst, List.getLast_eq_getElem]; congr 1; omega] at hrm
        exact hrm
      obtain ⟨e, he𝔪, he_pre, he_x⟩ :=
        exists_regular_both (N₁ := N ⧸ Ideal.ofList pre • (⊤ : Submodule R N)) (N₂ :=
          QuotSMulTop x N) (a₁ := lst) (a₂ := d) (hmem lst (hsplit ▸ (by simp))) hd𝔪 hlst_reg
          hd_reg
      have hpre_wk : RingTheory.Sequence.IsWeaklyRegular N pre := by
        have := hrs.toIsWeaklyRegular
        rw [← hsplit, RingTheory.Sequence.isWeaklyRegular_append_iff] at this
        exact this.left
      have happend_wk : RingTheory.Sequence.IsWeaklyRegular N (pre ++ [e]) := by
        rw [RingTheory.Sequence.isWeaklyRegular_append_iff,
          RingTheory.Sequence.isWeaklyRegular_singleton_iff]
        exact ⟨hpre_wk, he_pre⟩
      have hcons_wk : RingTheory.Sequence.IsWeaklyRegular N (e :: pre) :=
        IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal happend_wk
          (List.perm_append_singleton e pre) fun a ha =>
            (List.mem_append.1 ha).elim (hpre_mem a) fun h => List.mem_singleton.1 h ▸ he𝔪
      have hcons_reg : RingTheory.Sequence.IsRegular N (e :: pre) := by
        refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal N
          (fun a ha => ?_) hcons_wk
        rcases List.mem_cons.1 ha with rfl | h
        · exact he𝔪
        · exact hpre_mem a h
      have he_N : IsSMulRegular N e :=
        ((RingTheory.Sequence.isRegular_cons_iff N e pre).1 hcons_reg).1
      have hpre_quotE : RingTheory.Sequence.IsRegular (QuotSMulTop e N) pre :=
        ((RingTheory.Sequence.isRegular_cons_iff N e pre).1 hcons_reg).2
      have hxe_reg : RingTheory.Sequence.IsRegular N [x, e] := by
        rw [RingTheory.Sequence.isRegular_cons_iff]
        refine ⟨hxreg, ?_⟩
        rw [RingTheory.Sequence.isRegular_cons_iff]
        refine ⟨he_x, ?_⟩
        have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop hN hx
        have : Nontrivial (QuotSMulTop e (QuotSMulTop x N)) := nontrivial_quotSMulTop this he𝔪
        exact RingTheory.Sequence.IsRegular.nil _ _
      have hex_reg : RingTheory.Sequence.IsRegular N [e, x] :=
        IsLocalRing.isRegular_of_perm hxe_reg (List.Perm.swap e x [])
      have hx_quotE : IsSMulRegular (QuotSMulTop e N) x := by
        rw [RingTheory.Sequence.isRegular_cons_iff] at hex_reg
        rw [RingTheory.Sequence.isRegular_cons_iff] at hex_reg
        exact hex_reg.right.left
      have hNe : Nontrivial (QuotSMulTop e N) := nontrivial_quotSMulTop hN he𝔪
      obtain ⟨vs, hvs_mem, hvs_reg, hvs_len⟩ :=
        ih (k + 1) (by omega) (QuotSMulTop e N) hNe hx hx_quotE hpre_mem hpre_quotE hpre_len
          (by omega)
      have hexvs_reg : RingTheory.Sequence.IsRegular N (e :: x :: vs) := by
        rw [RingTheory.Sequence.isRegular_cons_iff]
        exact ⟨he_N, hvs_reg⟩
      have hres : RingTheory.Sequence.IsRegular N (x :: e :: vs) :=
        IsLocalRing.isRegular_of_perm hexvs_reg (List.Perm.swap x e vs)
      refine ⟨e :: vs, ?_, hres, ?_⟩
      · intro a ha
        rw [List.mem_cons] at ha
        rcases ha with rfl | h
        · exact he𝔪
        · exact hvs_mem a h
      · simp only [List.length_cons]
        omega

/-- Over a Noetherian local ring, if `M` is a nonzero finite module, `x ∈ 𝔪` is
`M`-regular and `rs ⊆ 𝔪` is a nonempty `M`-regular sequence, then `M/xM` has a regular
sequence `ys ⊆ 𝔪` with `ys.length + 1 = rs.length`. -/
theorem exists_regularSeq_quot_of_regularSeq {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Nontrivial M) {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x)
    {rs : List R} (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
    (hrs : RingTheory.Sequence.IsRegular M rs) (hne : rs ≠ []) :
    ∃ ys : List R,
      (∀ r ∈ ys, r ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular (QuotSMulTop x M) ys ∧ ys.length + 1 = rs.length := by
  obtain ⟨ys, hys_mem, hys_reg, hys_len⟩ :=
    exists_isRegular_cons_of_isRegular rs.length M hM hx hreg hmem hrs rfl
      (by
        rcases List.length_pos_iff.mpr hne with h; omega)
  refine ⟨ys, hys_mem, ?_, hys_len⟩
  rw [RingTheory.Sequence.isRegular_cons_iff] at hys_reg
  exact hys_reg.right

/-- **(D') Depth recurrence (Stacks 090R) — the analytic kernel.** For `M`
nonzero finite over a Noetherian local ring and `x ∈ 𝔪` an `M`-regular element,
`depth(M/xM) + 1 = depth(M)` in `ℕ∞`.

*Proof sketch.* Two inequalities, both from the `sSup` definition of depth.
- `≥` (easy, DONE): prepend `x` to any `M/xM`-regular sequence in `𝔪`
  (`isRegular_cons_iff`), so `depth(M) ≥ depth(M/xM)+1`.
- `≤` (hard): every `M`-regular sequence in `𝔪` of length `m ≥ 1`
  yields an `M/xM`-regular sequence of length `m-1`
  (`exists_regularSeq_quot_of_regularSeq`), so `m ≤ depth(M/xM)+1`; take `sSup`. -/
@[ega "0 16.4.6",
  sga "2 III 2.5" "special case",
  sga "2 X 2.1" "more general",
  sga "2 XII 3.4" "more general"]
theorem depth_recurrence {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Nontrivial M) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 =
      Module.depthSup R (IsLocalRing.maximalIdeal R) M := by
  have hMx : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop hM hx
  -- EASY direction (§1a): depth(M/xM) + 1 ≤ depth(M).
  -- Prepend the regular element `x` to any `M/xM`-regular sequence `rs` in `𝔪`:
  -- `RingTheory.Sequence.isRegular_cons_iff` shows `x :: rs` is then `M`-regular,
  -- and the ℕ∞ identity `sSup S + 1 = sSup ((·+1) '' S)` (via `ENat.add_iSup`)
  -- pushes this through the `sSup` definition of `Module.depthSup`.
  have hge :
    Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 ≤
      Module.depthSup R (IsLocalRing.maximalIdeal R) M := by
    rw [Module.depthSup, Module.depthSup]
    have hne :
      ({n : ℕ∞ |
          ∃ rs,
            ↑(List.length rs) = n ∧
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
              RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs}).Nonempty :=
      ⟨0, [], rfl, by simp, RingTheory.Sequence.IsRegular.nil R _⟩
    have hsub :
      (· + 1) ''
          {n : ℕ∞ |
            ∃ rs,
              ↑(List.length rs) = n ∧
                (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
                RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs} ⊆
        {n : ℕ∞ |
          ∃ rs,
            ↑(List.length rs) = n ∧
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
              RingTheory.Sequence.IsRegular M rs} := by
      rintro m ⟨n, ⟨rs, hlen, hmem, hrs⟩, rfl⟩
      refine ⟨x :: rs, ?_, ?_, ?_⟩
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ← hlen]
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hx
        · exact hmem r hr
      · rw [RingTheory.Sequence.isRegular_cons_iff]
        exact ⟨hreg, hrs⟩
    have hid :
      sSup
            {n : ℕ∞ |
              ∃ rs,
                ↑(List.length rs) = n ∧
                  (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
                  RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs} +
          1 =
        sSup
          ((· + 1) ''
            {n : ℕ∞ |
              ∃ rs,
                ↑(List.length rs) = n ∧
                  (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
                  RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs}) := by
      rw [sSup_image, sSup_eq_iSup']
      rw [add_comm]
      have : Nonempty _ := hne.to_subtype
      rw [ENat.add_iSup, iSup_subtype]
      simp [add_comm]
    rw [hid]
    exact sSup_le_sSup hsub
  -- HARD direction (§1b, Rees argument): depth(M) ≤ depth(M/xM) + 1.
  -- This still requires the self-contained Rees induction `(†ₙ)`: prime avoidance
  -- (`Ideal.subset_union_prime`), finiteness of `Ass` (`associatedPrimes.finite`),
  -- the depth-0 ⟺ `𝔪 ∈ Ass` dictionary, exchange/permutation invariance of regular
  -- sequences in 𝔪, and the iso `N/(x,y)N ≅ (N/yN)/x(N/yN)`. Left for decomposition.
  have hle :
    Module.depthSup R (IsLocalRing.maximalIdeal R) M ≤
      Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 := by
    rw [Module.depthSup]
    apply sSup_le
    rintro n ⟨rs, hlen, hmem, hrs⟩
    subst hlen
    -- Every M-regular sequence rs in 𝔪 satisfies rs.length ≤ depth(M/xM) + 1.
    rcases eq_or_ne rs [] with hnil | hne
    · -- empty sequence: 0 ≤ depth(M/xM) + 1.
      subst hnil; simp
    · -- nonempty: exchange head to x, peel off, get (M/xM)-regular tail of length len-1.
      obtain ⟨ys, hys_mem, hys_reg, hys_len⟩ :=
        exists_regularSeq_quot_of_regularSeq hM hx hreg hmem hrs hne
      -- (ys.length : ℕ∞) ≤ depth(M/xM)
      have hdq :
        (ys.length : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) := by
        rw [Module.depthSup]
        exact le_sSup ⟨ys, rfl, hys_mem, hys_reg⟩
      -- rs.length = ys.length + 1, so (rs.length : ℕ∞) ≤ depth(M/xM) + 1.
      have : ((rs.length : ℕ) : ℕ∞) = (ys.length : ℕ∞) + 1 := by
        rw [← hys_len]; push_cast; ring
      rw [this]
      gcongr
  exact le_antisymm hge hle

/-- **(B₀) Base case of (B).** `depth(M) = 0 ⟹ Ext^0(κ,M)` nontrivial.
`Ext^0(κ,M) ≃ (κ →ₗ M)`
via `Ext.homEquiv₀.trans ModuleCat.homEquiv`; `depth=0` forbids an `M`-regular
element in `𝔪 = ann κ` (built from the `sSup` definition via
`isRegular_cons_iff`, `nontrivial_quotSMulTop`), so by
`IsSMulRegular.subsingleton_linearMap_iff` the Hom is not subsingleton. -/
@[ega "0 16.4.4" "Depth zero",
  sga "2 III 2.4" "(3)⇒(4)",
  sga "2 III 2.8" "Ext^0(k",
  sga "2 III 3.3" "special case",
  sga "2 III 3.4" "(3)⇒(1) for n = 1"]
theorem ext_zero_nontrivial_of_depth_zero {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Nontrivial M) (hd : Module.depthSup R (IsLocalRing.maximalIdeal R) M = (0 : ℕ∞)) :
    Nontrivial (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) 0) := by
  -- Ext^0(κ,M) ≃ (κ →ₗ[R] M)
  let e :=
    (Ext.homEquiv₀ (X := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (Y :=
          ModuleCat.of R M)).trans
      ModuleCat.homEquiv
  -- First show the Hom is nontrivial, i.e. not subsingleton.
  have hHom :
    Nontrivial (↑(ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) →ₗ[R] ↑(ModuleCat.of R M)) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    -- A subsingleton Hom yields an M-regular element r in ann κ = 𝔪.
    rw [IsSMulRegular.subsingleton_linearMap_iff] at hsub
    obtain ⟨r, hr_ann, hreg⟩ := hsub
    rw [Ideal.annihilator_quotient] at hr_ann
    -- Such an r gives the M-regular sequence [r] in 𝔪, so depth ≥ 1, contradiction.
    have hntq : Nontrivial (QuotSMulTop r M) := nontrivial_quotSMulTop hM hr_ann
    have hle : (1 : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) M := by
      rw [Module.depthSup]
      apply le_sSup
      refine ⟨[r], rfl, ?_, ?_⟩
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hr_ann
      · rw [RingTheory.Sequence.isRegular_cons_iff]
        exact ⟨hreg, RingTheory.Sequence.IsRegular.nil R _⟩
    rw [hd] at hle
    exact absurd hle (by norm_num)
  exact e.nontrivial

/-- **(C₀) Base case of (C).** `depth(M) > 0 ⟹ Ext^0(κ,M)` subsingleton.
`depth ≥ 1 ⟹ 𝔪 ∉ Ass(M) ⟹ Hom(κ,M) = 0`, transported across
`Ext.homEquiv₀` to `Ext^0`.  Uses `IsSMulRegular.subsingleton_linearMap_iff`
with a regular `r ∈ ann κ = 𝔪`, available since `depth > 0`. -/
@[sga "2 III 2.1" "(iv) ⇒ (i) for N = A/m",
  sga "2 III 2.4" "(4)⇒(3)",
  sga "2 III 2.8" "Ext^0(k",
  sga "2 III 3.3" "(iv) ⇒ (vi) for n = 1",
  sga "2 III 3.4" "(1)⇒(3) for n = 1"]
theorem ext_zero_subsingleton_of_depth_pos {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hpos : (0 : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) M) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) 0) := by
  -- Ext^0(κ,M) ≃ (κ →ₗ[R] M)
  let e :=
    (Ext.homEquiv₀ (X := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (Y :=
          ModuleCat.of R M)).trans
      ModuleCat.homEquiv
  -- It suffices to show the Hom is subsingleton; transport across e.symm.
  have hHom :
    Subsingleton
      (↑(ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) →ₗ[R] ↑(ModuleCat.of R M)) := by
    rw [IsSMulRegular.subsingleton_linearMap_iff]
    -- extract an M-regular element r ∈ 𝔪 from depth > 0
    rw [Module.depthSup, lt_sSup_iff] at hpos
    obtain ⟨n, ⟨rs, hlen, hmem, hreg⟩, hn0⟩ := hpos
    subst hlen
    match rs, hreg, hmem, hn0 with
    | x :: t, hreg, hmem, _ =>
      refine ⟨x, ?_, ?_⟩
      · rw [Ideal.annihilator_quotient]
        exact hmem x (by simp)
      · rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
        exact hreg.left
  have := hHom
  exact e.subsingleton

/-- **(F) Existence of a regular element when `depth > 0`.** `depth(M) > 0`
means `𝔪 ⊄ ⋃ Ass(M)`; prime avoidance (`Ideal.subset_union_prime`,
`associatedPrimes.finite`) yields `x ∈ 𝔪` avoiding every associated prime,
hence `IsSMulRegular M x`. -/
theorem exists_regular_of_depth_pos {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    (hpos : (0 : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) M) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular M x := by
  rw [Module.depthSup] at hpos
  rw [lt_sSup_iff] at hpos
  obtain ⟨n, ⟨rs, hlen, hmem, hreg⟩, hn0⟩ := hpos
  subst hlen
  match rs, hreg, hmem, hn0 with
  | x :: t, hreg, hmem, _ =>
    refine ⟨x, hmem x (by simp), ?_⟩
    rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
    exact hreg.left

/-- Multiplication by an element of the maximal ideal is zero on every `Ext^n(κ, N)`, since it
annihilates the residue field `κ`. -/
theorem ext_residueField_smul_eq_zero {R : Type u} [CommRing R] [IsLocalRing R] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) {N : ModuleCat.{u} R} {n : ℕ}
    (α : Ext.{u} (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) N n) : x • α = 0 := by
  have hxid : x • 𝟙 (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show x • y = 0
    induction y using Submodule.Quotient.induction_on with
    | _ z =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      show x * z ∈ _
      exact Ideal.mul_mem_right z _ hx
  rw [← Ext.mk₀_id_comp α, ← Ext.smul_comp, ← Ext.mk₀_smul, hxid, Ext.mk₀_zero, Ext.zero_comp]

/-- **(E) Membership transfer (Stacks 00LV+00LU).** For `x` `M`-regular, if
`Ext^e(κ,M)` is subsingleton and `Ext^e(κ,M/xM)` is nontrivial, then
`Ext^{e+1}(κ,M)` is nontrivial.  The proof uses the smul
SES `IsSMulRegular.smulShortComplex_shortExact` + Ext LES
`Ext.covariant_sequence_exact₃`: the connecting map
`δ : Ext^e(κ,M/xM) → Ext^{e+1}(κ,M)` is injective since the subsingleton
`Ext^e(κ,M)` kills the preceding term, so `Ext^{e+1}(κ,M)` is nonzero. -/
theorem ext_succ_nontrivial_of_transfer {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {x : R} (hreg : IsSMulRegular M x) (e : ℕ)
    (hsub :
      Subsingleton (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) e))
    (hnt :
      Nontrivial
        (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R (QuotSMulTop x M))
          e)) :
    Nontrivial
      (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) (e + 1)) := by
  set κ := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) with hκ
  set S := (ModuleCat.of R M).smulShortComplex x with hS
  have hSE : S.ShortExact := hreg.smulShortComplex_shortExact
  -- transport the nontriviality hypothesis to S.X₃ (definitionally M/xM)
  have hnt3 : Nontrivial (Ext κ S.X₃ e) := hnt
  -- the subsingleton hypothesis lives on S.X₂ (definitionally M)
  have hsub2 : Subsingleton (Ext κ S.X₂ e) := hsub
  -- pick a nonzero element α ∈ Ext^e(κ, M/xM)
  obtain ⟨α, hα⟩ := exists_ne (0 : Ext κ S.X₃ e)
  -- form δ(α) = α ∘ extClass ∈ Ext^{e+1}(κ, M)
  refine nontrivial_of_ne (α.comp hSE.extClass rfl) 0 ?_
  intro hcon
  -- if δ(α) = 0 then by exactness at the S.X₃ spot α = x₂ ∘ (mk₀ S.g)
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ κ hSE α rfl hcon
  -- but Ext^e(κ, M) is subsingleton, so x₂ = 0, hence α = 0, contradiction
  have hx20 : x₂ = 0 := hsub2.elim _ _
  rw [hx20, Ext.zero_comp] at hx₂
  exact hα hx₂.symm

/-- **(E') Vanishing transfer (Stacks 00LV+00LU).** For `x ∈ 𝔪` `M`-regular, if
`Ext^e(κ,M/xM)` is subsingleton then `Ext^{e+1}(κ,M)` is subsingleton.  Same
collapsed SES `0 → Ext^e(κ,M) → Ext^e(κ,M/xM) → Ext^{e+1}(κ,M) → 0`: with the
middle term `0`, the right term `Ext^{e+1}(κ,M)` (a quotient of it) is `0`. -/
theorem ext_succ_subsingleton_of_transfer {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (e : ℕ)
    (hsub :
      Subsingleton
        (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R (QuotSMulTop x M))
          e)) :
    Subsingleton
      (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) (e + 1)) := by
  set κ := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) with hκ
  set S := (ModuleCat.of R M).smulShortComplex x with hS
  have hSE : S.ShortExact := hreg.smulShortComplex_shortExact
  -- transport the middle-term subsingleton hypothesis to S.X₃ (definitionally M/xM)
  have hsub3 : Subsingleton (Ext κ S.X₃ e) := hsub
  -- it suffices to show every element of Ext^{e+1}(κ, M) is zero
  apply subsingleton_of_forall_eq (0 : Ext κ (ModuleCat.of R M) (e + 1))
  intro x₁
  -- x₁ ∘ (mk₀ S.f) = x • x₁ = 0, since S.f = x • 𝟙 M
  have hcomp : x₁.comp (Ext.mk₀ S.f) (add_zero (e + 1)) = 0 := by
    have hfeq : Ext.mk₀ S.f = x • Ext.mk₀ (𝟙 (ModuleCat.of R M)) := by
      have hf : S.f = x • 𝟙 (ModuleCat.of R M) := rfl
      rw [hf]
      exact Ext.mk₀_smul x (𝟙 (ModuleCat.of R M))
    have step :
      x₁.comp (Ext.mk₀ S.f) (add_zero (e + 1)) =
        x₁.comp (x • Ext.mk₀ (𝟙 (ModuleCat.of R M))) (add_zero (e + 1)) := by
      congr 1
    rw [step, Ext.comp_smul, Ext.comp_mk₀_id]
    exact ext_residueField_smul_eq_zero hx x₁
  -- exactness of the Ext LES at the M-spot: x₁ is the image of some x₃ ∈ Ext^e(κ, M/xM)
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ κ hSE x₁ hcomp (n₀ := e) rfl
  -- but Ext^e(κ, M/xM) is a subsingleton, so x₃ = 0, hence x₁ = 0
  have hx30 : x₃ = 0 := hsub3.elim _ _
  rw [hx30, Ext.zero_comp] at hx₃
  exact hx₃.symm

-- needed: `ext_depth_combined`'s `WithTop.add_right_cancel (by simp)` step requires
-- `ℕ∞` and `WithTop ℕ` to be accepted as defeq without unfolding the abbreviation.
set_option backward.isDefEq.respectTransparency false in
/-- **Combined simultaneous induction (heart of 00LW).** For all `d`, every
nonzero finite `M`:
- (Bₐ) `depth M = d ⟹ Ext^d(κ,M)` nontrivial;
- (Cₐ) `∀ e ≤ d`, `e < depth M ⟹ Ext^e(κ,M)` subsingleton.

Proven by induction on `d`, dispatching the base cases to (B₀)/(C₀) and the
inductive step to the transfer lemmas (E)/(E') and the depth recurrence (D').
The two halves of the conclusion are mutually dependent, which is exactly why
they are bundled.  This single induction discharges BOTH sub-lemmas (B) and
(C). -/
@[sga "2 III 2.4" "(3)⇔(4)",
  sga "2 III 2.8" "partial",
  sga "2 III 3.3" "special case",
  sga "2 III 3.4" "(1)⇔(3) for nonzero M"]
theorem ext_depth_combined {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (d : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      Nontrivial M →
        (Module.depthSup R (IsLocalRing.maximalIdeal R) M = (d : ℕ∞) →
            Nontrivial
              (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) d)) ∧
          (∀ e : ℕ,
            e ≤ d →
              (e : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) M →
              Subsingleton
                (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) e)) := by
  induction d with
  | zero =>
    intro M _ _ _ hM
    refine ⟨fun hd => ext_zero_nontrivial_of_depth_zero hM hd, ?_⟩
    intro e he hlt
    interval_cases e
    exact ext_zero_subsingleton_of_depth_pos hlt
  | succ d ih =>
    intro M _ _ _ hM
    -- Prove the (C) component first (as `hCstep`), since (B)'s step needs it at e=d.
    have hCstep :
      ∀ e : ℕ,
        e ≤ d + 1 →
          (e : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) M →
          Subsingleton
            (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) e) := by
      intro e he hlt
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le he) with hee | hee
      · -- e ≤ d : it is (Cₐ) for M at stage d.
        exact (ih M hM).right e (Nat.lt_succ_iff.mp hee) hlt
      · -- e = d+1 : use the vanishing transfer with M/xM at stage d.
        subst hee
        have hpos : (0 : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) M :=
          lt_trans (by exact_mod_cast Nat.succ_pos d) hlt
        obtain ⟨x, hx, hreg⟩ := exists_regular_of_depth_pos hpos
        have hMx : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop hM hx
        have hrec := depth_recurrence hM hx hreg
        -- d < depth(M/xM):  depth(M/xM)+1 = depth M > d+1.
        have hdqlt :
          (d : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) := by
          have hh :
            ((d + 1 : ℕ) : ℕ∞) <
              Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 := by
            rw [hrec]; exact hlt
          have h2 :
            ((d : ℕ∞) + 1) <
              Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 := by
            push_cast at hh; convert hh using 2
          exact
            (WithTop.add_lt_add_iff_right
                  (show (1 : ℕ∞) ≠ ⊤ by exact_mod_cast ENat.natCast_ne_top 1)).mp
              h2
        have hsubq :
          Subsingleton
            (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
              (ModuleCat.of R (QuotSMulTop x M)) d) :=
          (ih (QuotSMulTop x M) hMx).right d (le_refl d) hdqlt
        exact ext_succ_subsingleton_of_transfer hx hreg d hsubq
    refine ⟨?_, hCstep⟩
    -- (B_{d+1}): depth = d+1 ⟹ Ext^{d+1}(κ,M) nontrivial.
    intro hd
    have hpos : (0 : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) M := by
      rw [hd]; exact_mod_cast Nat.succ_pos d
    obtain ⟨x, hx, hreg⟩ := exists_regular_of_depth_pos hpos
    have hMx : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop hM hx
    have hrec := depth_recurrence hM hx hreg
    -- depth(M/xM) = d.
    have hdq : Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) = (d : ℕ∞) := by
      rw [hd] at hrec
      have hcast : ((d : ℕ∞) + 1) = ((d + 1 : ℕ) : ℕ∞) := by
        push_cast; ring
      rw [← hcast] at hrec
      exact WithTop.add_right_cancel (by simp) hrec
    -- Ext^d(κ,M) subsingleton = (C) at stage d+1, e=d.
    have hsub :
      Subsingleton
        (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) d) := by
      apply hCstep d (Nat.le_succ d)
      rw [hd]; exact_mod_cast Nat.lt_succ_self d
    -- Ext^d(κ,M/xM) nontrivial = (B) at stage d for the quotient.
    have hntq :
      Nontrivial
        (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R (QuotSMulTop x M))
          d) :=
      (ih (QuotSMulTop x M) hMx).left hdq
    exact ext_succ_nontrivial_of_transfer hreg d hsub hntq

/-- **(B) Membership.** If `depth_𝔪(M) = d` then `Ext^d(κ, M)` is nonzero.

*Argument (induction on `d`).*

Base case `d = 0`: `depth(M) = 0` means there is NO `M`-regular element in `𝔪`,
i.e. every `x ∈ 𝔪` is a zerodivisor on `M`, i.e. `𝔪 ⊆ ⋃ associated primes`, so by
prime avoidance `𝔪 ∈ Ass(M)` (Stacks 00LD `biUnion_associatedPrimes_eq_zero_divisors`).
Then `Hom_R(κ, M) ≠ 0`: an associated prime `𝔪 = ann(m)` gives an injection
`κ = R/𝔪 ↪ M`, a nonzero element of `Hom_R(κ, M)`. Via `Ext.homEquiv₀`,
`Ext^0(κ, M) ≅ Hom_R(κ, M) ≠ 0`. Concretely: `Ext^0 ≅ Hom` is nonzero iff
`¬ Subsingleton (κ →ₗ[R] M)`, and by `IsSMulRegular.subsingleton_linearMap_iff`
this subsingleton-ness is equivalent to `∃ r ∈ ann(κ) = 𝔪, IsSMulRegular M r`,
which fails exactly when `depth = 0`.

Inductive step `d = e + 1`: since `depth(M) = e + 1 > 0`, by the depth recurrence
(sub-lemma (D), Stacks 090R) choose `x ∈ 𝔪` with `IsSMulRegular M x` and
`depth(M/xM) = e`. The smul short exact sequence
`0 → M --x--> M → M/xM → 0` (`IsSMulRegular.smulShortComplex_shortExact`) feeds the
Ext long exact sequence (`Ext.covariantSequence_exact`, Stacks 00LU). Because
`x ∈ 𝔪 = ann(κ)` annihilates `κ`, multiplication by `x` on each `Ext^i(κ, M)` is
the zero map (Stacks 00LV), so the LES breaks into short exact sequences
`0 → Ext^i(κ,M) → Ext^i(κ,M/xM) → Ext^{i+1}(κ,M) → 0`.
In particular `Ext^{e+1}(κ,M) ≅ coker(Ext^e(κ,M) → Ext^e(κ,M/xM))`, and the
surjection `Ext^e(κ,M/xM) ↠ Ext^{e+1}(κ,M)` together with the induction
hypothesis `Ext^e(κ,M/xM) ≠ 0` plus the injection `Ext^e(κ,M) ↪ Ext^e(κ,M/xM)`
forces `Ext^{e+1}(κ,M) ≠ 0` (this is where the index shift `i(M/xM)=i(M)-1`
combines with `depth(M/xM)=depth(M)-1`). -/
@[ega "0 16.4.4" "Ext^d(k",
  sga "2 III 2.4" "(3)⇒(4)",
  sga "2 III 2.8" "Ext^d(k",
  sga "2 III 3.3" "special case",
  sga "2 III 3.4" "(3)⇒(1)"]
theorem ext_nontrivial_of_depth_eq {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Nontrivial M) (d : ℕ)
    (hd : Module.depthSup R (IsLocalRing.maximalIdeal R) M = (d : ℕ∞)) :
    Nontrivial (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) d) := by
  -- Discharged by the combined simultaneous induction.
  exact (ext_depth_combined d M hM).left hd

/-- **(C) Lower bound.** If `depth_𝔪(M) = d` then `Ext^j(κ, M) = 0` for all
`j < d`; equivalently, `Ext^j(κ, M)` is a subsingleton for `j < d`.

*Argument (induction on `d`).* For `d = 0` there is nothing to prove (no `j < 0`).
For `d = e+1`: choose `x ∈ 𝔪` regular on `M` with `depth(M/xM) = e` as in (B).
The same short exact sequences
`0 → Ext^{j-1}(κ,M) → Ext^{j-1}(κ,M/xM) → Ext^j(κ,M) → 0` (for `j ≥ 1`) and the
base relation `Ext^0(κ,M) = Hom(κ,M) = 0` (because `depth > 0` means `𝔪 ∉ Ass M`,
so `Hom(κ,M)=0` via `IsSMulRegular.subsingleton_linearMap_iff` with the regular
element `x ∈ ann κ`) give, by induction on `j ≤ e`, that `Ext^j(κ,M/xM)=0` for
`j < e` and hence `Ext^j(κ,M)=0` for `j < e+1`. Precisely: `Ext^0(κ,M)=0`
directly; for `1 ≤ j < e+1`, the injection `Ext^{j-1}(κ,M) ↪ Ext^{j-1}(κ,M/xM)`
is irrelevant—what we use is that `Ext^j(κ,M)` injects into … no: we use that the
quotient `Ext^j(κ,M)` is a sub/quotient controlled by `Ext^{j-1}(κ,M/xM)` and
`Ext^j(κ,M/xM)`, both of which vanish for `j < e+1` by the induction hypothesis
`Ext^k(κ,M/xM)=0` for `k < e`. -/
@[ega "0 16.4.4" "Ext^j(k",
  sga "2 III 2.4" "(4)⇒(3)",
  sga "2 III 2.8" "Ext^j(k",
  sga "2 III 3.3" "special case",
  sga "2 III 3.4" "(1)⇒(3)"]
theorem ext_eq_zero_of_lt_depth {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Nontrivial M) (d : ℕ)
    (hd : Module.depthSup R (IsLocalRing.maximalIdeal R) M = (d : ℕ∞)) (j : ℕ) (hj : j < d) :
    ¬Nontrivial (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) j) := by
  -- Discharged by the combined simultaneous induction: `Ext^j(κ,M)` is a
  -- subsingleton for `j < d = depth M`, hence not nontrivial.
  have hsub :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) j) :=
    (ext_depth_combined j M hM).right j (le_refl j)
      (by
        rw [hd]; exact_mod_cast hj)
  rw [not_nontrivial_iff_subsingleton]
  exact hsub

/-- **Stacks Tag 00LW (Lemma 10.72.5).** Let `R` be a Noetherian local ring with
maximal ideal `𝔪`, residue field `κ = R/𝔪`, and let `M` be a nonzero finite
`R`-module. Then there is a least index `n` for which `Ext^n_R(κ, M)` is nonzero,
and the depth of `M` equals this index `n`:
`depth(M) = min { i | Ext^i_R(κ, M) ≠ 0 }`. -/
@[stacks 00LW,
  sga "2 III 2.8" "local case",
  ega "0 16.4.4" "depth = least n Ext≠0",
  sga "2 III 3.4" "(1) <=> (3)",
  ega "0 16.4.5" "partial",
  sga "2 III 2.4" "(3)⇔(4)",
  sga "2 III 2.7" "special case",
  sga "2 III 3.3" "special case"]
theorem depth_eq_least_nonzero_ext {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Nontrivial M) :
    ∃ n : ℕ,
      IsLeast
          {i : ℕ |
            Nontrivial
              (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) i)}
          n ∧
        Module.depthSup R (IsLocalRing.maximalIdeal R) M = (n : ℕ∞) := by
  -- Notation: `S` is the set of indices `i` with `Ext^i(κ, M)` nonzero.
  set S : Set ℕ :=
    {i : ℕ |
      Nontrivial (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) i)} with
    hS
  -- (A) depth is a finite natural number `d`.
  obtain ⟨d, hd⟩ := Module.depthSup_eq_natCast (R := R) (M := M) hM
  -- The witness is `n := d`; show `IsLeast S d` and `depth = d`.
  refine ⟨d, ⟨?_, ?_⟩, hd⟩
  · -- (B) `d ∈ S`: `Ext^d(κ, M)` is nonzero.
    show Nontrivial _
    exact ext_nontrivial_of_depth_eq hM d hd
  · -- Lower bound: every `i ∈ S` satisfies `d ≤ i`.
    intro i hi
    -- `hi : Nontrivial (Ext … i)`.  Suppose `i < d`; then (C) gives a
    -- contradiction with `hi`.
    by_contra h
    -- `h : ¬ d ≤ i`, i.e. `i < d`; then (C) gives a contradiction with `hi`.
    exact ext_eq_zero_of_lt_depth hM d hd i (Nat.lt_of_not_le h) hi

end
