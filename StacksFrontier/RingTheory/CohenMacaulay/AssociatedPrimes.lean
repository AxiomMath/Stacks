module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# Associated primes of a Cohen-Macaulay module are minimal in its support

Throughout, `R` is a commutative ring, `M` an `R`-module, and `𝔪` the maximal ideal
of a local ring `R`. The notions used from Mathlib are
`associatedPrimes R M : Set (Ideal R)`, the associated primes of `M`;
`Module.support R M : Set (PrimeSpectrum R)`, the support of `M`, which for finitely
generated `M` is the zero locus of the annihilator;
`Module.supportDim R M : WithBot ℕ∞`, the Krull dimension of the support;
`RingTheory.Sequence.IsRegular M rs`, saying that the finite list `rs = [f₁, …, f_r]`
is an `M`-regular sequence; and `(Module.annihilator R M).minimalPrimes`, the minimal
primes over the annihilator, equivalently the minimal primes of the support.

Mathlib has no notion of depth or of Cohen-Macaulay module, so both are defined here.

For a local ring `(R, 𝔪)` and an `R`-module `M`, the *depth* of `M`, meaning its
`𝔪`-depth, is the supremum in `ℕ∞ = ℕ ∪ {∞}` of the lengths of `M`-regular sequences
contained in `𝔪`. For a Noetherian local ring `(R, 𝔪)` and a finite `R`-module `M`,
`M` is *Cohen-Macaulay* when `depth M = dim (Supp M)`. A prime `𝔭` is an *embedded
associated prime* of `M` when `𝔭 ∈ associatedPrimes R M` and `𝔭` is not minimal among
the associated primes, that is, `𝔮 < 𝔭` for some `𝔮 ∈ associatedPrimes R M`.

The main result: let `(R, 𝔪)` be a Noetherian local ring and `M` a finite
Cohen-Macaulay `R`-module. Then every associated prime `𝔭` of `M` satisfies
`dim (R/𝔭) = dim (Supp M)` and is a minimal prime of the support of `M`; in
particular `M` has no embedded associated prime.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence in
/-- The `𝔪`-depth of an `R`-module `M` over a local ring `(R, 𝔪)`: the supremum of
the lengths of `M`-regular sequences whose entries all lie in the maximal ideal. -/
@[ega "0 16.4.5" "partial", sga "2 III 2.8" "prof M for a local ring"]
noncomputable def depthM (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  ⨆ rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M rs}, (rs.length : ℕ∞)

/-- Definition 2: `M` is Cohen–Macaulay when its depth equals the dimension of its
support. -/
@[ega "0 16.5.1" "nonzero-module clause", ega "IV 5.7.1" "F is Cohen–Macaulay at x", ega "IV 7.5.3"]
def IsCM (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  (depthM R M : WithBot ℕ∞) = Module.supportDim R M

-- `IsEmbeddedAssociatedPrime` is provided by
-- `StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded` (imported above).

-- Auxiliary lemmas

/-- Krull dimension is monotone under set inclusion. -/
private lemma krullDim_subset {α : Type*} [Preorder α] {s t : Set α} (h : s ⊆ t) :
    Order.krullDim s ≤ Order.krullDim t := by
  apply Order.krullDim_le_of_strictMono (Set.inclusion h)
  intro a b hab; exact hab

/-- Strict drop of the dimension of a residue ring along a strict inclusion of primes. -/
private lemma ringKrullDim_quotient_strictAnti {R : Type*} [CommRing R] [FiniteRingKrullDim R]
    (p₀ p : Ideal R) [hp₀ : p₀.IsPrime] [hp : p.IsPrime] (hlt : p₀ < p) :
    ringKrullDim (R ⧸ p) < ringKrullDim (R ⧸ p₀) := by
  rw [← coheight_eq_ringKrullDim_quotient ⟨p, hp⟩, ← coheight_eq_ringKrullDim_quotient ⟨p₀, hp₀⟩]
  have hco : Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) < ⊤ := Order.coheight_lt_top _
  have hpp : (⟨p₀, hp₀⟩ : PrimeSpectrum R) < (⟨p, hp⟩ : PrimeSpectrum R) := hlt
  exact_mod_cast Order.coheight_strictAnti hpp hco

/-- The annihilator of `M` is contained in every associated prime of `M`. -/
private lemma annihilator_le_of_isAssociatedPrime {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {p : Ideal R} (h : IsAssociatedPrime p M) :
    Module.annihilator R M ≤ p := by
  have := h.annihilator_le
  rwa [Submodule.annihilator_top] at this

/-- For a prime `p` containing the annihilator of `M`, `dim (R ⧸ p) ≤ dim (Supp M)`. This is
the easy inclusion `V(p) ⊆ V(Ann M)`. -/
private lemma ringKrullDim_quotient_le_supportDim {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hle : Module.annihilator R M ≤ p) :
    ringKrullDim (R ⧸ p) ≤ Module.supportDim R M := by
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
      ringKrullDim_quotient, ringKrullDim_quotient]
  exact krullDim_subset (PrimeSpectrum.zeroLocus_anti_mono hle)

open Pointwise in
/-- **Stacks 10.63.4.** For `k : ℕ`, every associated prime of `M ⧸ xᵏ • ⊤` is an
associated prime of `M ⧸ x • ⊤`, for `x` an `M`-regular element.

This is the filtration step: `M ⊇ x M ⊇ ⋯ ⊇ xᵏ M` realises `M ⧸ xᵏ • ⊤` as an
iterated extension whose graded pieces `(xⁱ M)/(x^{i+1} M)` are subquotients
comparable to quotients of `M ⧸ x • ⊤`, and the associated primes of an extension
lie in the union of those of the sub and of the quotient. Regularity of `x` is
needed; the proof is by induction on `k` via the short exact sequence. -/
private lemma associatedPrime_quotSMulTop_of_pow
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R) (k : ℕ)
    (hx : IsSMulRegular M x)
    {q : Ideal R} (hq : IsAssociatedPrime q (M ⧸ (x ^ k • ⊤ : Submodule R M))) :
    IsAssociatedPrime q (QuotSMulTop x M) := by
  -- counterexample R=k[x,y]_(x,y), M=R/(xy), k=2, q=(x,y).
  induction k generalizing q with
  | zero =>
    rw [pow_zero, one_smul] at hq
    exfalso
    obtain ⟨hp, y, hy⟩ := hq
    apply hp.ne_top
    rw [hy]
    have hcolon : (⊥ : Submodule R (M ⧸ (⊤ : Submodule R M))).colon {y} = ⊤ := by
      ext r
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Submodule.mem_top, iff_true]
      exact Subsingleton.elim _ _
    rw [hcolon, Ideal.radical_top]
  | succ k ih =>
    set S : Submodule R M := x ^ (k+1) • ⊤ with hS
    set T : Submodule R M := x ^ k • ⊤ with hT
    have hST : S ≤ T := by
      rw [hS, hT, pow_succ, mul_comm, mul_smul]
      intro m hm
      obtain ⟨n, hn, rfl⟩ := hm
      exact (x ^ k • ⊤ : Submodule R M).smul_mem x hn
    have hexact : Function.Exact (T.map S.mkQ).subtype (T.map S.mkQ).mkQ :=
      LinearMap.exact_subtype_mkQ (T.map S.mkQ)
    have hinj : Function.Injective (T.map S.mkQ).subtype := Subtype.coe_injective
    have hsub := associatedPrimes.subset_union_of_exact hinj hexact
    have hqmem : q ∈ associatedPrimes R (M ⧸ S) := hq
    rcases hsub hqmem with hcase | hcase
    · -- submodule case: T.map S.mkQ ≅ QuotSMulTop x M (multiplication by x^k, using regularity)
      let φ : M →ₗ[R] (M ⧸ S) := (S.mkQ).comp (x ^ k • LinearMap.id)
      have hφ : ∀ m, φ m = S.mkQ (x ^ k • m) := fun m => rfl
      have hxk : IsSMulRegular M (x ^ k) := hx.pow k
      have hrange : LinearMap.range φ = T.map S.mkQ := by
        apply le_antisymm
        · rintro _ ⟨m, rfl⟩
          rw [hφ]
          exact ⟨x ^ k • m, ⟨m, Submodule.mem_top, rfl⟩, rfl⟩
        · rintro _ ⟨t, ⟨m, -, rfl⟩, rfl⟩
          exact ⟨m, (hφ m).symm⟩
      have hker : LinearMap.ker φ = (x • ⊤ : Submodule R M) := by
        ext m
        rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        constructor
        · rintro ⟨n, -, hn⟩
          simp only [DistribSMul.toLinearMap_apply] at hn
          refine ⟨n, Submodule.mem_top, ?_⟩
          simp only [DistribSMul.toLinearMap_apply]
          apply hxk
          simp only []
          rw [smul_comm, ← mul_smul, ← pow_succ']
          exact hn
        · rintro ⟨n, -, rfl⟩
          refine ⟨n, Submodule.mem_top, ?_⟩
          simp only [DistribSMul.toLinearMap_apply]
          rw [pow_succ, mul_smul, smul_comm]
      let e1 : (M ⧸ (x • ⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ LinearMap.ker φ) :=
        Submodule.quotEquivOfEq _ _ hker.symm
      let e2 : (M ⧸ LinearMap.ker φ) ≃ₗ[R] LinearMap.range φ := φ.quotKerEquivRange
      let e3 : (LinearMap.range φ) ≃ₗ[R] (T.map S.mkQ) := LinearEquiv.ofEq _ _ hrange
      let e : QuotSMulTop x M ≃ₗ[R] (T.map S.mkQ) := e1 ≪≫ₗ e2 ≪≫ₗ e3
      exact (LinearEquiv.isAssociatedPrime_iff e).mpr hcase
    · -- quotient case: (M⧸S)/(T.map S.mkQ) ≅ M⧸T, then apply the induction hypothesis
      have e : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T :=
        Submodule.quotientQuotientEquivQuotient S T hST
      exact ih ((LinearEquiv.isAssociatedPrime_iff e).mp hcase)

open Pointwise in
private lemma exists_associatedPrime_lt_of_isSMulRegular
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : IsAssociatedPrime p M)
    {x : R} (hxmem : x ∈ IsLocalRing.maximalIdeal R) (hx : IsSMulRegular M x) :
    ∃ q : Ideal R, IsAssociatedPrime q (QuotSMulTop x M) ∧ p < q := by
  have : p.IsPrime := hp.isPrime
  -- Step 1: write `p = Ann(y)` for some `y ≠ 0` (`isAssociatedPrime_iff`).
  obtain ⟨hpp, y, hyeq⟩ := (isAssociatedPrime_iff).mp hp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hpp.ne_top
    rw [hyeq]; ext r; simp [Submodule.mem_colon_singleton]
  -- Step 2: `x` is `M`-regular and `y ≠ 0`, hence `x ∉ Ann(y) = p`.
  have hxnp : x ∉ p := by
    rw [hyeq, Submodule.mem_colon_singleton]
    intro hmem
    have : x • y = 0 := by simpa using hmem
    exact hy0 (hx (by simpa using this))
  -- Step 3: Krull's intersection theorem gives `k` with `y ∉ x^k • ⊤`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, y ∉ (x ^ k • ⊤ : Submodule R M) := by
    set I : Ideal R := Ideal.span {x} with hI
    have hIne : I ≠ ⊤ := by
      have hle : I ≤ IsLocalRing.maximalIdeal R := by
        rw [hI, Ideal.span_le]; simpa using hxmem
      intro hu
      rw [hu, top_le_iff] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
    have hbot : (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hIne
    have hnotin : y ∉ (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) := by
      rw [hbot]; simpa using hy0
    rw [Submodule.mem_iInf] at hnotin
    push Not at hnotin
    obtain ⟨k, hkk⟩ := hnotin
    refine ⟨k, ?_⟩
    have : (I ^ k • ⊤ : Submodule R M) = (x ^ k • ⊤ : Submodule R M) := by
      rw [hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    rwa [this] at hkk
  -- Step 4: the image `ȳ` of `y` in `N := M ⧸ x^k • ⊤` is nonzero.
  set ybar : (M ⧸ (x ^ k • ⊤ : Submodule R M)) := (Submodule.mkQ _) y with hybar
  have hybar0 : ybar ≠ 0 := by
    rw [hybar, Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hk
  -- Step 5: `exists_le_isAssociatedPrime_of_isNoetherianRing` yields `q ∈ Ass(N)`, `Ann(ȳ) ≤ q`.
  obtain ⟨q, hqass, hqle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R ybar hybar0
  have : q.IsPrime := hqass.isPrime
  -- Step 6: `r ∈ q` whenever `r • y ∈ x^k • ⊤`, since then `r • ȳ = 0`, i.e. `r ∈ Ann(ȳ) ≤ q`.
  have hmemq : ∀ r : R, r • y ∈ (x ^ k • ⊤ : Submodule R M) → r ∈ q := by
    intro r hr
    apply hqle
    rw [Submodule.mem_colon_singleton]
    have : r • ybar = (Submodule.mkQ _) (r • y) := by rw [hybar, map_smul]
    rw [this, Submodule.mkQ_apply, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hr
  -- `p ≤ q` since `Ann_M(y) ⊆ Ann_N(ȳ) ⊆ q`.
  have hpq : p ≤ q := by
    intro r hr
    rw [hyeq, Submodule.mem_colon_singleton] at hr
    refine hmemq r ?_
    rw [show r • y = 0 by simpa using hr]
    exact Submodule.zero_mem _
  -- Step 7: `x ∈ q` since `x^k • y ∈ x^k • ⊤`, so `x^k ∈ q` and `q` is prime.
  have hxq : x ∈ q :=
    hqass.isPrime.mem_of_pow_mem k
      (hmemq _ (Submodule.smul_mem_pointwise_smul y (x ^ k) ⊤ Submodule.mem_top))
  -- Step 8: `x ∈ q` but `x ∉ p` forces `p ≠ q`, hence `p < q`.
  have hplt : p < q := lt_of_le_of_ne hpq (by rintro rfl; exact hxnp hxq)
  -- Step 9 (Obligation 1): transfer `q ∈ Ass(M ⧸ x^k•⊤)` to `q ∈ Ass(M ⧸ x•⊤)`.
  exact ⟨q, associatedPrime_quotSMulTop_of_pow (R := R) (M := M) x k hx hqass, hplt⟩

/-- **Core combinatorial lemma.** For *every* `M`-regular
sequence `rs` with all entries in the maximal ideal and every associated prime `p ∈ Ass(M)`,
there is a strictly increasing chain of prime ideals of `R`, of length `rs.length`, whose head
is `p`. (Phrased as an `LTSeries (PrimeSpectrum R)` with head `⟨p, _⟩` and length `rs.length`.)

The proof is by induction on the list `rs`, with `M` and `p` universally quantified so the
induction hypothesis can be applied to the quotient module `M ⧸ x • ⊤` and a larger prime.
  * `rs = []`: the one-point series `⟨p, _⟩` has length `0`.
  * `rs = x :: rs'`: `isRegular_cons_iff` gives `x` `M`-regular and `rs'`
    `(QuotSMulTop x M)`-regular (entries still in `𝔪`). By
    `exists_associatedPrime_lt_of_isSMulRegular`, pick `q ∈ Ass(M ⧸ x•⊤)` with `p < q`. The IH
    for `M ⧸ x•⊤`, `q`, `rs'` gives a chain of length `rs'.length` with head `q`; prepend
    `p < q` (`LTSeries.cons`) to get a chain of length `rs'.length + 1 = (x::rs').length` with
    head `p`. -/
private lemma exists_ltSeries_primeSpectrum_of_isRegular
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : IsAssociatedPrime p M)
    {rs : List R} (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M rs) :
    ∃ s : LTSeries (PrimeSpectrum R),
      s.head = ⟨p, hp.isPrime⟩ ∧ s.length = rs.length := by
  induction rs generalizing M p with
  | nil =>
    refine ⟨RelSeries.singleton _ (⟨p, hp.isPrime⟩ : PrimeSpectrum R), ?_, ?_⟩
    · exact RelSeries.head_singleton _
    · rfl
  | cons x rs' ih =>
    obtain ⟨hx, hreg'⟩ := (RingTheory.Sequence.isRegular_cons_iff M x rs').mp hreg
    have hxmem : x ∈ IsLocalRing.maximalIdeal R := hmem x (List.mem_cons_self ..)
    obtain ⟨q, hq, hlt⟩ := exists_associatedPrime_lt_of_isSMulRegular hp hxmem hx
    have : Module.Finite R (QuotSMulTop x M) := inferInstance
    obtain ⟨s, hhead, hlen⟩ := ih hq
      (fun r hr => hmem r (List.mem_cons_of_mem _ hr)) hreg'
    refine ⟨s.cons ⟨p, hp.isPrime⟩ ?_, ?_, ?_⟩
    · rw [hhead]; exact hlt
    · exact RelSeries.head_cons _ _ _
    · rw [RelSeries.cons_length, hlen, List.length_cons]

private lemma depthM_le_ringKrullDim_quotient_of_associatedPrime
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (h : IsAssociatedPrime p M) :
    (depthM R M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have : p.IsPrime := h.isPrime
  -- It suffices to bound the depth (an ℕ∞ value) by `coheight p`, then identify
  -- `coheight p` with `ringKrullDim (R ⧸ p)`.
  rw [← coheight_eq_ringKrullDim_quotient ⟨p, h.isPrime⟩]
  -- Reduce the `WithBot ℕ∞` goal to the `ℕ∞` bound `depthM R M ≤ coheight ⟨p,_⟩`.
  have hbound : depthM R M ≤ Order.coheight (⟨p, h.isPrime⟩ : PrimeSpectrum R) := by
    -- Step 1: unfold the supremum and apply `iSup_le`.
    rw [depthM]
    refine iSup_le ?_
    intro rs
    refine iSup_le ?_
    rintro ⟨hmem, hreg⟩
    -- (★): each regular sequence `rs ⊆ 𝔪` has `rs.length ≤ coheight p`.
    -- Build a prime chain of length `rs.length` with head `p` (Lemma A), then use
    -- `Order.length_le_coheight`.
    obtain ⟨s, hhead, hlen⟩ :=
      exists_ltSeries_primeSpectrum_of_isRegular h hmem hreg
    have hle : (s.length : ℕ∞) ≤ Order.coheight (⟨p, h.isPrime⟩ : PrimeSpectrum R) := by
      have := Order.length_le_coheight (x := (⟨p, h.isPrime⟩ : PrimeSpectrum R)) (p := s)
        (le_of_eq hhead.symm)
      exact_mod_cast this
    rw [hlen] at hle
    exact_mod_cast hle
  -- Cast the `ℕ∞` bound up to `WithBot ℕ∞`.
  exact_mod_cast hbound

/-- The deep half of the lemma: for a Cohen–Macaulay finite module over a Noetherian local
ring, the depth — equivalently `dim (Supp M)` — is bounded above by `dim (R ⧸ p)` for every
associated prime `p`. This is the inequality `depth M ≤ dim (R ⧸ p)` (Stacks 10.72.9 / EGA 0
16.5.4), the content of the Auslander–Buchsbaum / depth–dimension estimate.

INFORMAL PROOF: by `hCM`, `Module.supportDim R M = (depthM R M : WithBot ℕ∞)`, so the goal
becomes `depthM R M ≤ dim (R/p)`, which is exactly
`depthM_le_ringKrullDim_quotient_of_associatedPrime`. The only step here is the `IsCM`
rewrite; the substance lives in that kernel lemma. -/
private lemma supportDim_le_ringKrullDim_quotient_of_isCM
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hCM : IsCM R M) {p : Ideal R} (h : IsAssociatedPrime p M) :
    Module.supportDim R M ≤ ringKrullDim (R ⧸ p) := by
  -- `IsCM R M` is the equation `(depthM R M : WithBot ℕ∞) = Module.supportDim R M`.
  rw [← hCM]
  exact depthM_le_ringKrullDim_quotient_of_associatedPrime h

/-- Stacks 02M5 / `lemma-CM-ass-minimal-support`. For a finite Cohen–Macaulay
module `M` over a Noetherian local ring `(R, 𝔪)`:
1. every associated prime `p` satisfies `dim(R/p) = dim(Supp(M))` and is a minimal
   prime of the support of `M`; and
2. `M` has no embedded associated primes. -/
@[ega "0 16.5.4", ega "IV 15.4.1" "partial", ega "IV 7.2.1.1" "more general"]
theorem CM_ass_minimal_support
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hCM : IsCM R M) :
    (∀ p ∈ associatedPrimes R M,
        ringKrullDim (R ⧸ p) = Module.supportDim R M ∧
        p ∈ (Module.annihilator R M).minimalPrimes)
    ∧ (∀ p, ¬ IsEmbeddedAssociatedPrime R M p) := by
  -- Part 1: dimension equality and minimality for every associated prime.
  have part1 : ∀ p ∈ associatedPrimes R M,
      ringKrullDim (R ⧸ p) = Module.supportDim R M ∧
      p ∈ (Module.annihilator R M).minimalPrimes := by
    intro p hp
    have hpa : IsAssociatedPrime p M := hp
    have : p.IsPrime := hpa.isPrime
    -- annihilator is contained in p
    have hAle := annihilator_le_of_isAssociatedPrime hpa
    -- both inequalities give the dimension equality
    have hle : ringKrullDim (R ⧸ p) ≤ Module.supportDim R M :=
      ringKrullDim_quotient_le_supportDim hAle
    have hge : Module.supportDim R M ≤ ringKrullDim (R ⧸ p) :=
      supportDim_le_ringKrullDim_quotient_of_isCM hCM hpa
    have hdim : ringKrullDim (R ⧸ p) = Module.supportDim R M := le_antisymm hle hge
    refine ⟨hdim, ?_⟩
    -- minimality: a minimal prime p₀ ≤ p exists; if p₀ < p the dimension would strictly drop.
    obtain ⟨p₀, hp₀min, hp₀le⟩ := Ideal.exists_minimalPrimes_le (J := p) hAle
    have hp₀prime : p₀.IsPrime := hp₀min.isPrime
    have : p₀ = p := by
      rcases eq_or_lt_of_le hp₀le with h | hlt
      · exact h
      · exfalso
        have : p₀.IsPrime := hp₀prime
        have hdrop : ringKrullDim (R ⧸ p) < ringKrullDim (R ⧸ p₀) :=
          ringKrullDim_quotient_strictAnti p₀ p hlt
        -- but dim(R/p₀) ≤ supportDim = dim(R/p), contradiction
        have hp₀dim : ringKrullDim (R ⧸ p₀) ≤ Module.supportDim R M :=
          ringKrullDim_quotient_le_supportDim hp₀min.1.2
        rw [hdim] at hdrop
        exact absurd hdrop (not_lt.mpr hp₀dim)
    rwa [this] at hp₀min
  refine ⟨part1, ?_⟩
  -- Part 2: no embedded associated primes, deduced from part 1.
  rintro p ⟨hp, q, hq, hqp⟩
  have hpmin := (part1 p hp).right
  have hqmin := (part1 q hq).right
  obtain ⟨⟨hpp, hpI⟩, hpminmin⟩ := hpmin
  obtain ⟨⟨hqp', hqI⟩, hqminmin⟩ := hqmin
  have hle := hpminmin ⟨hqp', hqI⟩ (le_of_lt hqp)
  exact absurd (le_antisymm hle (le_of_lt hqp)) (ne_of_gt hqp)
