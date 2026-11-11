module

public import StacksFrontier.RingTheory.Length.Additivity
public import StacksFrontier.RingTheory.Length.CompositionSeries

/-!
# Composition series and localization at a maximal ideal

The full statement of Stacks 00J3: for a maximal chain `0 = M_0 ⊂ … ⊂ M_n = M` of submodules
with successive quotients `M_{i+1}/M_i ≅ R/𝔪_i`, the number of indices `i` with `𝔪_i = 𝔪` is
`length_{R_𝔪}(M_𝔪)` for every maximal ideal `𝔪`, besides parts (1)–(3) proved in
`StacksFrontier.RingTheory.Length.CompositionSeries`. The count is deduced from Stacks 00L7
(`Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length`): every point of the
support of `M` is one of the maximal ideals `𝔪_i`, hence minimal in the support.
-/

@[expose] public section

/-! ### The full statement of Stacks 00J3 -/

/-- **Stacks 00J3**. Let `M` be an `R`-module and `0 = M_0 ⊂ M_1 ⊂ … ⊂ M_n = M` a maximal
chain of submodules with `M_i ≠ M_{i-1}`. Then

1. `n = length_R(M)`;
2. each successive quotient `M_{i+1}/M_i` is simple;
3. each successive quotient is isomorphic to `R/𝔪_i` for some maximal ideal `𝔪_i`;
4. for any choice of such maximal ideals `𝔪_i` (part (3)) and every maximal ideal `𝔪` of `R`,
   `#{i | 𝔪_i = 𝔪} = length_{R_𝔪}(M_𝔪)`.

The source assumes `M` has finite length; this is not needed as a hypothesis, since a finite
maximal chain forces it (and part (1) records it). The length in part (1) is `Module.length`
in `ℕ∞`, and `M_𝔪`, `R_𝔪` are `LocalizedModule 𝔪.primeCompl M` and
`Localization.AtPrime 𝔪`. In part (4) the ideal `𝔪_i` is in fact determined by `M_{i+1}/M_i`
(it is its annihilator), so the count does not depend on the choice. -/
@[stacks 00J3]
theorem length_eq_and_subQuot_isSimpleModule_and_exists_quot_maximal_and_ncard_eq_length
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (M' : Fin (n + 1) → Submodule R M) (hchain : IsMaximalChainPrime M') :
    (n : ℕ∞) = Module.length R M ∧
      (∀ i : Fin n, IsSimpleModule R (subQuot M' i)) ∧
      (∀ i : Fin n, ∃ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal),
        Nonempty (subQuot M' i ≃ₗ[R] R ⧸ 𝔪)) ∧
      ∀ 𝔪s : Fin n → Ideal R,
        (∀ i : Fin n, (𝔪s i).IsMaximal ∧ Nonempty (subQuot M' i ≃ₗ[R] R ⧸ 𝔪s i)) →
        ∀ (𝔪 : Ideal R) [𝔪.IsMaximal],
          ({i | 𝔪s i = 𝔪}.ncard : ℕ∞) =
            Module.length (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) := by
  obtain ⟨h1, h2, h3⟩ := length_eq_and_subQuot_isSimpleModule_and_exists_quot_maximal M' hchain
  refine ⟨h1, h2, h3, fun 𝔪s h𝔪s 𝔪 _ => ?_⟩
  -- Part (4): the chain is a filtration with subquotients `R ⧸ 𝔪_i`, so Stacks 00L7 counts the
  -- `𝔪_i` equal to any minimal point of the support; every point of the support is some `𝔪_i`.
  let p : Fin n → PrimeSpectrum R := fun i => ⟨𝔪s i, (h𝔪s i).1.isPrime⟩
  obtain ⟨hmin, hcount⟩ := Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length
    M' p (fun i => (hchain.strictMono (Fin.castSucc_lt_succ (i := i))).le)
    (fun i => (h𝔪s i).2) hchain.bot hchain.top
  have hfin : IsFiniteLength R M := Module.length_ne_top_iff.mp (h1 ▸ ENat.natCast_ne_top n)
  have : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  -- Every element of the range of `p` is maximal, hence minimal in the range.
  have hminRange : ∀ i, Minimal (· ∈ Set.range p) (p i) := fun i =>
    ⟨Set.mem_range_self i, fun y ⟨j, hj⟩ hy => by
      subst hj
      exact (PrimeSpectrum.ext ((h𝔪s j).1.eq_of_le (h𝔪s i).1.ne_top hy) : p j = p i).ge⟩
  have hmemSupp : ∀ i, p i ∈ Module.support R M := fun i => by
    have : p i ∈ {q | Minimal (· ∈ Module.support R M) q} := hmin ▸ hminRange i
    exact this.1
  -- Every point of the support is one of the `𝔪_i`.
  have hsupp : ∀ q ∈ Module.support R M, ∃ i, p i = q := fun q hq => by
    obtain ⟨r, hrm, hrq⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hq)
    let r' : PrimeSpectrum R := ⟨r, hrm.isPrime⟩
    have hr' : Minimal (· ∈ Module.support R M) r' :=
      ⟨Module.mem_support_iff_of_finite.mpr hrm.1.2, fun y hy hyr =>
        hrm.2 ⟨y.2, Module.mem_support_iff_of_finite.mp hy⟩ hyr⟩
    have : r' ∈ {q | Minimal (· ∈ Set.range p) q} := hmin ▸ hr'
    obtain ⟨i, hi⟩ := this.1
    refine ⟨i, PrimeSpectrum.ext ?_⟩
    have hir : 𝔪s i = r := congrArg PrimeSpectrum.asIdeal hi
    exact (h𝔪s i).1.eq_of_le q.2.ne_top (hir ▸ hrq)
  let q : PrimeSpectrum R := ⟨𝔪, inferInstance⟩
  have hset : {i | 𝔪s i = 𝔪} = {i | p i = q} := by
    ext i
    simp [p, q, PrimeSpectrum.ext_iff]
  by_cases hq : q ∈ Module.support R M
  · have hqmin : Minimal (· ∈ Module.support R M) q := ⟨hq, fun y hy hyq => by
      obtain ⟨j, rfl⟩ := hsupp y hy
      exact (PrimeSpectrum.ext ((h𝔪s j).1.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hyq) :
        p j = q).ge⟩
    rw [hset]
    exact hcount q hqmin
  · have : Subsingleton (LocalizedModule 𝔪.primeCompl M) := Module.notMem_support_iff.mp hq
    rw [Module.length_eq_zero, hset]
    have : {i | p i = q} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hq (h ▸ hmemSupp i)
    simp [this]
