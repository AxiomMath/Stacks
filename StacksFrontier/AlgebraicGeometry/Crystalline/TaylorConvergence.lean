module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs

/-!
# The convergence of the Taylor series of [Stacks, Tag 07JH]

For two divided power maps `f, g : D → B` into the section ring of an object of `Cris(X/S)`,
agreeing modulo the divided power ideal `J_B`, and `ξ_i = f(x_i) - g(x_i) ∈ J_B`, the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] uses the Taylor comparison

`c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`,  `m ⊗ 1 ↦ ∑_K θ_K(m) ⊗ ∏_i ξ_i^{[k_i]}`.

This file proves that the Taylor series `∑_K ξ^{[K]} ⊗ θ_K(m)` has only finitely many nonzero
terms when `p` is nilpotent in `B` and the coordinate operators satisfy the quasi-nilpotence
condition of [Stacks, Tag 07JE], so that it converges in the `p`-adic topology of `B ⊗_D M`.

## Main definitions

* `Crystalline.pPowSmul`: the submodule `p^n M` of a `D`-module.
* `Crystalline.HasTaylorSum`: the Taylor series at `m` converges to `t` in the `p`-adic topology
  of `B ⊗_D M`.

## Main results

* `Crystalline.exists_hasTaylorSum`,
  `Crystalline.exists_hasTaylorSum_of_isTopologicallyQuasiNilpotent`: the Taylor series converges.
* `Crystalline.finite_thetaPow_notMem_pPowSmul`: only finitely many composite coordinate operators
  take a given `m` outside `p^n M`.
* `Crystalline.finite_iterate_notMem_pPowSmul`: quasi-nilpotence modulo `p` of an additive
  operator implies quasi-nilpotence modulo every power of `p`.
* `Crystalline.IsThetaMonomialFamily.add`: `θ_{K + L} = θ_L ∘ θ_K`.
* `Crystalline.IsThetaMonomialFamily.comm`: the operators `θ_i` commute.
* `Crystalline.taylorTerm_eq_zero_of_mem_pPowSmul`: a term of the series vanishes as soon as
  `θ_K m ∈ p^N M`, where `p^N = 0` in `B`.
* `Crystalline.hasTaylorSum_firstOrder`: the series truncated to total degree `≤ 1` converges to
  the first-order comparison `1 ⊗ m + ∑_i ξ_i ⊗ θ_i(m)`.
* `Crystalline.hasTaylorComparison_of_linearTaylorSum`: `Crystalline.HasTaylorComparison` holds
  when the Taylor sum is `D`-linear in `m`.
* `Crystalline.taylorSum_smul_eq_of_isTaylorComparison`: conversely, a Taylor comparison forces
  the Taylor sum to be `D`-linear in `m`.

## Implementation notes

`Crystalline.HasTaylorSum` is a definition rather than an abbreviation of the `HasSum` statement so
that the `p`-adic topology is fixed in one place. It is definitionally the body of
`Crystalline.IsTaylorComparison`, so `Crystalline.isTaylorComparison_iff_hasTaylorSum` is
`Iff.rfl`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/


@[expose] public section

open scoped TensorProduct

universe u v uI w

namespace Crystalline

/-! ### The composite coordinate operators `θ_K` -/

section ThetaCalculus

variable {M : Type w} {ι : Type uI} {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- The iterate of an additive map is additive. -/
theorem iterate_map_add [AddCommGroup M] {f : M → M} (hf : ∀ x y, f (x + y) = f x + f y)
    (b : ℕ) (x y : M) : f^[b] (x + y) = f^[b] x + f^[b] y := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, hf]

namespace IsThetaMonomialFamily

/-- The composite coordinate operator at the empty multi-index is the identity. -/
theorem apply_zero (h : IsThetaMonomialFamily M theta thetaPow) : thetaPow 0 = id := h.1

/-- Adding one to the `i`-th entry of a multi-index applies one more `θ_i`. -/
theorem succ (h : IsThetaMonomialFamily M theta thetaPow) (i : ι) (K : ι →₀ ℕ) :
    thetaPow (K + Finsupp.single i 1) = theta i ∘ thetaPow K := h.2 i K

/-- Raising the `i`-th entry of a multi-index by `b` applies `θ_i` another `b` times. -/
theorem add_single (h : IsThetaMonomialFamily M theta thetaPow) (K : ι →₀ ℕ) (i : ι) (b : ℕ) :
    thetaPow (K + Finsupp.single i b) = (theta i)^[b] ∘ thetaPow K := by
  induction b with
  | zero => rw [Finsupp.single_zero, add_zero, Function.iterate_zero, Function.id_comp]
  | succ b ih =>
      have hK : K + Finsupp.single i (b + 1) = K + Finsupp.single i b + Finsupp.single i 1 := by
        rw [add_assoc, ← Finsupp.single_add]
      rw [hK, h.succ, ih, Function.iterate_succ']
      rfl

/-- The composite operator at a one-point multi-index is an iterate of one `θ_i`. -/
theorem single (h : IsThetaMonomialFamily M theta thetaPow) (i : ι) (b : ℕ) :
    thetaPow (Finsupp.single i b) = (theta i)^[b] := by
  have hz := h.add_single 0 i b
  rw [zero_add, h.apply_zero, Function.comp_id] at hz
  exact hz

/-- The composite operators compose along addition of multi-indices: `θ_{K + L} = θ_L ∘ θ_K`. -/
theorem add (h : IsThetaMonomialFamily M theta thetaPow) (K L : ι →₀ ℕ) :
    thetaPow (K + L) = thetaPow L ∘ thetaPow K := by
  classical
  induction L using Finsupp.induction with
  | zero => rw [add_zero, h.apply_zero, Function.id_comp]
  | single_add a b L _ _ ih =>
      have h1 : K + (Finsupp.single a b + L) = K + L + Finsupp.single a b := by abel
      have h2 : Finsupp.single a b + L = L + Finsupp.single a b := by abel
      rw [h1, h.add_single, ih, h2, h.add_single]
      rfl

/-- The coordinate operators `θ_i` of a monomial family commute. -/
theorem comm (h : IsThetaMonomialFamily M theta thetaPow) (i j : ι) :
    theta i ∘ theta j = theta j ∘ theta i := by
  have hij := h.add (Finsupp.single j 1) (Finsupp.single i 1)
  have hji := h.add (Finsupp.single i 1) (Finsupp.single j 1)
  rw [h.single, h.single] at hij hji
  rw [add_comm] at hji
  rw [Function.iterate_one, Function.iterate_one] at hij hji
  rw [← hij, hji]

/-- The composite coordinate operators are additive when the `θ_i` are. -/
theorem map_add [AddCommGroup M] (h : IsThetaMonomialFamily M theta thetaPow)
    (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y) (K : ι →₀ ℕ)
    (x y : M) : thetaPow K (x + y) = thetaPow K x + thetaPow K y := by
  classical
  induction K using Finsupp.induction with
  | zero => rw [h.apply_zero]; rfl
  | single_add a b K _ _ ih =>
      have h2 : Finsupp.single a b + K = K + Finsupp.single a b := by abel
      rw [h2, h.add_single]
      show (theta a)^[b] (thetaPow K (x + y)) = _
      rw [ih, iterate_map_add (hadd a)]
      rfl

end IsThetaMonomialFamily

end ThetaCalculus

/-! ### The submodules `p^n M` -/

section PPow

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type w) [AddCommGroup M] [Module D M]

/-- The submodule `p^n M = (p)^n M` of a `D`-module `M`, for the `p`-adic ideal `(p)` of `D`. -/
def pPowSmul (n : ℕ) : Submodule D M :=
  DividedPowers.pAdicIdeal (A := D) p ^ n • (⊤ : Submodule D M)

/-- At `n = 0` the submodule `p^n M` is all of `M`. -/
theorem pPowSmul_zero : pPowSmul p D M 0 = ⊤ := by
  rw [pPowSmul, pow_zero, Ideal.one_eq_top, Submodule.top_smul]

/-- At `n = 1` the submodule `p^n M` is the submodule `p M` of [Stacks, Tag 07JE]. -/
theorem pPowSmul_one : pPowSmul p D M 1 = pSmul p D M := by
  rw [pPowSmul, pow_one]

/-- An element lies in `p^n M` if and only if it is `p^n • y` for some `y : M`. -/
theorem mem_pPowSmul_iff {n : ℕ} {x : M} :
    x ∈ pPowSmul p D M n ↔ ∃ y : M, ((p : D) ^ n) • y = x := by
  rw [pPowSmul, DividedPowers.pAdicIdeal, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]
  refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists x _ _).mp hx
    exact ⟨y, hy⟩
  · exact (Submodule.mem_smul_pointwise_iff_exists x _ _).mpr ⟨y, trivial, hy⟩

/-- An additive map `M → M` commutes with scalar multiplication by `p ^ n`. -/
private theorem map_pow_smul_of_add {f : M → M} (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ)
    (y : M) : f (((p : D) ^ n) • y) = ((p : D) ^ n) • f y := by
  have hcast : ((p : D) ^ n) = ((p ^ n : ℕ) : D) := by push_cast; ring
  rw [hcast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  exact (AddMonoidHom.mk' f hf).map_nsmul (p ^ n) y

/-- An additive map `M → M` carries `p^n M` into itself. -/
theorem map_mem_pPowSmul {f : M → M} (hf : ∀ x y, f (x + y) = f x + f y) {n : ℕ} {x : M}
    (hx : x ∈ pPowSmul p D M n) : f x ∈ pPowSmul p D M n := by
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p D M).mp hx
  exact (mem_pPowSmul_iff p D M).mpr ⟨f y, by rw [← map_pow_smul_of_add p D M hf, hy]⟩

/-- If `p^N = 0` in `D` then `p^N M = 0`. -/
theorem pPowSmul_eq_bot_of_pow_eq_zero {N : ℕ} (hp : ((p : D) ^ N) = 0) :
    pPowSmul p D M N = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p D M).mp hx
  rw [← hy, hp, zero_smul]

/-- Multiplying an element of `p^n M` by `p` lands in `p^{n+1} M`. -/
theorem smul_mem_pPowSmul_succ {n : ℕ} {x : M} (hx : x ∈ pPowSmul p D M n) :
    (p : D) • x ∈ pPowSmul p D M (n + 1) := by
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p D M).mp hx
  refine (mem_pPowSmul_iff p D M).mpr ⟨y, ?_⟩
  rw [← hy, pow_succ, mul_comm, mul_smul]

end PPow

/-! ### Quasi-nilpotence modulo every power of `p` -/

section QuasiNilpotence

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type w) [AddCommGroup M] [Module D M]

/-- If only finitely many `k` fail `P`, then `P k` holds for all large enough `k`. -/
private theorem exists_forall_le_of_finite_not {P : ℕ → Prop} (h : {k : ℕ | ¬ P k}.Finite) :
    ∃ b : ℕ, ∀ k, b ≤ k → P k := by
  obtain ⟨b, hb⟩ := h.bddAbove
  exact ⟨b + 1, fun k hk ↦ by_contra fun hc ↦ absurd (hb hc) (by omega)⟩

/-- Quasi-nilpotence modulo `p` implies quasi-nilpotence modulo every power of `p`: if an
additive operator `f` has, for every `m`, only finitely many iterates `f^k m` outside `p M`, then
for every `m` and every `n` only finitely many iterates lie outside `p^n M`. -/
theorem finite_iterate_notMem_pPowSmul {f : M → M} (hf : ∀ x y, f (x + y) = f x + f y)
    (hqn : ∀ m : M, {k : ℕ | k ≠ 0 ∧ f^[k] m ∉ pSmul p D M}.Finite) (n : ℕ) (m : M) :
    {k : ℕ | f^[k] m ∉ pPowSmul p D M n}.Finite := by
  induction n generalizing m with
  | zero =>
      have hempty : {k : ℕ | f^[k] m ∉ pPowSmul p D M 0} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun k hk ↦ hk ?_
        rw [pPowSmul_zero]
        exact Submodule.mem_top
      rw [hempty]
      exact Set.finite_empty
  | succ n ih =>
      obtain ⟨b, hb⟩ := exists_forall_le_of_finite_not
        (P := fun k ↦ k ≠ 0 → f^[k] m ∈ pSmul p D M) (by simpa [not_imp] using hqn m)
      have hmem : f^[b + 1] m ∈ pSmul p D M := hb (b + 1) (by omega) (Nat.succ_ne_zero b)
      rw [← pPowSmul_one] at hmem
      obtain ⟨m₁, hm₁⟩ := (mem_pPowSmul_iff p D M).mp hmem
      rw [pow_one] at hm₁
      obtain ⟨b₂, hb₂⟩ := exists_forall_le_of_finite_not (P := fun k ↦ f^[k] m₁ ∈ pPowSmul p D M n)
        (ih m₁)
      refine Set.Finite.subset (Set.finite_Iic (b + 1 + b₂)) fun k hk ↦ ?_
      by_contra hlt
      rw [Set.mem_Iic] at hlt
      have hk' : k = (k - (b + 1)) + (b + 1) := by omega
      refine hk ?_
      have hcomm := map_pow_smul_of_add p D M (iterate_map_add hf (k - (b + 1))) 1 m₁
      rw [pow_one] at hcomm
      rw [hk', Function.iterate_add_apply, ← hm₁, hcomm]
      exact smul_mem_pPowSmul_succ p D M (hb₂ _ (by omega))

variable {ι : Type uI} {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- If only finitely many pairs `(i, k)` with `k ≠ 0` have `θ_i^k m ∉ p M`, then for each index
`i` only finitely many `k ≠ 0` have `θ_i^k m ∉ p M`. -/
theorem finite_iterate_notMem_pSmul_of_finite_prod
    (h : ∀ m : M, {q : ι × ℕ | q.2 ≠ 0 ∧ (theta q.1)^[q.2] m ∉ pSmul p D M}.Finite) (i : ι)
    (m : M) : {k : ℕ | k ≠ 0 ∧ (theta i)^[k] m ∉ pSmul p D M}.Finite := by
  refine Set.Finite.of_finite_image (f := fun k : ℕ ↦ ((i, k) : ι × ℕ)) ?_ ?_
  · refine Set.Finite.subset (h m) ?_
    rintro q ⟨k, hk, rfl⟩
    exact hk
  · exact fun k _ k' _ hkk' ↦ (Prod.mk.injEq _ _ _ _ ▸ hkk').2

/-- If `θ_K m` lies in `p^n M` then so does `θ_L m` for every multi-index `L ≥ K`. -/
theorem thetaPow_mem_pPowSmul_of_le (hfam : IsThetaMonomialFamily M theta thetaPow)
    (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y) {n : ℕ} {m : M}
    {K L : ι →₀ ℕ} (hKL : K ≤ L) (hK : thetaPow K m ∈ pPowSmul p D M n) :
    thetaPow L m ∈ pPowSmul p D M n := by
  obtain ⟨N, rfl⟩ := exists_add_of_le hKL
  rw [hfam.add K N]
  exact map_mem_pPowSmul p D M (hfam.map_add hadd N) hK

/-- Only finitely many composite coordinate operators take `m` outside `p^n M`, given the
quasi-nilpotence condition `hqn` of [Stacks, Tag 07JE] in each variable and the finiteness `hsupp`
of the set of indices `i` with `θ_i m ∉ p^n M`. -/
theorem finite_thetaPow_notMem_pPowSmul (hfam : IsThetaMonomialFamily M theta thetaPow)
    (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hqn : ∀ (i : ι) (m : M), {k : ℕ | k ≠ 0 ∧ (theta i)^[k] m ∉ pSmul p D M}.Finite) {n : ℕ}
    {m : M} (hsupp : {i : ι | theta i m ∉ pPowSmul p D M n}.Finite) :
    {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p D M n}.Finite := by
  classical
  have hmemFinset : ∀ i : ι, i ∈ hsupp.toFinset ↔ theta i m ∉ pPowSmul p D M n :=
    fun i ↦ Set.Finite.mem_toFinset hsupp
  have hbound : ∀ i : ι, ∃ b : ℕ, ∀ k : ℕ, b < k → (theta i)^[k] m ∈ pPowSmul p D M n := by
    intro i
    obtain ⟨b, hb⟩ := exists_forall_le_of_finite_not
      (finite_iterate_notMem_pPowSmul p D M (hadd i) (hqn i) n m)
    exact ⟨b, fun k hk ↦ hb k hk.le⟩
  choose bnd hbnd using hbound
  refine Set.Finite.subset
    (Finset.finite_toSet (Finset.Iic (Finsupp.indicator hsupp.toFinset (fun i _ ↦ bnd i))))
    fun K hK ↦ ?_
  rw [Finset.mem_coe, Finset.mem_Iic]
  refine Finsupp.le_def.mpr fun i ↦ ?_
  by_cases hi : i ∈ hsupp.toFinset
  · rw [Finsupp.indicator_of_mem hi]
    by_contra hlt
    refine hK (thetaPow_mem_pPowSmul_of_le p D M hfam hadd
      (Finsupp.single_le_iff.mpr (le_refl (K i))) ?_)
    rw [hfam.single]
    exact hbnd i (K i) (by omega)
  · rw [Finsupp.indicator_of_notMem hi, Nat.le_zero]
    by_contra hne
    refine hK (thetaPow_mem_pPowSmul_of_le p D M hfam hadd
      (Finsupp.single_le_iff.mpr (show 1 ≤ K i by omega)) ?_)
    rw [hfam.single, Function.iterate_one]
    exact not_not.mp (fun hc ↦ hi ((hmemFinset i).mpr hc))

end QuasiNilpotence

/-! ### The Taylor series of the proof of [Stacks, Tag 07JH] -/

section Taylor

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} {theta : ι → (M → M)} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- The Taylor series `∑_K ξ^{[K]} ⊗ θ_K(m)` of divided power monomials against the composite
coordinate operators converges to `t` in the `p`-adic topology of `B ⊗_D M`. -/
def HasTaylorSum (xi : ι → (B : Type u)) (m : M) (t : (B : Type u) ⊗[(D : Type u)] M) : Prop :=
  letI := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := (B : Type u)) p)
    ((B : Type u) ⊗[(D : Type u)] M)
  HasSum (fun K : ι →₀ ℕ ↦ taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m) t

/-- A `B`-linear map `c` is a Taylor comparison if and only if each value `c (1 ⊗ m)` is a sum
of the Taylor series at `m`. -/
theorem isTaylorComparison_iff_hasTaylorSum (xi : ι → (B : Type u))
    (c : ((B : Type u) ⊗[(D : Type u)] M) →ₗ[(B : Type u)] ((B : Type u) ⊗[(D : Type u)] M)) :
    IsTaylorComparison p D B M thetaPow xi c ↔
      ∀ m : M, HasTaylorSum p D B M thetaPow xi m (c ((1 : (B : Type u)) ⊗ₜ[(D : Type u)] m)) :=
  Iff.rfl

/-- If `p^N = 0` in `B` and `θ_K m ∈ p^N M`, then the Taylor term `ξ^{[K]} ⊗ θ_K(m)`
vanishes. -/
theorem taylorTerm_eq_zero_of_mem_pPowSmul {N : ℕ} (hpB : ((p : (B : Type u))) ^ N = 0)
    (xi : ι → (B : Type u)) {K : ι →₀ ℕ} {m : M}
    (hK : thetaPow K m ∈ pPowSmul p (D : Type u) M N) :
    taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m = 0 := by
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p (D : Type u) M).mp hK
  have hzero : ((p : (D : Type u)) ^ N) • taylorMonomial B xi K = 0 := by
    rw [Algebra.smul_def, map_pow, map_natCast, hpB, zero_mul]
  rw [← hy, TensorProduct.tmul_smul, TensorProduct.smul_tmul', hzero,
    TensorProduct.zero_tmul]

/-- A Taylor series whose terms vanish outside a finite set `s` converges to the sum of its terms
over `s`. -/
theorem hasTaylorSum_of_eq_zero (xi : ι → (B : Type u)) (m : M) (s : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m = 0) :
    HasTaylorSum p D B M thetaPow xi m
      (∑ K ∈ s, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m) := by
  let := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := (B : Type u)) p)
    ((B : Type u) ⊗[(D : Type u)] M)
  exact hasSum_sum_of_ne_finset_zero hs

variable {thetaPow}

/-- The Taylor series of [Stacks, Tag 07JH] converges, given additive coordinate operators forming
a monomial family, the quasi-nilpotence condition `hqn` of [Stacks, Tag 07JE] in each variable,
nilpotence of `p` in `B`, and the finiteness `hsupp`, at each level `n`, of the set of indices `i`
with `θ_i m ∉ p^n M`. -/
theorem exists_hasTaylorSum (hfam : IsThetaMonomialFamily M theta thetaPow)
    (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hqn : ∀ (i : ι) (m : M), {k : ℕ | k ≠ 0 ∧ (theta i)^[k] m ∉ pSmul p (D : Type u) M}.Finite)
    (hpB : IsNilpotent ((p : (B : Type u)))) (xi : ι → (B : Type u)) (m : M)
    (hsupp : ∀ n : ℕ, {i : ι | theta i m ∉ pPowSmul p (D : Type u) M n}.Finite) :
    ∃ t : (B : Type u) ⊗[(D : Type u)] M, HasTaylorSum p D B M thetaPow xi m t := by
  classical
  obtain ⟨N, hN⟩ := hpB
  have hfin := finite_thetaPow_notMem_pPowSmul p (D : Type u) M hfam hadd hqn (hsupp N)
  refine ⟨_, hasTaylorSum_of_eq_zero p D B M thetaPow xi m hfin.toFinset fun K hK ↦ ?_⟩
  refine taylorTerm_eq_zero_of_mem_pPowSmul p D B M thetaPow hN xi ?_
  exact not_not.mp fun hc ↦ hK (hfin.mem_toFinset.mpr hc)

/-! ### The series in total degree `≤ 1` -/

/-- The divided power monomial at the one-point multi-index `single i 1` is `ξ_i`. -/
theorem taylorMonomial_single_one (xi : ι → (B : Type u)) (i : ι) (hxi : xi i ∈ B.ideal) :
    taylorMonomial B xi (Finsupp.single i 1) = xi i := by
  rw [taylorMonomial, Finsupp.support_single_ne_zero i one_ne_zero, Finset.prod_singleton,
    Finsupp.single_eq_same, B.dividedPowers.dpow_one hxi]

/-- If the composite coordinate operators vanish at `m` outside the empty multi-index and the
one-point multi-indices of a finite set `s` of indices, then the Taylor series at `m` converges to

`1 ⊗ m + ∑_{i ∈ s} ξ_i ⊗ θ_i(m)`. -/
theorem hasTaylorSum_firstOrder (hfam : IsThetaMonomialFamily M theta thetaPow)
    (xi : ι → (B : Type u)) (hxi : ∀ i, xi i ∈ B.ideal) (m : M) (s : Finset ι)
    (hvanish : ∀ K : ι →₀ ℕ, K ≠ 0 → (∀ i ∈ s, K ≠ Finsupp.single i 1) → thetaPow K m = 0) :
    HasTaylorSum p D B M thetaPow xi m
      ((1 : (B : Type u)) ⊗ₜ[(D : Type u)] m +
        ∑ i ∈ s, xi i ⊗ₜ[(D : Type u)] theta i m) := by
  classical
  have hinj : Set.InjOn (fun i : ι ↦ (Finsupp.single i 1 : ι →₀ ℕ)) s := fun i _ j _ hij ↦
    Finsupp.single_left_injective one_ne_zero hij
  have hterm : ∀ i : ι, taylorMonomial B xi (Finsupp.single i 1) ⊗ₜ[(D : Type u)]
      thetaPow (Finsupp.single i 1) m = xi i ⊗ₜ[(D : Type u)] theta i m := by
    intro i
    rw [taylorMonomial_single_one B xi i (hxi i), hfam.single, Function.iterate_one]
  have hsum : ∑ K ∈ insert (0 : ι →₀ ℕ) (s.image fun i ↦ (Finsupp.single i 1 : ι →₀ ℕ)),
      taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m =
        (1 : (B : Type u)) ⊗ₜ[(D : Type u)] m + ∑ i ∈ s, xi i ⊗ₜ[(D : Type u)] theta i m := by
    rw [Finset.sum_insert (by simp),
      Finset.sum_image fun i hi j hj hij ↦ hinj hi hj hij]
    congr 1
    · rw [taylorMonomial_zero, hfam.apply_zero, id_eq]
    · exact Finset.sum_congr rfl fun i _ ↦ hterm i
  rw [← hsum]
  refine hasTaylorSum_of_eq_zero p D B M thetaPow xi m _ fun K hK ↦ ?_
  rw [Finset.mem_insert, Finset.mem_image] at hK
  rw [hvanish K (fun h ↦ hK (Or.inl h)) fun i hi h ↦ hK (Or.inr ⟨i, hi, h.symm⟩),
    TensorProduct.tmul_zero]

/-! ### What is left of `HasTaylorComparison` once the series converges -/

/-- If a `D`-linear map `T : M →ₗ[D] B ⊗_D M` sends each `m` to a sum of its Taylor series, then
its `B`-linear extension `T.liftBaseChange B` is a Taylor comparison. -/
theorem isTaylorComparison_liftBaseChange (xi : ι → (B : Type u))
    (T : M →ₗ[(D : Type u)] ((B : Type u) ⊗[(D : Type u)] M))
    (hT : ∀ m : M, HasTaylorSum p D B M thetaPow xi m (T m)) :
    IsTaylorComparison p D B M thetaPow xi (T.liftBaseChange (B : Type u)) := by
  intro m
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  exact hT m

/-- `Crystalline.HasTaylorComparison` holds if, for every family `ξ` in the divided power ideal,
some `D`-linear map `M →ₗ[D] B ⊗_D M` sends each `m` to a sum of its Taylor series. -/
theorem hasTaylorComparison_of_linearTaylorSum
    (hT : ∀ xi : ι → (B : Type u), (∀ i, xi i ∈ B.ideal) →
      ∃ T : M →ₗ[(D : Type u)] ((B : Type u) ⊗[(D : Type u)] M),
        ∀ m : M, HasTaylorSum p D B M thetaPow xi m (T m)) :
    HasTaylorComparison p D B M thetaPow := by
  intro xi hxi
  obtain ⟨T, hTxi⟩ := hT xi hxi
  exact ⟨T.liftBaseChange (B : Type u), isTaylorComparison_liftBaseChange p D B M xi T hTxi⟩

/-- For a Taylor comparison `c`, the Taylor series at `a • m` converges to
`a • c (1 ⊗ m)`. -/
theorem hasTaylorSum_smul_of_isTaylorComparison (xi : ι → (B : Type u))
    (c : ((B : Type u) ⊗[(D : Type u)] M) →ₗ[(B : Type u)] ((B : Type u) ⊗[(D : Type u)] M))
    (hc : IsTaylorComparison p D B M thetaPow xi c) (a : (D : Type u)) (m : M) :
    HasTaylorSum p D B M thetaPow xi (a • m)
      (a • c ((1 : (B : Type u)) ⊗ₜ[(D : Type u)] m)) := by
  have hsmul : ∀ (b : (D : Type u)) (z : (B : Type u) ⊗[(D : Type u)] M), c (b • z) = b • c z := by
    intro b z
    rw [← algebraMap_smul (B : Type u) b z, map_smul, algebraMap_smul]
  have h := hc (a • m)
  rwa [TensorProduct.tmul_smul, hsmul] at h

/-- If the sum of a Taylor series is unique, then a Taylor comparison forces

`∑_K ξ^{[K]} ⊗ θ_K(a m) = a ∑_K ξ^{[K]} ⊗ θ_K(m)`    for every `a ∈ D` and `m ∈ M`. -/
theorem taylorSum_smul_eq_of_isTaylorComparison (xi : ι → (B : Type u))
    (c : ((B : Type u) ⊗[(D : Type u)] M) →ₗ[(B : Type u)] ((B : Type u) ⊗[(D : Type u)] M))
    (hc : IsTaylorComparison p D B M thetaPow xi c)
    (huniq : ∀ (m' : M) (t t' : (B : Type u) ⊗[(D : Type u)] M),
      HasTaylorSum p D B M thetaPow xi m' t → HasTaylorSum p D B M thetaPow xi m' t' → t = t')
    (a : (D : Type u)) (m : M) (t ta : (B : Type u) ⊗[(D : Type u)] M)
    (ht : HasTaylorSum p D B M thetaPow xi m t)
    (hta : HasTaylorSum p D B M thetaPow xi (a • m) ta) : ta = a • t := by
  rw [huniq m t _ ht (hc m),
    huniq (a • m) ta _ hta (hasTaylorSum_smul_of_isTaylorComparison p D B M xi c hc a m)]

end Taylor

/-! ### The convergence read off a pair `(M, ∇)` -/

section FromPair

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (Omega : Type v) [AddCommGroup Omega]
  [Module (D : Type u) Omega] (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} (dx : ι → Omega) {dd : D.carrier → Omega}
  (nabla : CompletedConnection p (D : Type u) Omega dd M)
  {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- The Taylor series of [Stacks, Tag 07JH] converges for a monomial family of additive
coordinate operators of a connection `∇` that is topologically quasi-nilpotent in the sense of
[Stacks, Tag 07JE], given nilpotence of `p` in `B` and the finiteness `hsupp`. -/
theorem exists_hasTaylorSum_of_isTopologicallyQuasiNilpotent
    (hfam : IsThetaMonomialFamily M theta thetaPow)
    (hadd : ∀ (i : ι) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hco : IsCoordinateExpansion p (D : Type u) Omega dx nabla theta)
    (hqn : IsTopologicallyQuasiNilpotent p (D : Type u) Omega dx nabla)
    (hpB : IsNilpotent ((p : (B : Type u)))) (xi : ι → (B : Type u)) (m : M)
    (hsupp : ∀ n : ℕ, {i : ι | theta i m ∉ pPowSmul p (D : Type u) M n}.Finite) :
    ∃ t : (B : Type u) ⊗[(D : Type u)] M, HasTaylorSum p D B M thetaPow xi m t :=
  exists_hasTaylorSum p D B M hfam hadd
    (finite_iterate_notMem_pSmul_of_finite_prod p (D : Type u) M (hqn theta hco)) hpB xi m hsupp

end FromPair

end Crystalline

end

