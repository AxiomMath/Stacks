module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyAbsIrr
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The levels of a saturated lattice of a subspace

Let `O` be a domain with fraction field `E` and `ℓ ∈ O` a nonzero nonunit such that every nonzero
element of `O` divides a power of `ℓ` (a discrete valuation ring with `ℓ` in the maximal ideal).
For a subspace `W ⊆ E^ι`, the vectors of `O^ι` lying in `W` form the saturated lattice
`W° = W ∩ O^ι`; its image in `(O/ℓᴺ⁺¹)^ι` is `Stacks.EtaleCohomology.latticeLevel W`. It is stable
under every integral matrix stabilizing `W` (`Stacks.EtaleCohomology.mulVec_mem_latticeLevel`),
and:

* if `W ≠ 0`, `ℓᴺ` does not kill it
  (`Stacks.EtaleCohomology.exists_pow_smul_ne_zero_mem_latticeLevel`): a nonzero vector of `W°`
  divided by the largest power of `ℓ` dividing it has a coordinate prime to `ℓ`;
* if `W ≠ E^ι` and `c ≤ N`, it does not contain `ℓᶜ (O/ℓᴺ⁺¹)^ι`
  (`Stacks.EtaleCohomology.exists_pow_smul_not_mem_latticeLevel`): a linear form vanishing on `W`,
  with coprime integral coefficients, would vanish modulo `ℓᴺ⁺¹` on `ℓᶜ eⱼ` for a coefficient `hⱼ`
  prime to `ℓ`.

So a stable subspace `0 ≠ W ≠ E^ι` gives at every level `N ≥ c` a stable submodule which `ℓᴺ` does
not kill and which does not contain `ℓᶜ (O/ℓᴺ⁺¹)^ι`. We also record the level dichotomy of an
absolutely irreducible integral representation for submodules not killed by a smaller power of `ℓ`
(`Stacks.EtaleCohomology.exists_levelDichotomy_of_absIrr_pow`) and the divisibility it needs in
`O/ℓᴺ⁺¹` for a valuation ring `O`
(`Stacks.EtaleCohomology.exists_pow_succ_eq_mul_of_pow_smul_ne_zero`).

This is the lattice algebra by which, in piece L6 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), a proper nonzero subspace stable under `τ`
contradicts the level dichotomy of the Fourier transform.

## Main definitions

* `Stacks.EtaleCohomology.latticeLevel`.

## Main results

* `Stacks.EtaleCohomology.exists_eq_pow_smul_of_ne_zero`.
* `Stacks.EtaleCohomology.mulVec_mem_latticeLevel`.
* `Stacks.EtaleCohomology.exists_pow_smul_ne_zero_mem_latticeLevel`.
* `Stacks.EtaleCohomology.exists_pow_smul_not_mem_latticeLevel`.
* `Stacks.EtaleCohomology.exists_levelDichotomy_of_absIrr_pow`.
* `Stacks.EtaleCohomology.exists_pow_succ_eq_mul_of_pow_smul_ne_zero`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Primitive

variable {O : Type*} [CommRing O] [IsDomain O] {ι : Type*}

/-- **A nonzero integral vector is a power of `ℓ` times a vector with a coordinate prime to
`ℓ`**, when every nonzero element of `O` divides a power of the nonzero nonunit `ℓ`. -/
theorem exists_eq_pow_smul_of_ne_zero {ℓ : O} (hℓ0 : ℓ ≠ 0) (hℓu : ¬IsUnit ℓ)
    (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) {v : ι → O} (hv : v ≠ 0) :
    ∃ (k : ℕ) (u : ι → O), v = ℓ ^ k • u ∧ ∃ j, ¬ℓ ∣ u j := by
  classical
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hv
  obtain ⟨c, hc⟩ := hℓ (v j₀) hj₀
  have hex : ∃ k, ¬∀ i, ℓ ^ (k + 1) ∣ v i := by
    refine ⟨c, fun h => hℓu ?_⟩
    obtain ⟨t, ht⟩ := (h j₀).trans hc
    refine isUnit_iff_exists_inv.2 ⟨t, mul_left_cancel₀ (pow_ne_zero c hℓ0) ?_⟩
    rw [mul_one, ← mul_assoc, ← pow_succ]
    exact ht.symm
  let k := Nat.find hex
  have hk : ∀ i, ℓ ^ k ∣ v i := by
    intro i
    rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hs
    · simp [h0]
    · have hlt : k.pred < k := Nat.pred_lt (by omega)
      have := Nat.find_min hex hlt
      push Not at this
      rw [hs]
      exact this i
  choose u hu using hk
  refine ⟨k, u, funext fun i => by simp [hu i], ?_⟩
  obtain ⟨j, hj⟩ := not_forall.1 (Nat.find_spec hex)
  refine ⟨j, fun hdiv => hj ?_⟩
  rw [hu j, pow_succ]
  exact mul_dvd_mul_left _ hdiv

end Primitive

section Level

variable {O : Type*} (E : Type*) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
  [IsFractionRing O E] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The level of the saturated lattice of a subspace**: the image in `(O/I)^ι` of the vectors
of `O^ι` lying in `W ⊆ E^ι`. -/
def latticeLevel (W : Submodule E (ι → E)) (I : Ideal O) : Submodule (O ⧸ I) (ι → O ⧸ I) where
  carrier := {x | ∃ v : ι → O, (fun i => algebraMap O E (v i)) ∈ W ∧
    (fun i => Ideal.Quotient.mk I (v i)) = x}
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨v + w, ?_, funext fun i => by simp⟩
    convert W.add_mem hv hw using 1
    funext i
    simp
  zero_mem' := by
    refine ⟨0, ?_, funext fun i => by simp⟩
    convert W.zero_mem using 1
    funext i
    simp
  smul_mem' := by
    rintro r _ ⟨v, hv, rfl⟩
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨o • v, ?_, funext fun i => by simp⟩
    convert W.smul_mem (algebraMap O E o) hv using 1
    funext i
    simp

omit [IsDomain O] [IsFractionRing O E] [DecidableEq ι] in
/-- **The level of the saturated lattice is stable under the integral matrices stabilizing
`W`.** -/
theorem mulVec_mem_latticeLevel (W : Submodule E (ι → E)) (I : Ideal O) (X : Matrix ι ι O)
    (hX : ∀ v ∈ W, X.map (algebraMap O E) *ᵥ v ∈ W) {x : ι → O ⧸ I}
    (hx : x ∈ latticeLevel E W I) : X.map (algebraMap O (O ⧸ I)) *ᵥ x ∈ latticeLevel E W I := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨X *ᵥ v, ?_, ?_⟩
  · convert hX _ hv using 1
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  · funext i
    simp [Matrix.mulVec, dotProduct, map_sum, Ideal.Quotient.algebraMap_eq]

/-- `ℓᴺ x = 0` in `O/ℓᴺ⁺¹` exactly when `ℓ ∣ x`. -/
theorem pow_smul_mk_eq_zero_iff {ℓ : O} (hℓ0 : ℓ ≠ 0) (N : ℕ) (o : O) :
    ℓ ^ N • Ideal.Quotient.mk (Ideal.span {ℓ ^ (N + 1)}) o = 0 ↔ ℓ ∣ o := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, pow_succ]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ hℓ0)

variable {E}

omit [Fintype ι] [DecidableEq ι] in
/-- Clearing the denominators of a vector of `E^ι` lying in a subspace `W`: a nonzero vector of
`W` has a nonzero integral multiple in `W°`. -/
theorem exists_integral_mem_of_ne_bot [Finite ι] {W : Submodule E (ι → E)} (hW : W ≠ ⊥) :
    ∃ v : ι → O, v ≠ 0 ∧ (fun i => algebraMap O E (v i)) ∈ W := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose v hv using hb
  have hvw : (fun i => algebraMap O E (v i)) = algebraMap O E (b : O) • w :=
    funext fun i => by rw [hv i, Pi.smul_apply, Algebra.smul_def, smul_eq_mul]
  refine ⟨v, fun h0 => hw0 ?_, ?_⟩
  · have : algebraMap O E (b : O) • w = 0 := by
      rw [← hvw, h0]
      funext i
      simp
    exact (smul_eq_zero.1 this).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  · rw [hvw]
    exact W.smul_mem _ hw

/-- Recovering an integral element from its multiple by `ℓᵏ` in the fraction field. -/
private theorem algebraMap_eq_inv_pow_mul {ℓ : O} (hℓ0 : ℓ ≠ 0) (k : ℕ) (u : O) :
    algebraMap O E u = (algebraMap O E ℓ ^ k)⁻¹ * algebraMap O E (ℓ ^ k * u) := by
  rw [map_mul, map_pow, inv_mul_cancel_left₀]
  exact pow_ne_zero _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hℓ0))

variable (E)

omit [Fintype ι] [DecidableEq ι] in
/-- **`ℓᴺ` does not kill the `N`-th level of the saturated lattice of a nonzero subspace.** -/
theorem exists_pow_smul_ne_zero_mem_latticeLevel [Finite ι] {ℓ : O} (hℓ0 : ℓ ≠ 0)
    (hℓu : ¬IsUnit ℓ) (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) {W : Submodule E (ι → E)}
    (hW : W ≠ ⊥) (N : ℕ) :
    ∃ x ∈ latticeLevel E W (Ideal.span {ℓ ^ (N + 1)}), ℓ ^ N • x ≠ 0 := by
  obtain ⟨v, hv0, hvW⟩ := exists_integral_mem_of_ne_bot (O := O) hW
  obtain ⟨k, u, rfl, j, hj⟩ := exists_eq_pow_smul_of_ne_zero hℓ0 hℓu hℓ hv0
  have huW : (fun i => algebraMap O E (u i)) ∈ W := by
    have : (fun i => algebraMap O E (u i)) =
        (algebraMap O E ℓ ^ k)⁻¹ • fun i => algebraMap O E ((ℓ ^ k • u) i) :=
      funext fun i => algebraMap_eq_inv_pow_mul hℓ0 k (u i)
    rw [this]
    exact W.smul_mem _ hvW
  exact ⟨fun i => Ideal.Quotient.mk _ (u i), ⟨u, huW, rfl⟩,
    fun h => hj ((pow_smul_mk_eq_zero_iff hℓ0 N (u j)).1 (congrFun h j))⟩

omit [DecidableEq ι] in
/-- **A proper subspace has a linear form with integral coefficients, one of them prime to `ℓ`,
vanishing on its saturated lattice.** -/
theorem exists_primitive_integral_form_of_ne_top {ℓ : O} (hℓ0 : ℓ ≠ 0) (hℓu : ¬IsUnit ℓ)
    (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) {W : Submodule E (ι → E)} (hW : W ≠ ⊤) :
    ∃ h : ι → O, (∃ j, ¬ℓ ∣ h j) ∧
      ∀ v : ι → O, (fun i => algebraMap O E (v i)) ∈ W → ∑ i, h i * v i = 0 := by
  classical
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hW)
  let fc : ι → E := fun i => f fun j => if i = j then 1 else 0
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fc
  choose g hg using hb
  have hb0 : algebraMap O E (b : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hfc0 : ∀ i, g i = 0 → fc i = 0 := fun i hi => by
    have := hg i
    rw [hi, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hb0
  have hg0 : g ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f x, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    show x i • fc i = 0
    rw [hfc0 i (congrFun h0 i), smul_zero]
  obtain ⟨k, h, hgh, j, hj⟩ := exists_eq_pow_smul_of_ne_zero hℓ0 hℓu hℓ hg0
  refine ⟨h, ⟨j, hj⟩, fun v hv => ?_⟩
  have hfv : f (fun i => algebraMap O E (v i)) = 0 := hWf hv
  rw [LinearMap.pi_apply_eq_sum_univ f] at hfv
  apply IsFractionRing.injective O E
  rw [map_sum, map_zero]
  have hfc : ∀ i, algebraMap O E (h i) = (algebraMap O E ℓ ^ k)⁻¹ *
      (algebraMap O E (b : O) * fc i) := by
    intro i
    rw [algebraMap_eq_inv_pow_mul (E := E) hℓ0 k (h i), show ℓ ^ k * h i = g i from
      (congrFun hgh i).symm, hg i, Algebra.smul_def]
  have : ∑ i, algebraMap O E (h i * v i) =
      (algebraMap O E ℓ ^ k)⁻¹ * algebraMap O E (b : O) *
        ∑ i, algebraMap O E (v i) • fc i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hfc i, smul_eq_mul]
    ring
  rw [this]
  show _ * ∑ i, algebraMap O E (v i) • f (fun j => if i = j then 1 else 0) = 0
  rw [hfv, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- **The `N`-th level of the saturated lattice of a proper subspace does not contain
`ℓᶜ (O/ℓᴺ⁺¹)^ι` for `c ≤ N`.** -/
theorem exists_pow_smul_not_mem_latticeLevel [Finite ι] {ℓ : O} (hℓ0 : ℓ ≠ 0) (hℓu : ¬IsUnit ℓ)
    (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) {W : Submodule E (ι → E)} (hW : W ≠ ⊤) {c N : ℕ}
    (hcN : c ≤ N) :
    ∃ w : ι → O ⧸ Ideal.span {ℓ ^ (N + 1)},
      ℓ ^ c • w ∉ latticeLevel E W (Ideal.span {ℓ ^ (N + 1)}) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨h, ⟨j, hj⟩, hker⟩ := exists_primitive_integral_form_of_ne_top E hℓ0 hℓu hℓ hW
  refine ⟨Pi.single j 1, fun hmem => hj ?_⟩
  obtain ⟨v, hv, hvx⟩ := hmem
  have hcoord : ∀ i, ∃ z, v i = ℓ ^ c * (if i = j then 1 else 0) + ℓ ^ (N + 1) * z := by
    intro i
    have := congrFun hvx i
    simp only [Pi.smul_apply, Pi.single_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
      at this
    have h2 : Ideal.Quotient.mk (Ideal.span {ℓ ^ (N + 1)}) (v i) =
        Ideal.Quotient.mk _ (ℓ ^ c * if i = j then 1 else 0) := by
      rw [this]
      split_ifs <;> simp
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨z, hz⟩ := h2
    exact ⟨z, by linear_combination hz⟩
  choose z hz using hcoord
  have hsum := hker v hv
  have hexp : ∑ i, h i * v i = ℓ ^ c * (h j + ℓ ^ (N + 1 - c) * ∑ i, h i * z i) := by
    have hN : ℓ ^ (N + 1) = ℓ ^ c * ℓ ^ (N + 1 - c) := by
      rw [← pow_add, Nat.add_sub_cancel' (show c ≤ N + 1 by omega)]
    simp only [hz, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hN, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
  rw [hexp] at hsum
  have h3 : h j = -(ℓ ^ (N + 1 - c) * ∑ i, h i * z i) :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 hsum).resolve_left (pow_ne_zero _ hℓ0))
  rw [h3]
  exact ((dvd_pow_self ℓ (by omega)).mul_right _).neg_right

end Level

section Dichotomy

variable {O : Type*} (E : Type*) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
  [IsFractionRing O E] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The level dichotomy of an absolutely irreducible integral representation, for submodules
not killed by a smaller power of `ℓ`.** Under the hypotheses of
`Stacks.EtaleCohomology.exists_levelDichotomy_of_absIrr`, there is `c₀` such that for every
commutative `O`-algebra `R` and all `N`, `a` with `ℓᴺ r ≠ 0 ⇒ r ∣ ℓ^{a+1}` in `R`, an
`S₀`-stable submodule `S ⊆ R^ι` with `ℓᴺ S ≠ 0` contains `ℓ^{c₀ + a} R^ι`. -/
theorem exists_levelDichotomy_of_absIrr_pow (K : Type*) [Field K] [IsAlgClosed K] [Algebra E K]
    {ℓ : O} (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) (S₀ : Set (Matrix ι ι O))
    (hmul : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b ∈ S₀) (hone : (1 : Matrix ι ι O) ∈ S₀)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ a ∈ S₀, ∀ v ∈ W, (a.map (algebraMap O E)).map (algebraMap E K) *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    ∃ c₀ : ℕ, ∀ (R : Type) [CommRing R] [Algebra O R] (N a : ℕ),
      (∀ r : R, ℓ ^ N • r ≠ 0 → ∃ t : R, algebraMap O R ℓ ^ (a + 1) = r * t) →
      ∀ S : Submodule R (ι → R), (∀ M ∈ S₀, ∀ v ∈ S, M.map (algebraMap O R) *ᵥ v ∈ S) →
        (∃ x ∈ S, ℓ ^ N • x ≠ 0) → ∀ w : ι → R, ℓ ^ (c₀ + a) • w ∈ S := by
  have hspan : Submodule.span E (Set.range fun a : S₀ => a.1.map (algebraMap O E)) = ⊤ :=
    span_range_eq_top_of_forall_mulVec_map_mem (K := K) (fun a : S₀ => a.1.map (algebraMap O E))
      (fun a b => ⟨⟨a.1 * b.1, hmul a.1 a.2 b.1 b.2⟩, (Matrix.map_mul).symm⟩)
      ⟨⟨1, hone⟩, Matrix.map_one _ (map_zero _) (map_one _)⟩
      (fun W hW => hirr W fun a ha v hv => hW ⟨a, ha⟩ v hv)
  obtain ⟨d, hd, hdS⟩ := exists_ne_zero_smul_mem_span_of_span_map_eq_top E S₀ hspan
  obtain ⟨c, e, he⟩ := hℓ d hd
  refine ⟨c + 1, fun R _ _ N a hdiv S hS ⟨x, hx, hxN⟩ w => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, ℓ ^ N • x j ≠ 0 := Function.ne_iff.1 hxN
  obtain ⟨t, ht⟩ := hdiv (x j) hj
  have hR : algebraMap O R (ℓ ^ (c + 1 + a)) =
      algebraMap O R d * x j * (algebraMap O R e * t) := by
    rw [show c + 1 + a = c + (a + 1) by omega, pow_add, map_mul, he, map_mul, map_pow, ht]
    ring
  have hw : ℓ ^ (c + 1 + a) • w = (algebraMap O R d * x j) • (algebraMap O R e * t) • w := by
    rw [smul_smul, algebra_compatible_smul R (ℓ ^ (c + 1 + a)) w, hR]
  rw [hw]
  exact smul_mem_of_forall_matrix_mem S₀ d hdS S hS hx j ((algebraMap O R e * t) • w)

/-- **Divisibility in `O/ℓᴺ⁺¹` for a valuation ring `O`**: if `ℓ^{N-a} r ≠ 0` then `r` divides
`ℓ^{a+1}` (for `a ≤ N`). -/
theorem exists_pow_succ_eq_mul_of_pow_smul_ne_zero [ValuationRing O] (ℓ : O) {N a : ℕ}
    (haN : a ≤ N) (r : O ⧸ Ideal.span {ℓ ^ (N + 1)}) (hr : ℓ ^ (N - a) • r ≠ 0) :
    ∃ t : O ⧸ Ideal.span {ℓ ^ (N + 1)},
      algebraMap O (O ⧸ Ideal.span {ℓ ^ (N + 1)}) ℓ ^ (a + 1) = r * t := by
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨t, ht | ht⟩ := ValuationRing.cond o (ℓ ^ (a + 1))
  · exact ⟨Ideal.Quotient.mk _ t, by rw [Ideal.Quotient.algebraMap_eq, ← map_pow, ← ht, map_mul]⟩
  · exfalso
    apply hr
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, ← ht, ← mul_assoc, ← pow_add]
    exact dvd_mul_of_dvd_left (by rw [show N - a + (a + 1) = N + 1 by omega]) _

end Dichotomy

end Stacks.EtaleCohomology

end
