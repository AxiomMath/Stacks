module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreierInertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.ConstantFieldExtension

/-!
# Artin–Schreier classes of large pole order over all constant field extensions at once

Let `A` be a discrete valuation ring with finite residue field and fraction field `K` of
characteristic `p`, `k ⊆ K` a finite field at least as large as the residue field, `M` a separable
closure of `K` and `P` a maximal ideal of the integral closure of `A` in `M`. Let `K̄ ⊆ M` be the
field generated over `K` by all elements of `M` algebraic over `k` (the constants). Every finite
level `K(k₃)` of `K̄` is inert over `A` (`IsDiscreteValuationRing.ConstantFieldExtension`), so
the integral closure `Ā` of `A` in `K̄` is again a discrete valuation ring, with the same
uniformizer and a perfect residue field. Applying
`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_mem_ne` over `Ā` gives one bound `N`
for all constant field extensions at once: for `n > N` prime to `p`, constants `a ≠ 0`, `c`, and
every root `y` of `y ^ p - y = a π ^ (-n) + c π ^ (-1)`, some element of the inertia group of `P`
fixing the constants and a given finite subextension moves `y`.

## Main results

* `IsDiscreteValuationRing.forall_exists_mem_sub_eq_of_forall_exists_ne`: the trace trick, for
  any subgroup of the Galois group.
* `IsDiscreteValuationRing.constantClosure_dvr`: the integral closure of `A` in `K̄` is a discrete
  valuation ring with uniformizer `π`; `isFractionRing_constantClosure`,
  `perfectField_residueField_constantClosure`.
* `IsDiscreteValuationRing.exists_forall_exists_mem_inertia_ne_of_dvr`: the pole-order argument
  over an intermediate field carrying a discrete valuation ring.
* `IsDiscreteValuationRing.exists_forall_exists_mem_inertia_ne_of_isAlgebraic`: one bound for all
  constant field extensions.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

section Trace

/-- An additive subgroup `W` of a finite field `k` on which no nonzero linear form `Tr(b ·)`
vanishes is all of `k`, by nondegeneracy of the trace form. -/
theorem forall_mem_of_forall_exists_trace_mul_ne_zero {k : Type*} [Field k] [Finite k] (p : ℕ)
    [Fact p.Prime] [Algebra (ZMod p) k] (W : AddSubgroup k)
    (htr : ∀ b : k, b ≠ 0 → ∃ w ∈ W, Algebra.trace (ZMod p) k (b * w) ≠ 0) (c : k) : c ∈ W := by
  let W' : Submodule (ZMod p) k :=
    { W with
      smul_mem' := fun a w hw => by
        rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul]
        exact W.nsmul_mem hw _ }
  let β : k →ₗ[ZMod p] Module.Dual (ZMod p) W' :=
    (Algebra.traceForm (ZMod p) k).compl₂ W'.subtype
  have hβ : Function.Injective β := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro b hb
    by_contra hb0
    obtain ⟨w, hw, hw0⟩ := htr b hb0
    apply hw0
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hb) ⟨w, hw⟩
    simpa [β, Algebra.traceForm_apply] using this
  have hle := LinearMap.finrank_le_finrank_of_injective hβ
  rw [Subspace.dual_finrank_eq] at hle
  have htop : W' = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W') hle)
  exact (htop ▸ Submodule.mem_top : c ∈ W')

/-- **The trace trick.** Let `H` be a subgroup of `Gal(L/K)`, `k ⊆ K` a finite field with `q`
elements, `f ∈ K` and `t ∈ L` a root of `t ^ q - t = f`. If for every `b ∈ kˣ` every root `z` of
`z ^ p - z = b f` is moved by some element of `H`, then `σ ↦ σ t - t` maps `H` onto `k`. For
`b ∈ k`, `z = ∑_{i < r} (b t) ^ (p ^ i)` (`q = p ^ r`) is such a root, with
`σ z - z = Tr_{k/𝔽_p}(b (σ t - t))`; so the image `W` of `H` is killed by no linear form
`Tr(b ·)`, `b ≠ 0`, and `W = k` by nondegeneracy of the trace form. -/
theorem forall_exists_mem_sub_eq_of_forall_exists_ne {K L : Type*} [Field K] [Field L]
    [Algebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (k : Type*) [Field k] [Fintype k]
    [Algebra k K] (H : Subgroup Gal(L/K)) (f : K)
    (hH : ∀ b : k, b ≠ 0 → ∀ z : L, z ^ p - z = algebraMap K L (algebraMap k K b * f) →
      ∃ σ ∈ H, σ z ≠ z)
    (t : L) (ht : t ^ Fintype.card k - t = algebraMap K L f) :
    ∀ c : k, ∃ σ ∈ H, σ t - t = algebraMap K L (algebraMap k K c) := by
  classical
  let e : k →+* L := (algebraMap K L).comp (algebraMap k K)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 (e.injective (by simp))
  let : Algebra (ZMod p) k := ZMod.algebra k p
  set r := Module.finrank (ZMod p) k
  have hcard : Fintype.card k = p ^ r := by
    rw [Module.card_fintype (Module.finBasis (ZMod p) k), ZMod.card, Fintype.card_fin]
  have hfix : ∀ (σ : Gal(L/K)) (c : k), σ (e c) = e c := fun σ c => AlgEquiv.commutes σ _
  -- the image of `H` is an additive subgroup of `k`
  let W : AddSubgroup k :=
    { carrier := {c | ∃ σ ∈ H, σ t - t = e c}
      zero_mem' := ⟨1, H.one_mem, by simp⟩
      add_mem' := by
        rintro c₁ c₂ ⟨σ₁, h₁H, h₁⟩ ⟨σ₂, h₂H, h₂⟩
        refine ⟨σ₁ * σ₂, H.mul_mem h₁H h₂H, ?_⟩
        have : σ₁ (σ₂ t) = σ₁ t + e c₂ := by
          rw [show σ₂ t = t + e c₂ by rw [← h₂]; ring, map_add, hfix]
        rw [AlgEquiv.mul_apply, this, map_add]
        linear_combination h₁
      neg_mem' := by
        rintro c ⟨σ, hσH, h⟩
        refine ⟨σ⁻¹, H.inv_mem hσH, ?_⟩
        have h1 : σ⁻¹ (σ t - t) = σ⁻¹ (e c) := by rw [h]
        rw [map_sub, hfix, show σ⁻¹ (σ t) = t from σ.symm_apply_apply t] at h1
        rw [map_neg]
        linear_combination -h1 }
  -- no nonzero linear form `Tr(b ·)` kills `W`
  have htr : ∀ b : k, b ≠ 0 → ∃ w ∈ W, Algebra.trace (ZMod p) k (b * w) ≠ 0 := by
    intro b hb
    let z : L := ∑ i ∈ Finset.range r, (e b * t) ^ (p ^ i)
    have hzp : z ^ p = ∑ i ∈ Finset.range r, (e b * t) ^ (p ^ (i + 1)) := by
      rw [sum_pow_char]
      exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul, pow_succ]
    have hbq : e b ^ (p ^ r) = e b := by rw [← map_pow, ← hcard, FiniteField.pow_card]
    have hz : z ^ p - z = algebraMap K L (algebraMap k K b * f) := by
      rw [hzp, show z = ∑ i ∈ Finset.range r, (e b * t) ^ (p ^ i) from rfl,
        ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (e b * t) ^ (p ^ i)), pow_zero,
        pow_one, mul_pow, hbq, ← hcard, map_mul]
      change e b * t ^ Fintype.card k - e b * t = e b * algebraMap K L f
      linear_combination (e b) * ht
    obtain ⟨σ, hσH, hσ⟩ := hH b hb z hz
    obtain ⟨c, hc⟩ := exists_sub_eq_algebraMap_of_pow_card_sub_self K k σ t _ ht
    refine ⟨c, ⟨σ, hσH, hc⟩, fun h0 => hσ ?_⟩
    have hσz : σ z - z = e (algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (b * c))) := by
      rw [FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) k, Nat.card_zmod, map_sum, map_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, map_mul, hfix, map_pow, map_mul, ← sub_pow_char_pow, ← mul_sub, hc]
      rfl
    rwa [h0, map_zero, map_zero, sub_eq_zero] at hσz
  -- hence `W = k`, by nondegeneracy of the trace form
  exact forall_mem_of_forall_exists_trace_mul_ne_zero p W htr

end Trace

/-- `K(φ(k'))` is finite over `K` for a `k`-algebra map `φ` from a finite field `k'`. -/
private theorem finiteDimensional_adjoin_range_of_finite {k k' K M : Type*} [Field k] [Finite k]
    [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field M] [Algebra K M] [Algebra k K]
    [Algebra k M] [IsScalarTower k K M] (φ : k' →ₐ[k] M) :
    FiniteDimensional K (IntermediateField.adjoin K (Set.range φ)) := by
  have : Finite (Set.range φ) := (Set.finite_range _).to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  obtain ⟨z, rfl⟩ := hx
  exact ((Algebra.IsIntegral.isIntegral (R := k) z).map φ).tower_top

/-- `K(φ(k'))` is separable over `K` for a `k`-algebra map `φ` from a finite field `k'`. -/
private theorem isSeparable_adjoin_range_of_finite {k k' K M : Type*} [Field k] [Finite k]
    [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field M] [Algebra K M] [Algebra k K]
    [Algebra k M] [IsScalarTower k K M] (φ : k' →ₐ[k] M) :
    Algebra.IsSeparable K (IntermediateField.adjoin K (Set.range φ)) := by
  refine (IntermediateField.isSeparable_adjoin_iff_isSeparable K M).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := hx
  exact ((Algebra.IsSeparable.isSeparable k z).map (f := φ) φ.injective).tower_top K

/-- `c ^ [K(φ(k')) : K] ≤ |k'|` whenever `c ≤ |k|`, for a `k`-algebra map `φ` from a finite field
`k'`, since `[K(φ(k')) : K] ≤ [k' : k]`. -/
private theorem pow_finrank_adjoin_range_le_card {k k' K M : Type*} [Field k] [Finite k]
    [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field M] [Algebra K M] [Algebra k K]
    [Algebra k M] [IsScalarTower k K M] {c : ℕ} (hc : c ≤ Nat.card k) (φ : k' →ₐ[k] M) :
    c ^ Module.finrank K (IntermediateField.adjoin K (Set.range φ)) ≤ Nat.card k' := by
  rw [Module.natCard_eq_pow_finrank (K := k) (V := k')]
  exact (Nat.pow_le_pow_left hc _).trans
    (Nat.pow_le_pow_right Finite.card_pos (finrank_adjoin_range_le φ))

section Levels

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K] [Finite (IsLocalRing.ResidueField A)]
  (k : Type*) [Field k] [Finite k] [Algebra k K]
  (M : Type*) [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M] [Algebra k M]
  [IsScalarTower k K M]

/-- The constant field extension `K(k(T)) ⊆ M` generated by the field `k(T)`, `T` a finite set of
constants. -/
def constantLevel (T : Finset M) : IntermediateField K M :=
  IntermediateField.adjoin K (Set.range (IntermediateField.adjoin k (T : Set M)).val)

/-- The field `K̄ ⊆ M` generated over `K` by all elements of `M` algebraic over `k`. -/
def constantClosure : IntermediateField K M :=
  IntermediateField.adjoin K ((algebraicClosure k M : IntermediateField k M) : Set M)

variable {k M} in
omit [Finite k] in
/-- `k(T)` is a finite extension of `k` for a finite set `T` of constants. -/
theorem finiteDimensional_adjoin_constants {T : Finset M} (hT : ∀ t ∈ T, IsAlgebraic k t) :
    FiniteDimensional k (IntermediateField.adjoin k (T : Set M)) :=
  IntermediateField.finiteDimensional_adjoin fun t ht => (hT t ht).isIntegral

variable {k M} in
/-- `k(T)` is finite for a finite set `T` of constants. -/
theorem finite_adjoin_constants {T : Finset M} (hT : ∀ t ∈ T, IsAlgebraic k t) :
    Finite (IntermediateField.adjoin k (T : Set M)) :=
  have := finiteDimensional_adjoin_constants hT
  Module.finite_of_finite k

variable {k M} in
/-- `K(k(T))` is a finite extension of `K` for a finite set `T` of constants. -/
theorem finiteDimensional_constantLevel {T : Finset M} (hT : ∀ t ∈ T, IsAlgebraic k t) :
    FiniteDimensional K (constantLevel K k M T) := by
  have := finite_adjoin_constants hT
  exact finiteDimensional_adjoin_range_of_finite (k := k)
    (IntermediateField.adjoin k (T : Set M)).val

variable {k M} in
/-- `K(k(T))` is a separable extension of `K` for a finite set `T` of constants. -/
theorem isSeparable_constantLevel {T : Finset M} (hT : ∀ t ∈ T, IsAlgebraic k t) :
    Algebra.IsSeparable K (constantLevel K k M T) := by
  have := finite_adjoin_constants hT
  exact isSeparable_adjoin_range_of_finite (k := k) (IntermediateField.adjoin k (T : Set M)).val

variable {k M} in
/-- The inclusion of `k(T)` into `K(k(T))`. -/
def constantLevelIncl (T : Finset M) :
    IntermediateField.adjoin k (T : Set M) →+* constantLevel K k M T where
  toFun z := ⟨z, IntermediateField.subset_adjoin _ _ ⟨z, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {k M} in
omit [Algebra A K] [IsFractionRing A K] [Finite (IsLocalRing.ResidueField A)] [Algebra A M]
  [IsScalarTower A K M] in
/-- **The size condition of inertness for a constant level**: `|κ| ^ [K(k(T)) : K] ≤ |k(T)|`,
by `[K(k(T)) : K] ≤ [k(T) : k]` and `|κ| ≤ |k|`. -/
theorem card_pow_finrank_constantLevel_le
    (hk : Nat.card (IsLocalRing.ResidueField A) ≤ Nat.card k) {T : Finset M}
    (hT : ∀ t ∈ T, IsAlgebraic k t) :
    Nat.card (IsLocalRing.ResidueField A) ^ Module.finrank K (constantLevel K k M T) ≤
      Nat.card (IntermediateField.adjoin k (T : Set M)) := by
  have := finite_adjoin_constants hT
  exact pow_finrank_adjoin_range_le_card (K := K) hk (IntermediateField.adjoin k (T : Set M)).val

variable {k M} in
omit [Finite k] in
/-- `k(T)` is contained in the algebraic closure of `k` in `M` for a finite set `T` of
constants. -/
theorem adjoin_constants_le_algebraicClosure {T : Finset M} (hT : ∀ t ∈ T, IsAlgebraic k t) :
    IntermediateField.adjoin k (T : Set M) ≤ algebraicClosure k M :=
  IntermediateField.adjoin_le_iff.2 fun t ht => mem_algebraicClosure_iff.2 (hT t ht)

variable {k M} in
omit [Algebra k K] [IsScalarTower k K M] [Finite k] in
/-- `K(k(T)) ⊆ K̄` for a finite set `T` of constants. -/
theorem constantLevel_le_constantClosure {T : Finset M} (hT : ∀ t ∈ T, IsAlgebraic k t) :
    constantLevel K k M T ≤ constantClosure K k M := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro _ ⟨z, rfl⟩
  exact IntermediateField.subset_adjoin _ _ (adjoin_constants_le_algebraicClosure hT z.2)

variable {k M} in
omit [Finite k] [Algebra k K] [IsScalarTower k K M] in
/-- `K(k(T)) ⊆ K(k(T'))` for `T ⊆ T'`. -/
theorem constantLevel_mono {T T' : Finset M} (h : T ⊆ T') :
    constantLevel K k M T ≤ constantLevel K k M T' := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro _ ⟨z, rfl⟩
  have hz : (z : M) ∈ IntermediateField.adjoin k (T' : Set M) :=
    IntermediateField.adjoin.mono _ _ _ (Finset.coe_subset.2 h) z.2
  exact IntermediateField.subset_adjoin _ _ ⟨⟨z, hz⟩, rfl⟩

variable {k M} in
omit [Finite k] [Algebra k K] [IsScalarTower k K M] in
/-- Every element of `K̄` lies in a finite constant level. -/
theorem exists_mem_constantLevel {x : M} (hx : x ∈ constantClosure K k M) :
    ∃ T : Finset M, (∀ t ∈ T, IsAlgebraic k t) ∧ x ∈ constantLevel K k M T := by
  obtain ⟨T, hTS, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hx
  refine ⟨T, fun t ht => mem_algebraicClosure_iff.1 (hTS ht), ?_⟩
  refine IntermediateField.adjoin_le_iff.2 (fun t ht => ?_) hxT
  exact IntermediateField.subset_adjoin _ _ ⟨⟨t, IntermediateField.subset_adjoin _ _ ht⟩, rfl⟩

section Inclusion

variable {K M} {E F : IntermediateField K M} (h : E ≤ F)

/-- The inclusion of the integral closure of `A` in `E` into its integral closure in `F`, for
intermediate fields `E ≤ F` of `M / K`. -/
def integralClosureInclusion : integralClosure A E →+* integralClosure A F where
  toFun y := ⟨IntermediateField.inclusion h y.1,
    (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars A)
      (IntermediateField.inclusion h).injective).2 y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Finite (IsLocalRing.ResidueField A)] in
/-- The inclusion `integralClosureInclusion A h` does not change the underlying element of
`M`. -/
theorem val_integralClosureInclusion (y : integralClosure A E) :
    ((integralClosureInclusion A h y : F) : M) = ((y : E) : M) :=
  rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Finite (IsLocalRing.ResidueField A)] in
/-- The inclusion `integralClosureInclusion A h` is injective. -/
theorem integralClosureInclusion_injective : Function.Injective (integralClosureInclusion A h) :=
  fun y y' hy => Subtype.ext (Subtype.ext (by
    rw [← val_integralClosureInclusion A h y, ← val_integralClosureInclusion A h y', hy]))

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Finite (IsLocalRing.ResidueField A)] in
/-- The inclusion `integralClosureInclusion A h` commutes with the structure maps from `A`. -/
theorem integralClosureInclusion_algebraMap (a : A) :
    integralClosureInclusion A h (algebraMap A _ a) = algebraMap A _ a :=
  Subtype.ext (AlgHom.commutes ((IntermediateField.inclusion h).restrictScalars A) a)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Finite (IsLocalRing.ResidueField A)] in
/-- An element of the integral closure of `A` in `F` whose value lies in `E` comes from `E`. -/
theorem exists_integralClosureInclusion_eq (x : integralClosure A F) (hx : ((x : F) : M) ∈ E) :
    ∃ y, integralClosureInclusion A h y = x := by
  have hint : IsIntegral A (⟨_, hx⟩ : E) := by
    refine (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars A)
      (IntermediateField.inclusion h).injective).1 ?_
    have he : ((IntermediateField.inclusion h).restrictScalars A) ⟨_, hx⟩ = (x : F) :=
      Subtype.ext rfl
    rw [he]
    exact x.2
  exact ⟨⟨_, hint⟩, Subtype.ext (Subtype.ext rfl)⟩

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [Finite (IsLocalRing.ResidueField A)] in
/-- The inclusion reflects units: the inverse of a value lies in `E`. -/
theorem isUnit_of_isUnit_integralClosureInclusion {y : integralClosure A E}
    (hy : IsUnit (integralClosureInclusion A h y)) : IsUnit y := by
  obtain ⟨u, hu⟩ := hy
  set q : integralClosure A F := ↑u⁻¹
  have hyq : integralClosureInclusion A h y * q = 1 := by rw [← hu]; exact u.mul_inv
  have hval := congrArg (fun z : integralClosure A F => ((z : F) : M)) hyq
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at hval
  rw [val_integralClosureInclusion] at hval
  have hqv : ((q : F) : M) = ((y : E) : M)⁻¹ := eq_inv_of_mul_eq_one_right hval
  have hqmem : ((q : F) : M) ∈ E := by
    rw [hqv]
    exact inv_mem (y : E).2
  obtain ⟨y', hy'⟩ := exists_integralClosureInclusion_eq A h q hqmem
  refine IsUnit.of_mul_eq_one y' (integralClosureInclusion_injective A h ?_)
  rw [map_mul, map_one, hy']
  exact hyq

end Inclusion

/-- Every element of the integral closure of `A` in `K̄` comes from a finite constant level. -/
private theorem exists_integralClosureInclusion_constantLevel_eq {A K k M : Type*}
    [CommRing A] [Field K] [Field k] [Field M] [Algebra K M] [Algebra A K] [Algebra A M]
    [IsScalarTower A K M] [Algebra k M] (x : integralClosure A (constantClosure K k M)) :
    ∃ (T : Finset M) (hT : ∀ t ∈ T, IsAlgebraic k t)
      (y : integralClosure A (constantLevel K k M T)),
      integralClosureInclusion A (constantLevel_le_constantClosure K hT) y = x := by
  obtain ⟨T, hT, hxT⟩ := exists_mem_constantLevel K (x : constantClosure K k M).2
  obtain ⟨y, hy⟩ :=
    exists_integralClosureInclusion_eq A (constantLevel_le_constantClosure K hT) x hxT
  exact ⟨T, hT, y, hy⟩

variable {k M} in
/-- The constant levels are discrete valuation rings in which a uniformizer of `A` stays a
uniformizer, with finite residue fields. -/
theorem constantLevel_dvr (hk : Nat.card (IsLocalRing.ResidueField A) ≤ Nat.card k)
    {T : Finset M} (hT : ∀ t ∈ T, IsAlgebraic k t) :
    IsDiscreteValuationRing (integralClosure A (constantLevel K k M T)) ∧
      (∀ {π : A}, Irreducible π → Irreducible (algebraMap A
        (integralClosure A (constantLevel K k M T)) π)) ∧
      ∀ (m : Ideal (integralClosure A (constantLevel K k M T))) [m.IsMaximal],
        Finite (integralClosure A (constantLevel K k M T) ⧸ m) := by
  have := finiteDimensional_constantLevel K hT
  have := isSeparable_constantLevel K hT
  have := finite_adjoin_constants hT
  have hcard := card_pow_finrank_constantLevel_le A K hk hT
  exact ⟨isDiscreteValuationRing_integralClosure_of_card_pow_le A K _ (constantLevelIncl K T) hcard,
    fun hπ => irreducible_algebraMap_integralClosure_of_card_pow_le A K _ (constantLevelIncl K T)
      hcard hπ,
    fun m _ => finite_quotient_integralClosure_of_card_pow_le A K _ (constantLevelIncl K T)
      hcard m⟩

variable {k M} in
/-- **The integral closure of `A` in `K̄` is a discrete valuation ring with uniformizer `π`.**
Every nonzero element lies in a constant level, where it is a unit times a power of `π`, and the
units of the levels are units of the closure. -/
theorem constantClosure_dvr (hk : Nat.card (IsLocalRing.ResidueField A) ≤ Nat.card k) {π : A}
    (hπ : Irreducible π) :
    Irreducible (algebraMap A (integralClosure A (constantClosure K k M)) π) ∧
      IsDiscreteValuationRing (integralClosure A (constantClosure K k M)) := by
  classical
  set p₀ := algebraMap A (integralClosure A (constantClosure K k M)) π
  -- the closure is a domain, as a subring of a field
  have h0 : ∀ t ∈ (∅ : Finset M), IsAlgebraic k t := fun t ht => absurd ht (Finset.notMem_empty t)
  have hirr : Irreducible p₀ := by
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · obtain ⟨q, hq⟩ := hu.exists_right_inv
      obtain ⟨T, hT, y, rfl⟩ := exists_integralClosureInclusion_constantLevel_eq q
      have h1 : integralClosureInclusion A (constantLevel_le_constantClosure K hT)
          (algebraMap A _ π * y) =
          integralClosureInclusion A (constantLevel_le_constantClosure K hT) 1 := by
        rw [map_mul, integralClosureInclusion_algebraMap, map_one]
        exact hq
      exact ((constantLevel_dvr A K hk hT).2.1 hπ).not_isUnit
        (IsUnit.of_mul_eq_one y
          (integralClosureInclusion_injective A (constantLevel_le_constantClosure K hT) h1))
    · obtain ⟨T₁, hT₁, ha⟩ := exists_mem_constantLevel K (a : constantClosure K k M).2
      obtain ⟨T₂, hT₂, hb⟩ := exists_mem_constantLevel K (b : constantClosure K k M).2
      have hT : ∀ t ∈ T₁ ∪ T₂, IsAlgebraic k t := fun t ht =>
        (Finset.mem_union.1 ht).elim (hT₁ t) (hT₂ t)
      obtain ⟨ya, rfl⟩ := exists_integralClosureInclusion_eq A
        (constantLevel_le_constantClosure K hT) a
        (constantLevel_mono K Finset.subset_union_left ha)
      obtain ⟨yb, rfl⟩ := exists_integralClosureInclusion_eq A
        (constantLevel_le_constantClosure K hT) b
        (constantLevel_mono K Finset.subset_union_right hb)
      have h1 : algebraMap A _ π = ya * yb :=
        integralClosureInclusion_injective A (constantLevel_le_constantClosure K hT) (by
          rw [map_mul, integralClosureInclusion_algebraMap]
          exact hab)
      exact (((constantLevel_dvr A K hk hT).2.1 hπ).isUnit_or_isUnit h1).imp
        (fun h => h.map _) (fun h => h.map _)
  refine ⟨hirr, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p₀, hirr, fun {x} hx => ?_⟩⟩
  obtain ⟨T, hT, y, rfl⟩ := exists_integralClosureInclusion_constantLevel_eq x
  have := (constantLevel_dvr A K hk hT).1
  have hy0 : y ≠ 0 := by rintro rfl; exact hx (map_zero _)
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 ((constantLevel_dvr A K hk hT).2.1 hπ)
  refine ⟨n, (u.map (integralClosureInclusion A
    (constantLevel_le_constantClosure K hT)).toMonoidHom), ?_⟩
  rw [hu, map_mul, map_pow, integralClosureInclusion_algebraMap, mul_comm]
  rfl

variable {k M} in
omit [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] [Finite k] in
/-- `K̄` is the fraction field of the integral closure of `A` in it: `K̄ / K` is algebraic. -/
theorem isFractionRing_constantClosure :
    IsFractionRing (integralClosure A (constantClosure K k M)) (constantClosure K k M) := by
  have : Algebra.IsAlgebraic K (constantClosure K k M) :=
    IntermediateField.isAlgebraic_adjoin fun x hx =>
      (mem_algebraicClosure_iff'.1 hx).tower_top
  have : Algebra.IsAlgebraic A (constantClosure K k M) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  refine integralClosure.isFractionRing_of_algebraic (A := A) (L := constantClosure K k M)
    fun x hx => ?_
  have hx' : algebraMap K (constantClosure K k M) (algebraMap A K x) = 0 := by
    rw [← IsScalarTower.algebraMap_apply]
    exact hx
  exact IsFractionRing.injective A K ((map_eq_zero_iff _ (algebraMap K _).injective).1 hx'
    |>.trans (map_zero _).symm)

variable {k M} in
/-- **The residue field of the integral closure of `A` in `K̄` is perfect**: every residue is the
residue of an element of a constant level, whose residue field is finite, so it is fixed by a
power `q = p ^ n` of Frobenius and is a `p`-th power. -/
theorem perfectField_residueField_constantClosure (p : ℕ) [Fact p.Prime] [CharP K p]
    (hk : Nat.card (IsLocalRing.ResidueField A) ≤ Nat.card k)
    [IsLocalRing (integralClosure A (constantClosure K k M))] :
    PerfectField (IsLocalRing.ResidueField (integralClosure A (constantClosure K k M))) := by
  classical
  set R := integralClosure A (constantClosure K k M)
  set κ := IsLocalRing.ResidueField R
  have hp0 : ∀ E : IntermediateField K M, (p : integralClosure A E) = 0 := fun E => by
    apply Subtype.ext
    apply Subtype.ext
    change ((p : M)) = 0
    rw [← map_natCast (algebraMap K M), CharP.cast_eq_zero, map_zero]
  have : CharP κ p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 ?_
    rw [← map_natCast (IsLocalRing.residue R), hp0, map_zero]
  have : PerfectRing κ p := by
    refine PerfectRing.ofSurjective κ p fun z => ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨T, hT, y, rfl⟩ := exists_integralClosureInclusion_constantLevel_eq x
    obtain ⟨hdvr, -, hfin⟩ := constantLevel_dvr A K hk hT
    have := hdvr
    have := hfin (IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T)))
    let : Field (integralClosure A (constantLevel K k M T) ⧸
        IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T))) :=
      Ideal.Quotient.field (IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T)))
    let : Fintype (integralClosure A (constantLevel K k M T) ⧸
        IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T))) :=
      Fintype.ofFinite _
    have : CharP (integralClosure A (constantLevel K k M T) ⧸
        IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T))) p := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 ?_
      rw [← map_natCast (Ideal.Quotient.mk _), hp0, map_zero]
    obtain ⟨n, -, hn⟩ := FiniteField.card (integralClosure A (constantLevel K k M T) ⧸
      IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T))) p
    set Q := Fintype.card (integralClosure A (constantLevel K k M T) ⧸
      IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T)))
    have hyQ :
        y ^ Q - y ∈ IsLocalRing.maximalIdeal (integralClosure A (constantLevel K k M T)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, FiniteField.pow_card, sub_self]
    have hxQ : IsLocalRing.residue R
        (integralClosureInclusion A (constantLevel_le_constantClosure K hT) y) ^ Q =
        IsLocalRing.residue R
          (integralClosureInclusion A (constantLevel_le_constantClosure K hT) y) := by
      rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_pow, ← map_sub]
      exact fun hu => (IsLocalRing.mem_maximalIdeal _).1 hyQ
        (isUnit_of_isUnit_integralClosureInclusion A _ hu)
    refine ⟨IsLocalRing.residue R
      (integralClosureInclusion A (constantLevel_le_constantClosure K hT) y) ^
        (p ^ (n - 1 : ℕ)), ?_⟩
    rw [frobenius_def, ← pow_mul, ← pow_succ, Nat.sub_add_cancel n.pos, ← hn, hxQ]
  exact PerfectRing.toPerfectField κ p

end Levels

section Generic

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  (M : Type*) [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M] [IsSepClosure K M]
  (p : ℕ) [Fact p.Prime] [CharP K p]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- **The pole-order argument over an intermediate field.** Let `K ⊆ F ⊆ M` with `M` a separable
closure of `K`, and `R` a discrete valuation ring with fraction field `F`, perfect residue field
and uniformizer `π`, integral over `A`; let `E₀` be a finite subextension of `M / K`. There is `N`
such that for every unit `u` of `R`, `n > N` prime to `p` and root `y` of
`y ^ p - y = π ^ (-n) u`, some element of the inertia group of `P` fixing `F` and `E₀` moves `y`:
`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_mem_ne` over `F`, whose inertia group
lies in that over `K` (the integral closures of `A` and of `R` in `M` agree). -/
theorem exists_forall_exists_mem_inertia_ne_of_dvr
    (F : Type*) [Field F] [Algebra K F] [Algebra F M] [IsScalarTower K F M]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R F]
    [IsFractionRing R F] [Algebra R M] [IsScalarTower R F M]
    [PerfectField (IsLocalRing.ResidueField R)] [Algebra A R] [IsScalarTower A R M]
    [Algebra.IsIntegral A R]
    {π : A} (hπ : Irreducible (algebraMap A R π))
    (P : Ideal (integralClosure A M)) [P.IsMaximal] (E₀ : IntermediateField K M)
    [FiniteDimensional K E₀] :
    letI := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
    ∃ N : ℕ, ∀ (n : ℕ) (u : R), N < n → ¬ p ∣ n → IsUnit u → ∀ y : M,
      y ^ p - y = (algebraMap K M (algebraMap A K π))⁻¹ ^ n * algebraMap R M u →
      ∃ σ ∈ P.inertia Gal(M/K), (∀ z : F, σ (algebraMap F M z) = algebraMap F M z) ∧
        (∀ e ∈ E₀, σ e = e) ∧ σ y ≠ y := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have : IsSepClosed M := IsSepClosure.sep_closed (k := K)
  have : Algebra.IsSeparable K M := IsSepClosure.separable
  have : IsSepClosure F M := ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K F M⟩
  -- the integral closures of `A` and of `R` agree in `M`
  let f : integralClosure R M →+* integralClosure A M :=
    { toFun := fun y => ⟨y, isIntegral_trans (R := A) (A := R) _ y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun b => ⟨⟨b, b.2.tower_top⟩, rfl⟩
  let Pb : Ideal (integralClosure R M) := P.comap f
  have : Pb.IsMaximal := Ideal.comap_isMaximal_of_surjective f hf
  let := IsIntegralClosure.MulSemiringAction R F M (integralClosure R M)
  -- the open subgroup fixing `E₀`
  let b := Module.finBasis K E₀
  let S : Set M := Set.range fun i => ((b i : E₀) : M)
  have : Finite S := (Set.finite_range _).to_subtype
  let E' : IntermediateField F M := IntermediateField.adjoin F S
  have : FiniteDimensional F E' := IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact ((Algebra.IsIntegral.isIntegral (R := K) (b i)).map E₀.val).tower_top
  obtain ⟨N, hN⟩ := exists_forall_exists_mem_inertia_mem_ne R F M p Pb hπ
    E'.fixingSubgroup E'.fixingSubgroup_isOpen
  refine ⟨N, fun n u hn hpn hu y hy => ?_⟩
  have hπM : algebraMap F M (algebraMap R F (algebraMap A R π)) =
      algebraMap K M (algebraMap A K π) := by
    rw [← IsScalarTower.algebraMap_apply R F M, ← IsScalarTower.algebraMap_apply A R M,
      IsScalarTower.algebraMap_apply A K M]
  have hy' : y ^ p - y = algebraMap F M ((algebraMap R F (algebraMap A R π))⁻¹ ^ n *
      algebraMap R F u) := by
    rw [hy, map_mul, map_pow, map_inv₀, hπM, ← IsScalarTower.algebraMap_apply R F M]
  obtain ⟨σ, hσI, hσU, hσy⟩ := hN n u hn hpn hu y hy'
  refine ⟨σ.restrictScalars K, ?_, fun z => σ.commutes z, fun e he => ?_, hσy⟩
  · rw [Ideal.mem_inertia]
    intro x
    have hx := Ideal.mem_inertia.1 hσI ⟨x, x.2.tower_top⟩
    have heq : f (σ • (⟨x, x.2.tower_top⟩ : integralClosure R M) - ⟨x, x.2.tower_top⟩) =
        σ.restrictScalars K • x - x := by
      apply Subtype.ext
      change (algebraMap (integralClosure R M) M
          (galRestrict R F M _ σ ⟨x, x.2.tower_top⟩) - (x : M)) =
        algebraMap (integralClosure A M) M
          (galRestrict A K M _ (σ.restrictScalars K) x) - (x : M)
      rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
      rfl
    rw [← heq]
    exact hx
  · have hfixS : ∀ i, σ ((b i : E₀) : M) = ((b i : E₀) : M) := fun i =>
      (IntermediateField.mem_fixingSubgroup_iff E' σ).1 hσU _
        (IntermediateField.subset_adjoin F S ⟨i, rfl⟩)
    have hsum := congrArg E₀.val (b.sum_repr ⟨e, he⟩)
    rw [map_sum] at hsum
    simp only [map_smul] at hsum
    change _ = e at hsum
    rw [← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    exact congrArg _ (hfixS i)

end Generic

section Model

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K] [Finite (IsLocalRing.ResidueField A)]
  (k : Type*) [Field k] [Finite k] [Algebra k K]
  (M : Type*) [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M] [Algebra k M]
  [IsScalarTower k K M] [IsSepClosure K M] (p : ℕ) [Fact p.Prime] [CharP K p]

variable {M} in
/-- An element algebraic over a finite field is integral over `ℤ`. -/
theorem isIntegral_int_of_isAlgebraic {z : M} (hz : IsAlgebraic k z) : IsIntegral ℤ z := by
  have : FiniteDimensional k (IntermediateField.adjoin k {z}) :=
    IntermediateField.adjoin.finiteDimensional hz.isIntegral
  have : Finite (IntermediateField.adjoin k {z}) := Module.finite_of_finite k
  exact (IsIntegral.of_finite ℤ (⟨z, IntermediateField.mem_adjoin_simple_self k z⟩ :
    IntermediateField.adjoin k {z})).map (IntermediateField.adjoin k {z}).val.toRingHom.toIntAlgHom

/-- **One bound for all constant field extensions.** There is `N` such that for every `n > N`
prime to `p`, all constants `a ≠ 0` and `c` of `M` (elements algebraic over `k`) and every root `y`
of `y ^ p - y = a π ^ (-n) + c π ^ (-1)`, some element of the inertia group of `P` fixing every
constant and a given finite subextension `E₀` moves `y`. Over the integral closure `Ā` of `A` in
`K̄ = K(constants)` (a discrete valuation ring with uniformizer `π` and perfect residue field),
`a π ^ (-n) + c π ^ (-1) = π ^ (-n) (a + c π ^ (n - 1))` with `a + c π ^ (n - 1)` a unit. -/
theorem exists_forall_exists_mem_inertia_ne_of_isAlgebraic
    (hk : Nat.card (IsLocalRing.ResidueField A) ≤ Nat.card k) {π : A} (hπ : Irreducible π)
    (P : Ideal (integralClosure A M)) [P.IsMaximal] (E₀ : IntermediateField K M)
    [FiniteDimensional K E₀] :
    letI := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
    ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n → ∀ a c : M, IsAlgebraic k a → IsAlgebraic k c → a ≠ 0 →
      ∀ y : M, y ^ p - y = a * (algebraMap K M (algebraMap A K π))⁻¹ ^ n +
          c * (algebraMap K M (algebraMap A K π))⁻¹ →
        ∃ σ ∈ P.inertia Gal(M/K), (∀ z : M, IsAlgebraic k z → σ z = z) ∧ (∀ e ∈ E₀, σ e = e) ∧
          σ y ≠ y := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
  obtain ⟨hirr, hdvr⟩ := constantClosure_dvr A K (k := k) (M := M) hk hπ
  have := hdvr
  have := isFractionRing_constantClosure A K (k := k) (M := M)
  have := perfectField_residueField_constantClosure A K (k := k) (M := M) p hk
  have hAB : IsScalarTower A (integralClosure A (constantClosure K k M)) M :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply (integralClosure A (constantClosure K k M))
        (constantClosure K k M) M, ← IsScalarTower.algebraMap_apply A
          (integralClosure A (constantClosure K k M)) (constantClosure K k M),
        IsScalarTower.algebraMap_apply A K (constantClosure K k M),
        ← IsScalarTower.algebraMap_apply K (constantClosure K k M) M,
        ← IsScalarTower.algebraMap_apply A K M]
  obtain ⟨N, hN⟩ := exists_forall_exists_mem_inertia_ne_of_dvr A K M p (constantClosure K k M)
    (integralClosure A (constantClosure K k M)) hirr P E₀
  refine ⟨N + 1, fun n hn hpn a c ha hc ha0 y hy => ?_⟩
  have hmem : ∀ z : M, IsAlgebraic k z → z ∈ constantClosure K k M := fun z hz =>
    IntermediateField.subset_adjoin _ _ (mem_algebraicClosure_iff.2 hz)
  have hint : ∀ (z : M) (hz : IsAlgebraic k z),
      IsIntegral A (⟨z, hmem z hz⟩ : constantClosure K k M) := fun z hz =>
    ((isIntegral_algHom_iff (constantClosure K k M).val.toRingHom.toIntAlgHom
      (constantClosure K k M).val.injective (x := ⟨z, hmem z hz⟩)).1
        (isIntegral_int_of_isAlgebraic k hz)).tower_top
  let elt : ∀ z : M, IsAlgebraic k z → integralClosure A (constantClosure K k M) :=
    fun z hz => ⟨⟨z, hmem z hz⟩, hint z hz⟩
  have ha' : IsUnit (elt a ha) := by
    refine IsUnit.of_mul_eq_one (elt a⁻¹ ha.inv) (Subtype.ext (Subtype.ext ?_))
    exact mul_inv_cancel₀ ha0
  set π' := algebraMap A (integralClosure A (constantClosure K k M)) π
  set u := elt a ha + elt c hc * π' ^ (n - 1) with hu_def
  have hu : IsUnit u := isUnit_add_mul_pow _ hirr ha' _ (by omega)
  have hπM : algebraMap (constantClosure K k M) M
      (algebraMap (integralClosure A (constantClosure K k M)) (constantClosure K k M) π') =
        algebraMap K M (algebraMap A K π) := by
    change algebraMap (constantClosure K k M) M (algebraMap A (constantClosure K k M) π) = _
    rw [IsScalarTower.algebraMap_apply A K (constantClosure K k M),
      ← IsScalarTower.algebraMap_apply K (constantClosure K k M) M]
  have hy' : y ^ p - y = (algebraMap K M (algebraMap A K π))⁻¹ ^ n *
      algebraMap (integralClosure A (constantClosure K k M)) M u := by
    have key := mul_inv_pow_add_mul_inv_eq (integralClosure A (constantClosure K k M))
      (constantClosure K k M) hirr (elt a ha) (elt c hc) (n := n) (by omega)
    have key' := congrArg (algebraMap (constantClosure K k M) M) key
    simp only [map_add, map_mul, map_pow, map_inv₀, hπM] at key'
    have hu_val : algebraMap (integralClosure A (constantClosure K k M)) M u =
        a + c * (algebraMap K M (algebraMap A K π)) ^ (n - 1) := by
      change algebraMap (constantClosure K k M) M
        (algebraMap (integralClosure A (constantClosure K k M)) (constantClosure K k M) u) = _
      rw [hu_def]
      simp only [map_add, map_mul, map_pow, hπM]
      rfl
    rw [hy, hu_val]
    exact key'
  obtain ⟨σ, hσI, hσK, hσE, hσy⟩ := hN n u (by omega) hpn hu y hy'
  exact ⟨σ, hσI, fun z hz => hσK ⟨z, hmem z hz⟩, hσE, hσy⟩

end Model

section Transport

open scoped Pointwise

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The Galois action on the integral closure of `A` in an algebraic extension `M / K` is
continuous for the discrete topology: the stabilizer of `x` contains the fixing subgroup of
`K(x)`. -/
theorem continuousSMul_integralClosure (M : Type*) [Field M] [Algebra K M] [Algebra A M]
    [IsScalarTower A K M] [Algebra.IsAlgebraic K M] [TopologicalSpace (integralClosure A M)]
    [DiscreteTopology (integralClosure A M)] :
    letI := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
    ContinuousSMul Gal(M/K) (integralClosure A M) := by
  let := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  have : FiniteDimensional K (IntermediateField.adjoin K {(x : M)}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (x : M))
  refine Subgroup.isOpen_mono (fun σ hσ => ?_)
    (IntermediateField.adjoin K {(x : M)}).fixingSubgroup_isOpen
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  change algebraMap (integralClosure A M) M (galRestrict A K M _ σ x) = (x : M)
  rw [algebraMap_galRestrict_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ _
    (IntermediateField.mem_adjoin_simple_self K _)

/-- The elements of the integral closure of `A` in a Galois extension `M / K` fixed by
`Gal(M/K)` come from `A`. -/
theorem isInvariant_integralClosure (M : Type*) [Field M] [Algebra K M] [Algebra A M]
    [IsScalarTower A K M] [IsGalois K M] :
    letI := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
    Algebra.IsInvariant A (integralClosure A M) Gal(M/K) := by
  let := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Gal(M/K), σ (b : M) = b := fun σ => by
    have h := congrArg (fun z : integralClosure A M => (z : M)) (hb σ)
    change algebraMap (integralClosure A M) M (galRestrict A K M _ σ b) = _ at h
    rwa [algebraMap_galRestrict_apply] at h
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : M)).2 hfix
  have hcint : IsIntegral A c := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K M) (algebraMap K M).injective).1 ?_
    change IsIntegral A (algebraMap K M c)
    rw [hc]
    exact b.2
  obtain ⟨a, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).1 hcint
  refine ⟨a, Subtype.ext ?_⟩
  change algebraMap A M a = (b : M)
  rw [← hc, IsScalarTower.algebraMap_apply A K M]

/-- **Any two separable closures of `K` with maximal ideals over `A` are isomorphic**: there is a
`K`-isomorphism `ι : M₁ ≃ M₂` carrying `P₁` to `P₂`. `IsSepClosure.equiv` gives one isomorphism,
and the Galois group of `M₂ / K`, profinite, acts transitively on the maximal ideals over the
maximal ideal of `A` (`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`). -/
theorem exists_algEquiv_mem_iff (M₁ M₂ : Type*) [Field M₁] [Algebra K M₁] [Algebra A M₁]
    [IsScalarTower A K M₁] [IsSepClosure K M₁] [Field M₂] [Algebra K M₂] [Algebra A M₂]
    [IsScalarTower A K M₂] [IsSepClosure K M₂] (P₁ : Ideal (integralClosure A M₁)) [P₁.IsMaximal]
    (P₂ : Ideal (integralClosure A M₂)) [P₂.IsMaximal] :
    ∃ ι : M₁ ≃ₐ[K] M₂, ∀ (x : M₁) (hx : IsIntegral A x),
      (⟨x, hx⟩ : integralClosure A M₁) ∈ P₁ ↔
        (⟨ι x, hx.map ((ι : M₁ →ₐ[K] M₂).restrictScalars A)⟩ : integralClosure A M₂) ∈ P₂ := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K M₂ (integralClosure A M₂)
  let ι₀ : M₁ ≃ₐ[K] M₂ := IsSepClosure.equiv K M₁ M₂
  let e₀ : integralClosure A M₁ ≃+* integralClosure A M₂ :=
    { toFun := fun x => ⟨ι₀ x, x.2.map ((ι₀ : M₁ →ₐ[K] M₂).restrictScalars A)⟩
      invFun := fun y => ⟨ι₀.symm y, y.2.map ((ι₀.symm : M₂ →ₐ[K] M₁).restrictScalars A)⟩
      left_inv := fun x => Subtype.ext (ι₀.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (ι₀.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (map_mul ι₀ (x : M₁) y)
      map_add' := fun x y => Subtype.ext (map_add ι₀ (x : M₁) y) }
  let Q : Ideal (integralClosure A M₂) := P₁.comap e₀.symm.toRingHom
  have : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e₀.symm.surjective
  have hQ : Q.under A = P₂.under A :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A Q)).trans
      (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P₂)).symm
  let : TopologicalSpace (integralClosure A M₂) := ⊥
  have : DiscreteTopology (integralClosure A M₂) := ⟨rfl⟩
  have := continuousSMul_integralClosure A K M₂
  have := isInvariant_integralClosure A K M₂
  have : SMulCommClass Gal(M₂/K) A (integralClosure A M₂) :=
    ⟨fun σ a b => by
      change galRestrict A K M₂ (integralClosure A M₂) σ (a • b) =
        a • galRestrict A K M₂ (integralClosure A M₂) σ b
      exact map_smul (galRestrict A K M₂ (integralClosure A M₂) σ) a b⟩
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G := Gal(M₂/K)) Q P₂ hQ
  refine ⟨ι₀.trans g, fun x hx => ?_⟩
  rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change _ ↔ e₀.symm (g⁻¹ • _) ∈ P₁
  have he : e₀.symm (g⁻¹ • (⟨(ι₀.trans g) x, hx.map
      (((ι₀.trans g) : M₁ →ₐ[K] M₂).restrictScalars A)⟩ : integralClosure A M₂)) = ⟨x, hx⟩ := by
    apply Subtype.ext
    change ι₀.symm (algebraMap (integralClosure A M₂) M₂ (galRestrict A K M₂ _ g⁻¹ _)) = x
    rw [algebraMap_galRestrict_apply]
    change ι₀.symm (g⁻¹ (g (ι₀ x))) = x
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply, AlgEquiv.symm_apply_apply]
  rw [he]

end Transport

section Descent

/-- The image of a finite field `k' ⊇ k` in an extension `K'` of `K ⊇ k` is integral over `K`. -/
theorem isIntegral_algebraMap_of_finite (k K : Type*) {k' K' : Type*} [Field k] [Finite k]
    [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field K'] [Algebra K K'] [Algebra k' K']
    [Algebra k K] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K'] (z : k') :
    IsIntegral K (algebraMap k' K' z) :=
  ((Algebra.IsIntegral.isIntegral (R := k) z).map (IsScalarTower.toAlgHom k k' K')).tower_top

/-- A field `K' = K(k')` generated over `K` by a finite field `k' ⊇ k` is finite over `K`. -/
theorem finiteDimensional_of_adjoin_range_eq_top (k : Type*) {k' K K' : Type*} [Field k]
    [Finite k] [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field K'] [Algebra K K']
    [Algebra k' K'] [Algebra k K] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (hK' : IntermediateField.adjoin K (Set.range (algebraMap k' K')) = ⊤) :
    FiniteDimensional K K' := by
  have : FiniteDimensional K (IntermediateField.adjoin K (Set.range (algebraMap k' K'))) :=
    finiteDimensional_adjoin_range_of_finite (IsScalarTower.toAlgHom k k' K')
  rw [hK'] at this
  exact (IntermediateField.topEquiv (F := K) (E := K')).toLinearEquiv.finiteDimensional

/-- A field `K' = K(k')` generated over `K` by a finite field `k' ⊇ k` is separable over `K`. -/
theorem isSeparable_of_adjoin_range_eq_top (k : Type*) {k' K K' : Type*} [Field k] [Finite k]
    [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field K'] [Algebra K K'] [Algebra k' K']
    [Algebra k K] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (hK' : IntermediateField.adjoin K (Set.range (algebraMap k' K')) = ⊤) :
    Algebra.IsSeparable K K' := by
  have hS : Algebra.IsSeparable K (IntermediateField.adjoin K (Set.range (algebraMap k' K'))) :=
    isSeparable_adjoin_range_of_finite (IsScalarTower.toAlgHom k k' K')
  refine ⟨fun x => ?_⟩
  have hx : x ∈ IntermediateField.adjoin K (Set.range (algebraMap k' K')) := by
    rw [hK']
    trivial
  exact (Algebra.IsSeparable.isSeparable K (⟨x, hx⟩ :
    IntermediateField.adjoin K (Set.range (algebraMap k' K')))).map
      (f := (IntermediateField.adjoin K (Set.range (algebraMap k' K'))).val) Subtype.val_injective

/-- If `K' = K(k')` for a finite field `k' ⊇ k`, then `c ^ [K' : K] ≤ |k'|` whenever `c ≤ |k|`,
since `[K' : K] ≤ [k' : k]`. -/
theorem pow_finrank_le_card_of_adjoin_range_eq_top {k k' K K' : Type*} [Field k] [Finite k]
    [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field K'] [Algebra K K'] [Algebra k' K']
    [Algebra k K] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K'] {c : ℕ}
    (hc : c ≤ Nat.card k) (hK' : IntermediateField.adjoin K (Set.range (algebraMap k' K')) = ⊤) :
    c ^ Module.finrank K K' ≤ Nat.card k' := by
  have h : c ^ Module.finrank K (IntermediateField.adjoin K (Set.range (algebraMap k' K'))) ≤
      Nat.card k' := pow_finrank_adjoin_range_le_card hc (IsScalarTower.toAlgHom k k' K')
  rwa [hK', IntermediateField.finrank_top'] at h

/-- A `K`-automorphism of an extension `L` of `K' = K(k')` fixing the image of the finite field
`k' ⊇ k` fixes `K'`. -/
theorem apply_algebraMap_eq_of_adjoin_range_eq_top (k : Type*) {k' K K' L : Type*} [Field k]
    [Finite k] [Field k'] [Finite k'] [Algebra k k'] [Field K] [Field K'] [Algebra K K']
    [Algebra k' K'] [Algebra k K] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
    (hK' : IntermediateField.adjoin K (Set.range (algebraMap k' K')) = ⊤) (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : k', σ (algebraMap K' L (algebraMap k' K' z)) = algebraMap K' L (algebraMap k' K' z))
    (x : K') : σ (algebraMap K' L x) = algebraMap K' L x := by
  have halg : ∀ x ∈ Set.range (algebraMap k' K'), IsAlgebraic K x := by
    rintro _ ⟨z, rfl⟩
    exact (isIntegral_algebraMap_of_finite k K z).isAlgebraic
  have hadj : Algebra.adjoin K (Set.range (algebraMap k' K')) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, hK',
      IntermediateField.top_toSubalgebra]
  refine DFunLike.congr_fun (AlgHom.ext_of_adjoin_eq_top hadj
    (φ₁ := (σ : L →ₐ[K] L).comp (IsScalarTower.toAlgHom K K' L))
    (φ₂ := IsScalarTower.toAlgHom K K' L) ?_) x
  rintro _ ⟨z, rfl⟩
  exact hσ z

/-- **A discrete valuation ring of an inert extension dominating `A` is integral over `A`.** If
`|κ| ^ [K' : K] ≤ |k'|` for a finite field `k' ⊆ K'`, the integral closure of `A` in `K'` is a
discrete valuation ring with uniformizer `π`; a discrete valuation ring `A'` of `K'` containing
`A` in which `π` is not a unit dominates it, hence equals it. -/
theorem algebra_isIntegral_of_dominates (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Finite (IsLocalRing.ResidueField A)] {k' K' A' : Type*} [Field k'] [Finite k'] [Field K']
    [Algebra K K'] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] [Algebra A K']
    [IsScalarTower A K K'] [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Algebra A' K'] [IsFractionRing A' K'] [Algebra A A'] [IsScalarTower A A' K'] (φ : k' →+* K')
    (hcard : Nat.card (IsLocalRing.ResidueField A) ^ Module.finrank K K' ≤ Nat.card k')
    {π : A} (hπ : Irreducible π)
    (hπA : ∀ b : A', algebraMap A' K' b = algebraMap A K' π → b ∈ IsLocalRing.maximalIdeal A') :
    Algebra.IsIntegral A A' := by
  have := isDiscreteValuationRing_integralClosure_of_card_pow_le A K K' φ hcard
  have hπR := irreducible_algebraMap_integralClosure_of_card_pow_le A K K' φ hcard hπ
  have : IsFractionRing (integralClosure A K') K' :=
    integralClosure.isFractionRing_of_finite_extension K K'
  have hRS : ∀ r : integralClosure A K', algebraMap (integralClosure A K') K' r ∈
      Set.range (algebraMap A' K') := fun r =>
    (IsIntegrallyClosed.isIntegral_iff (R := A') (K := K')).1 r.2.tower_top
  have hA' : ∀ b : A', IsIntegral A (algebraMap A' K' b) := fun b => by
    obtain ⟨r, hr⟩ := mem_range_of_mem_range_of_dominates hRS hπR.ne_zero
      ((IsLocalRing.mem_maximalIdeal _).2 hπR.not_isUnit) (fun s hs => hπA s hs) b
    rw [← hr]
    exact r.2
  exact ⟨fun b => (isIntegral_algHom_iff (IsScalarTower.toAlgHom A A' K')
    (IsFractionRing.injective A' K')).1 (hA' b)⟩

/-- **Matching maximal ideals across a separable closure of an extension.** Let `A'` be integral
over `A`, `K' / K` separable, `L` a separable closure of `K'` and `P` a maximal ideal of the
integral closure of `A'` in `L`. For every separable closure `M` of `K` and maximal ideal `P₀`
over `A`, there is a `K`-isomorphism `ι : L ≃ M` carrying `P` to `P₀`. -/
theorem exists_algEquiv_mem_iff_of_isIntegral (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] {A' K' L M : Type*}
    [CommRing A'] [Field K'] [Algebra K K'] [Algebra A K'] [IsScalarTower A K K'] [Algebra A' K']
    [Algebra A A'] [IsScalarTower A A' K'] [Algebra.IsIntegral A A'] [Algebra.IsSeparable K K']
    [Field L] [Algebra K' L] [IsSepClosure K' L] [Algebra A' L] [IsScalarTower A' K' L]
    [Algebra K L] [IsScalarTower K K' L] [Field M] [Algebra K M] [Algebra A M]
    [IsScalarTower A K M] [IsSepClosure K M] (P : Ideal (integralClosure A' L)) [P.IsMaximal]
    (P₀ : Ideal (integralClosure A M)) [P₀.IsMaximal] :
    ∃ (ι : L ≃ₐ[K] M) (hint : ∀ x : integralClosure A' L, IsIntegral A (ι (x : L))),
      ∀ x, x ∈ P ↔ (⟨ι (x : L), hint x⟩ : integralClosure A M) ∈ P₀ := by
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A A' L := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K L (algebraMap A K a) = _
    rw [IsScalarTower.algebraMap_apply A' K' L, ← IsScalarTower.algebraMap_apply A A' K',
      IsScalarTower.algebraMap_apply A K K', ← IsScalarTower.algebraMap_apply K K' L]
  have hA : ∀ x : integralClosure A' L, IsIntegral A (x : L) := fun x =>
    isIntegral_trans (R := A) (A := A') _ x.2
  let f : integralClosure A L →+* integralClosure A' L :=
    { toFun := fun x => ⟨x, x.2.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : (P.comap f).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective f fun x => ⟨⟨x, hA x⟩, rfl⟩
  have : Algebra.IsSeparable K' L := IsSepClosure.separable
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.trans K K' L
  have : IsSepClosure K L := ⟨IsSepClosure.sep_closed (k := K'), inferInstance⟩
  obtain ⟨ι, hι⟩ := exists_algEquiv_mem_iff A K L M (P.comap f) P₀
  exact ⟨ι, fun x => (hA x).map ((ι : L →ₐ[K] M).restrictScalars A), fun x => hι x (hA x)⟩

/-- An element `σ` of `Gal(L/K')` corresponding under `ι : L ≃ M` to an element `σ₀` of the
inertia group of `P₀` lies in the inertia group of `P`, if `ι` carries `P` to `P₀`. -/
theorem mem_inertia_of_apply_eq (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] {A' K' L M : Type*}
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
    [IsFractionRing A' K'] [Algebra K K'] [Field L] [Algebra K' L] [Algebra.IsAlgebraic K' L]
    [Algebra A' L] [IsScalarTower A' K' L] [Algebra K L] [Field M] [Algebra K M]
    [Algebra.IsAlgebraic K M] [Algebra A M] [IsScalarTower A K M]
    {P : Ideal (integralClosure A' L)} {P₀ : Ideal (integralClosure A M)} {ι : L ≃ₐ[K] M}
    {hint : ∀ x : integralClosure A' L, IsIntegral A (ι (x : L))}
    (hι : ∀ x, x ∈ P ↔ (⟨ι (x : L), hint x⟩ : integralClosure A M) ∈ P₀) {σ₀ : Gal(M/K)}
    {σ : Gal(L/K')} (hσ : ∀ w, ι (σ w) = σ₀ (ι w)) :
    letI := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
    letI := IsIntegralClosure.MulSemiringAction A' K' L (integralClosure A' L)
    σ₀ ∈ P₀.inertia Gal(M/K) → σ ∈ P.inertia Gal(L/K') := by
  let := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
  let := IsIntegralClosure.MulSemiringAction A' K' L (integralClosure A' L)
  intro hσ₀
  refine Ideal.mem_inertia.2 fun x => (hι _).2 ?_
  convert Ideal.mem_inertia.1 hσ₀ ⟨ι (x : L), hint x⟩ using 1
  apply Subtype.ext
  change ι (algebraMap (integralClosure A' L) L (galRestrict A' K' L _ σ x) - (x : L)) =
    algebraMap (integralClosure A M) M (galRestrict A K M _ σ₀ ⟨ι (x : L), hint x⟩) - ι x
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply, map_sub, hσ]
  rfl

/-- **Transport of inertia to a constant extension.** Let `ι : L ≃ M` be a `K`-isomorphism from an
algebraic extension `L` of `K' = K(k')` carrying `P` to `P₀`. An element `σ₀` of the inertia group
of `P₀` fixing the image of `k'` and a set `E₀` comes from an element `σ` of the inertia group of
`P` in `Gal(L/K')` fixing `ι⁻¹(E₀)`, with `ι ∘ σ = σ₀ ∘ ι`. -/
theorem exists_mem_inertia_inf_fixingSubgroup_apply_eq (A K k : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field k] [Finite k]
    [Algebra k K] {k' A' K' L M : Type*} [Field k'] [Finite k'] [Algebra k k'] [CommRing A']
    [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra K K'] [Algebra k' K'] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Field L] [Algebra K' L] [Algebra.IsAlgebraic K' L] [Algebra A' L] [IsScalarTower A' K' L]
    [Algebra K L] [IsScalarTower K K' L] [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]
    [Algebra A M] [IsScalarTower A K M]
    (hK' : IntermediateField.adjoin K (Set.range (algebraMap k' K')) = ⊤)
    (P : Ideal (integralClosure A' L)) (P₀ : Ideal (integralClosure A M)) (ι : L ≃ₐ[K] M)
    (hint : ∀ x : integralClosure A' L, IsIntegral A (ι (x : L)))
    (hι : ∀ x, x ∈ P ↔ (⟨ι (x : L), hint x⟩ : integralClosure A M) ∈ P₀) (E₀ : Set M)
    {σ₀ : Gal(M/K)} (hσ₀k : ∀ z : k', σ₀ (ι (algebraMap K' L (algebraMap k' K' z))) =
      ι (algebraMap K' L (algebraMap k' K' z))) (hσ₀E : ∀ e ∈ E₀, σ₀ e = e) :
    letI := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
    letI := IsIntegralClosure.MulSemiringAction A' K' L (integralClosure A' L)
    σ₀ ∈ P₀.inertia Gal(M/K) → ∃ σ ∈ P.inertia Gal(L/K') ⊓ fixingSubgroup Gal(L/K') (ι.symm '' E₀),
      ∀ w, ι (σ w) = σ₀ (ι w) := by
  let := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
  let := IsIntegralClosure.MulSemiringAction A' K' L (integralClosure A' L)
  intro hσ₀
  let σK : L ≃ₐ[K] L := (ι.trans σ₀).trans ι.symm
  have hσK : ∀ w, ι (σK w) = σ₀ (ι w) := fun w => ι.apply_symm_apply _
  -- `σK` fixes `K' = K(k')`
  let σ : Gal(L/K') := AlgEquiv.ofRingEquiv (f := σK.toRingEquiv)
    (apply_algebraMap_eq_of_adjoin_range_eq_top k hK' σK fun z =>
      ι.injective (by rw [hσK, hσ₀k]))
  have hσ : ∀ w, ι (σ w) = σ₀ (ι w) := hσK
  refine ⟨σ, ⟨mem_inertia_of_apply_eq A K hι hσ hσ₀, ?_⟩, hσ⟩
  change σ ∈ fixingSubgroup Gal(L/K') (ι.symm '' E₀)
  rw [mem_fixingSubgroup_iff]
  rintro _ ⟨e, he, rfl⟩
  apply ι.injective
  change ι (σ (ι.symm e)) = ι (ι.symm e)
  rw [hσ, ι.apply_symm_apply, hσ₀E e he]

end Descent

section Data

open scoped Pointwise

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K] [Finite (IsLocalRing.ResidueField A)]
  (k : Type*) [Field k] [Finite k] [Algebra k K]
  (M : Type*) [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M] [Algebra k M]
  [IsScalarTower k K M] [IsSepClosure K M] (p : ℕ) [Fact p.Prime] [CharP K p]

variable {k} in
omit [Finite k] in
/-- An element fixed by a power `w ↦ w ^ Q`, `Q > 1`, is algebraic over any field. -/
theorem isAlgebraic_of_pow_eq_self {B : Type*} [Field B] [Algebra k B] {w : B} {Q : ℕ}
    (hQ : 1 < Q) (hw : w ^ Q = w) : IsAlgebraic k w :=
  ⟨Polynomial.X ^ Q - Polynomial.X, (Polynomial.monic_X_pow_sub (by
      rw [Polynomial.degree_X]; exact_mod_cast hQ)).ne_zero, by simp [hw]⟩

/-- **The uniform inertia statement for constant field extensions, in any separable closure.**
Fix a model `(M, P₀)` and a finite subextension `E₀`. There is `N` such that for every finite field
`k' ⊇ k`, every field `K' = K(k')`, every discrete valuation ring `A'` of `K'` dominating `A`
(the constant extension of `A` at a place inert over `A`), every separable closure `L` of `K'`
and maximal ideal `P` over `A'`, there is a `K`-isomorphism `ι : L ≃ M` such that for `n > N`
prime to `p`, `a ≠ 0` and `c` in `k'` and every root `t` of `t ^ q' - t = a π ^ (-n) + c π ^ (-1)`,
the character `σ ↦ σ t - t` maps onto `k'` the elements of the inertia group of `P` fixing
`ι⁻¹(E₀)`. The integral closure of `A` in `K'` is a discrete valuation ring dominated by `A'`,
hence equal to it; `ι` is `IsDiscreteValuationRing.exists_algEquiv_mem_iff`; moving roots comes
from `IsDiscreteValuationRing.exists_forall_exists_mem_inertia_ne_of_isAlgebraic` in `M`, and
surjectivity from the trace trick. -/
theorem exists_forall_exists_mem_inertia_sub_eq_of_constantExtension
    (hk : Nat.card (IsLocalRing.ResidueField A) ≤ Nat.card k) {π : A} (hπ : Irreducible π)
    (P₀ : Ideal (integralClosure A M)) [P₀.IsMaximal] (E₀ : IntermediateField K M)
    [FiniteDimensional K E₀] :
    ∃ N : ℕ, ∀ (k' : Type*) [Field k'] [Fintype k'] [Algebra k k'] (K' : Type*) [Field K']
      [Algebra K K'] [Algebra k' K'] [Algebra k K'] [IsScalarTower k k' K']
      [IsScalarTower k K K'],
      IntermediateField.adjoin K (Set.range (algebraMap k' K')) = ⊤ →
      ∀ (A' : Type*) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Algebra A' K']
        [IsFractionRing A' K'],
      (∀ a : A, algebraMap K K' (algebraMap A K a) ∈ Set.range (algebraMap A' K')) →
      (∀ b : A', algebraMap A' K' b = algebraMap K K' (algebraMap A K π) →
        b ∈ IsLocalRing.maximalIdeal A') →
      ∀ (L : Type*) [Field L] [Algebra K' L] [IsSepClosure K' L] [Algebra A' L]
        [IsScalarTower A' K' L] [Algebra K L] [IsScalarTower K K' L]
        (P : Ideal (integralClosure A' L)) [P.IsMaximal],
      letI := IsIntegralClosure.MulSemiringAction A' K' L (integralClosure A' L)
      ∃ ι : L ≃ₐ[K] M, ∀ n : ℕ, N < n → ¬ p ∣ n → ∀ a c : k', a ≠ 0 → ∀ t : L,
        t ^ Fintype.card k' - t = algebraMap K' L (algebraMap k' K' a *
          (algebraMap K K' (algebraMap A K π))⁻¹ ^ n + algebraMap k' K' c *
            (algebraMap K K' (algebraMap A K π))⁻¹) →
        ∀ c₀ : k', ∃ σ ∈ P.inertia Gal(L/K'), (∀ e ∈ E₀, σ (ι.symm e) = ι.symm e) ∧
          σ t - t = algebraMap K' L (algebraMap k' K' c₀) := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K M (integralClosure A M)
  obtain ⟨N, hN⟩ := exists_forall_exists_mem_inertia_ne_of_isAlgebraic A K k M p hk hπ P₀ E₀
  refine ⟨N, fun k' _ _ _ K' _ _ _ _ _ _ hK' A' _ _ _ _ _ hA₀ hπA L _ _ _ _ _ _ _ P _ => ?_⟩
  let := IsIntegralClosure.MulSemiringAction A' K' L (integralClosure A' L)
  -- `K' / K` is finite and separable, of degree at most `[k' : k]`
  have := finiteDimensional_of_adjoin_range_eq_top k hK'
  have := isSeparable_of_adjoin_range_eq_top k hK'
  have : CharP K' p := charP_of_injective_algebraMap (algebraMap K K').injective p
  let : Algebra A K' := ((algebraMap K K').comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- `A → A'`
  let eS : A' ≃+* (algebraMap A' K').range := RingEquiv.ofBijective (algebraMap A' K').rangeRestrict
    ⟨fun a b h => IsFractionRing.injective A' K' (congrArg Subtype.val h),
      (algebraMap A' K').rangeRestrict_surjective⟩
  let : Algebra A A' := (eS.symm.toRingHom.comp ((algebraMap A K').codRestrict
    (algebraMap A' K').range fun a => RingHom.mem_range.2 (hA₀ a))).toAlgebra
  have : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a =>
    (congrArg Subtype.val (eS.apply_symm_apply ⟨_, RingHom.mem_range.2 (hA₀ a)⟩)).symm
  -- the integral closure of `A` in `K'` is a discrete valuation ring, dominated by `A'`
  have := algebra_isIntegral_of_dominates A K (algebraMap k' K')
    (pow_finrank_le_card_of_adjoin_range_eq_top hk hK') hπ hπA
  -- the integral closures of `A` and `A'` in `L` agree
  obtain ⟨ι, hint, hι⟩ := exists_algEquiv_mem_iff_of_isIntegral A K (K' := K') P P₀
  refine ⟨ι, fun n hn hpn a c ha0 t ht c₀ => ?_⟩
  -- constants of `L` go to constants of `M`
  have hconst : ∀ z : k', IsAlgebraic k (ι (algebraMap K' L (algebraMap k' K' z))) := fun z =>
    isAlgebraic_of_pow_eq_self Fintype.one_lt_card (by rw [← map_pow, ← map_pow, ← map_pow,
      FiniteField.pow_card])
  let H : Subgroup Gal(L/K') :=
    P.inertia Gal(L/K') ⊓ fixingSubgroup Gal(L/K') (ι.symm '' (E₀ : Set M))
  have hH : ∀ b : k', b ≠ 0 → ∀ z : L, z ^ p - z = algebraMap K' L (algebraMap k' K' b *
      (algebraMap k' K' a * (algebraMap K K' (algebraMap A K π))⁻¹ ^ n + algebraMap k' K' c *
        (algebraMap K K' (algebraMap A K π))⁻¹)) → ∃ σ ∈ H, σ z ≠ z := by
    intro b hb z hz
    have hz' : ι z ^ p - ι z = ι (algebraMap K' L (algebraMap k' K' (b * a))) *
        (algebraMap K M (algebraMap A K π))⁻¹ ^ n + ι (algebraMap K' L (algebraMap k' K' (b * c))) *
          (algebraMap K M (algebraMap A K π))⁻¹ := by
      rw [← map_pow ι, ← map_sub ι, hz, ← ι.commutes, IsScalarTower.algebraMap_apply K K' L]
      simp only [map_mul, map_add, map_pow, map_inv₀]
      ring
    have hba : ι (algebraMap K' L (algebraMap k' K' (b * a))) ≠ 0 := by
      rw [map_ne_zero_iff _ ι.injective, map_ne_zero_iff _ (algebraMap K' L).injective,
        map_ne_zero_iff _ (algebraMap k' K').injective]
      exact mul_ne_zero hb ha0
    obtain ⟨σ₀, hσ₀I, hσ₀k, hσ₀E, hσ₀z⟩ := hN n hn hpn _ _ (hconst (b * a)) (hconst (b * c)) hba
      (ι z) hz'
    obtain ⟨σ, hσH, hσ⟩ := exists_mem_inertia_inf_fixingSubgroup_apply_eq A K k hK' P P₀ ι hint
      hι E₀ (fun z => hσ₀k _ (hconst z)) hσ₀E hσ₀I
    exact ⟨σ, hσH, fun h => hσ₀z (by rw [← hσ, h])⟩
  obtain ⟨σ, ⟨hσI, hσF⟩, hσt⟩ := forall_exists_mem_sub_eq_of_forall_exists_ne p k' H _ hH t ht c₀
  exact ⟨σ, hσI, fun e he => (mem_fixingSubgroup_iff _).1 hσF _ ⟨e, he, rfl⟩, hσt⟩

end Data

end IsDiscreteValuationRing

end
