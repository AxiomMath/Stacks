module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.KummerTame

/-!
# The Kummer tower of `𝐆_m` over a finite field

Let `k` be a finite field with `q` elements and `Ω` the algebraically closed field of the
geometric generic point `η̄` of `𝐆_{m,k}`, with `x ∈ Ω` the image of the coordinate. For `f ≥ 1`
let `𝔽_f = {a ∈ Ω | a^{q^f} = a}` be the field with `q^f` elements inside `Ω`. With `f_m = m!`
and `N_m = q^{f_m} - 1`, this file constructs compatible choices of `N_m`-th roots `t_m` of `x`
and of primitive `N_m`-th roots of unity `ζ_m` in `Ω`, satisfying
`t_{m+1}^{N_{m+1}/N_m} = t_m` and `ζ_{m+1}^{N_{m+1}/N_m} = ζ_m`.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.Omega`: the field `Ω` of the geometric generic
  point of `𝐆_{m,k}`.
* `AlgebraicGeometry.TameMultiplicativeGroup.baseHom`: the map `k[x]_x → Ω`.
* `AlgebraicGeometry.TameMultiplicativeGroup.frobField`: the field `𝔽_f ⊆ Ω`.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerN`: the integer `N_m = q^{m!} - 1`.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerZeta`: the primitive `N_m`-th root of unity
  `ζ_m`.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerRoot`: the `N_m`-th root `t_m` of `x`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.baseHom_injective`: the map `k[x]_x → Ω` is
  injective.
* `AlgebraicGeometry.TameMultiplicativeGroup.transcendental_xΩ`: `x ∈ Ω` is transcendental
  over `k`.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerZeta_succ_pow`: `ζ_{m+1}^{N_{m+1}/N_m} = ζ_m`.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerRoot_succ_pow`: `t_{m+1}^{N_{m+1}/N_m} = t_m`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable (k : Type u) [Field k]

/-- The algebraically closed field `Ω` of the geometric generic point of `𝐆_{m,k}`. -/
abbrev Omega : Type u := (genericGeometricPoint k).residueField

/-- **The base map** `k[x]_x → Ω` of the geometric generic point. -/
def baseHom : Ring k →+* Omega k := (Spec.preimage (genericGeometricPoint k).hom).hom

/-- The morphism `Spec Ω → 𝐆_{m,k}` induced by `baseHom k` is the geometric generic point. -/
theorem specMap_baseHom :
    Spec.map (CommRingCat.ofHom (baseHom k)) = (genericGeometricPoint k).hom := by
  rw [baseHom, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The base map is injective: the geometric generic point lies over the generic point. -/
theorem baseHom_injective : Function.Injective (baseHom k) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hlies := GeometricPoint.ofPoint_liesOver (Gm k) (genericPoint (Gm k))
  change (genericGeometricPoint k).hom default = genericPoint (Gm k) at hlies
  rw [← specMap_baseHom k, genericPoint_eq_bot_of_affine (CommRingCat.of (Ring k))] at hlies
  have hmem : z ∈ ((Spec.map (CommRingCat.ofHom (baseHom k))).base default).asIdeal :=
    (Ideal.mem_comap (f := baseHom k)).mpr (hz ▸ Ideal.zero_mem _)
  rwa [hlies] at hmem

/-- `Ω` is a `k`-algebra via `k → k[x]_x → Ω`. -/
instance : Algebra k (Omega k) := ((baseHom k).comp (algebraMap k (Ring k))).toAlgebra

/-- The algebra map `k → Ω` is the composite of `k → k[x]_x` with `baseHom k`. -/
theorem algebraMap_omega (a : k) :
    algebraMap k (Omega k) a = baseHom k (algebraMap k (Ring k) a) := rfl

/-- The image `x ∈ Ω` of the coordinate. -/
abbrev xΩ : Omega k := baseHom k (coord k)

/-- The element `x ∈ Ω` is nonzero. -/
theorem xΩ_ne_zero : xΩ k ≠ 0 := ((isUnit_coord k).map _).ne_zero

/-- Evaluating a polynomial `p ∈ k[X]` at `x ∈ Ω` is the image of `p` under `k[X] → k[x]_x → Ω`. -/
theorem aeval_xΩ (p : k[X]) : aeval (xΩ k) p = baseHom k (algebraMap k[X] (Ring k) p) := by
  have : (aeval (xΩ k)).toRingHom = (baseHom k).comp (algebraMap k[X] (Ring k)) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply, algebraMap_C,
        algebraMap_omega]
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact RingHom.congr_fun this p

/-- `x ∈ Ω` is transcendental over `k`. -/
theorem transcendental_xΩ : Transcendental k (xΩ k) := by
  rw [transcendental_iff_injective]
  intro p p' h
  rw [aeval_xΩ, aeval_xΩ] at h
  exact IsLocalization.injective (Ring k) (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)
    (baseHom_injective k h)

/-! ### Roots of unity -/

/-- **Lifting a primitive root of unity.** In an algebraically closed field, every primitive
`N`-th root of unity is the `r`-th power of a primitive `N r`-th root of unity (when `N r` is
invertible). -/
theorem exists_isPrimitiveRoot_pow_eq {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {N r M : ℕ}
    (hM : M = N * r) [NeZero (M : Ω)] (hN : 0 < N) (hr : 0 < r) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) : ∃ ζ' : Ω, IsPrimitiveRoot ζ' M ∧ ζ' ^ r = ζ := by
  have hM0 : 0 < M := hM ▸ Nat.mul_pos hN hr
  have : NeZero M := ⟨hM0.ne'⟩
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hωr : IsPrimitiveRoot (ω ^ r) N := hω.pow hM0 (by rw [hM, mul_comm])
  obtain ⟨j, -, hj⟩ := hωr.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hjcop : j.Coprime N := (hωr.pow_iff_coprime hN j).mp (hj ▸ hζ)
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime j hjcop
  obtain ⟨u', hu'⟩ := ZMod.unitsMap_surjective (n := N) (m := M) (Dvd.intro r hM.symm) u
  set j' := (u' : ZMod M).val
  have hj'cop : j'.Coprime M := ZMod.val_coe_unit_coprime u'
  refine ⟨ω ^ j', hω.pow_of_coprime j' hj'cop, ?_⟩
  have hmod : j' % N = j % N := by
    have h1 : ((j' : ℕ) : ZMod N) = (j : ZMod N) := by
      have := congrArg (fun v : (ZMod N)ˣ ↦ (v : ZMod N)) hu'
      simp only [ZMod.unitsMap_val, u, ZMod.coe_unitOfCoprime] at this
      rw [ZMod.natCast_val, this]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  rw [← pow_mul, mul_comm, pow_mul, pow_eq_pow_mod j' hωr.pow_eq_one, hmod,
    ← pow_eq_pow_mod j hωr.pow_eq_one, hj]

section Finite

variable [Fintype k]

/-- The cardinality `q` of `k` vanishes in `Ω`. -/
theorem natCast_card_omega : ((Fintype.card k : ℕ) : Omega k) = 0 := by
  rw [← map_natCast (algebraMap k (Omega k)), FiniteField.cast_card_eq_zero, map_zero]

/-- **The field `𝔽_f = {a ∈ Ω | a^{q^f} = a}`** with `q^f` elements. -/
def frobField (f : ℕ) : IntermediateField k (Omega k) :=
  { toSubalgebra := AlgHom.equalizer (FiniteField.frobeniusAlgHom k (Omega k) ^ f)
      (AlgHom.id k (Omega k))
    inv_mem' := fun a ha ↦ by
      change (FiniteField.frobeniusAlgHom k (Omega k) ^ f) a⁻¹ = a⁻¹
      rw [map_inv₀]
      exact congrArg (·⁻¹) ha }

/-- An element `a ∈ Ω` lies in `𝔽_f` if and only if `a^{q^f} = a`. -/
theorem mem_frobField {f : ℕ} {a : Omega k} :
    a ∈ frobField k f ↔ a ^ (Fintype.card k ^ f) = a := by
  show (FiniteField.frobeniusAlgHom k (Omega k) ^ f) a = a ↔ _
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

/-- If `f ∣ f'`, then `𝔽_f ⊆ 𝔽_{f'}`. -/
theorem frobField_mono {f f' : ℕ} (h : f ∣ f') : frobField k f ≤ frobField k f' := by
  intro a ha
  rw [mem_frobField] at ha ⊢
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul]
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, pow_mul, ih, ha]

/-- For `f ≠ 0`, the field `𝔽_f` is finite. -/
theorem finite_frobField {f : ℕ} (hf : f ≠ 0) : Finite (frobField k f) := by
  classical
  have hq : 1 < Fintype.card k ^ f := Nat.one_lt_pow hf Fintype.one_lt_card
  have hne := FiniteField.X_pow_card_sub_X_ne_zero (K' := Omega k) hq
  have hsub : ((frobField k f : IntermediateField k (Omega k)) : Set (Omega k)) ⊆
      ((X ^ (Fintype.card k ^ f) - X : (Omega k)[X]).roots.toFinset : Set (Omega k)) := by
    intro a ha
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X,
      sub_eq_zero]
    exact (mem_frobField k).mp ha
  exact Set.finite_coe_iff.mpr ((Finset.finite_toSet _).subset hsub)

/-- For `f ≠ 0`, the field `𝔽_f` is finite. -/
instance (f : ℕ) [NeZero f] : Finite (frobField k f) := finite_frobField k (NeZero.ne f)

/-- For `f ≠ 0`, the field `𝔽_f` is finite-dimensional over `k`. -/
instance (f : ℕ) [NeZero f] : FiniteDimensional k (frobField k f) := Module.Finite.of_finite

/-- For `f ≠ 0`, the field `𝔽_f` is separable over `k`. -/
instance (f : ℕ) [NeZero f] : Algebra.IsSeparable k (frobField k f) := inferInstance

/-- For `f ≠ 0`, every `a ∈ Ω` with `a^{q^f - 1} = 1` lies in `𝔽_f`. -/
theorem mem_frobField_of_pow_eq_one {f : ℕ} (hf : f ≠ 0) {a : Omega k}
    (ha : a ^ (Fintype.card k ^ f - 1) = 1) : a ∈ frobField k f := by
  rw [mem_frobField, ← Nat.sub_add_cancel (Nat.one_le_pow _ _ Fintype.card_pos), pow_succ, ha,
    one_mul]

/-! ### The tower -/

/-- The factorial `m!` is nonzero. -/
instance (m : ℕ) : NeZero m.factorial := ⟨Nat.factorial_ne_zero m⟩

/-- The modulus `N_m = q^{m!} - 1`. -/
abbrev towerN (m : ℕ) : ℕ := Fintype.card k ^ m.factorial - 1

/-- The ratio `N_{m+1} / N_m`. -/
abbrev towerRatio (m : ℕ) : ℕ := towerN k (m + 1) / towerN k m

/-- For every `m`, `1 < q^{m!}`. -/
theorem one_lt_card_pow (m : ℕ) : 1 < Fintype.card k ^ m.factorial :=
  Nat.one_lt_pow (Nat.factorial_ne_zero m) Fintype.one_lt_card

/-- The integer `N_m` is positive. -/
theorem towerN_pos (m : ℕ) : 0 < towerN k m := Nat.sub_pos_of_lt (one_lt_card_pow k m)

/-- `N_m` divides `N_{m+1}`. -/
theorem towerN_dvd (m : ℕ) : towerN k m ∣ towerN k (m + 1) := by
  have h := Nat.sub_one_dvd_pow_sub_one (x := Fintype.card k ^ m.factorial) (n := m + 1)
  rwa [← pow_mul, mul_comm, ← Nat.factorial_succ] at h

/-- `N_{m+1} = N_m · (N_{m+1} / N_m)`. -/
theorem towerN_mul_ratio (m : ℕ) : towerN k (m + 1) = towerN k m * towerRatio k m :=
  (Nat.mul_div_cancel' (towerN_dvd k m)).symm

/-- The ratio `N_{m+1} / N_m` is positive. -/
theorem towerRatio_pos (m : ℕ) : 0 < towerRatio k m :=
  Nat.div_pos (Nat.le_of_dvd (towerN_pos k (m + 1)) (towerN_dvd k m)) (towerN_pos k m)

/-- In any `k`-algebra, `N_m` maps to `-1`. -/
theorem natCast_towerN {R : Type*} [CommRing R] [Algebra k R] (m : ℕ) :
    ((towerN k m : ℕ) : R) = -1 := by
  rw [Nat.cast_sub (one_lt_card_pow k m).le, Nat.cast_pow, ← map_natCast (algebraMap k R),
    FiniteField.cast_card_eq_zero, map_zero, zero_pow (Nat.factorial_ne_zero m), Nat.cast_one,
    zero_sub]

/-- `N_m` is a unit in `k`. -/
theorem isUnit_towerN (m : ℕ) : IsUnit ((towerN k m : ℕ) : k) := by
  rw [natCast_towerN k (R := k) m]
  exact isUnit_one.neg

/-- `N_m` is nonzero in `Ω`. -/
instance (m : ℕ) : NeZero ((towerN k m : ℕ) : Omega k) :=
  ⟨by
    rw [natCast_towerN k (R := Omega k) m]
    exact neg_ne_zero.mpr one_ne_zero⟩

/-- If `t^{N_m} = x` and `t'^{N_{m+1}/N_m} = t`, then `t'^{N_{m+1}} = x`. -/
theorem pow_towerN_succ (m : ℕ) {t t' : Omega k} (h1 : t' ^ towerRatio k m = t)
    (h2 : t ^ towerN k m = xΩ k) : t' ^ towerN k (m + 1) = xΩ k := by
  rw [towerN_mul_ratio k m, mul_comm, pow_mul, h1, h2]

/-- The compatible roots `(ζ_m, t_m)`: `ζ_m` a primitive `N_m`-th root of unity and
`t_m^{N_m} = x`, with `ζ_{m+1}^{N_{m+1}/N_m} = ζ_m` and `t_{m+1}^{N_{m+1}/N_m} = t_m`. -/
def towerData : (m : ℕ) →
    {p : Omega k × Omega k // IsPrimitiveRoot p.1 (towerN k m) ∧ p.2 ^ towerN k m = xΩ k}
  | 0 => ⟨(Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot (Omega k) (towerN k 0)),
      Classical.choose (IsAlgClosed.exists_pow_nat_eq (xΩ k) (towerN_pos k 0))),
      Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot (Omega k) (towerN k 0)),
      Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (xΩ k) (towerN_pos k 0))⟩
  | m + 1 =>
    ⟨(Classical.choose (exists_isPrimitiveRoot_pow_eq (towerN_mul_ratio k m) (towerN_pos k m)
        (towerRatio_pos k m) (towerData m).2.1),
      Classical.choose (IsAlgClosed.exists_pow_nat_eq (towerData m).1.2 (towerRatio_pos k m))),
      (Classical.choose_spec (exists_isPrimitiveRoot_pow_eq (towerN_mul_ratio k m) (towerN_pos k m)
        (towerRatio_pos k m) (towerData m).2.1)).1,
      pow_towerN_succ k m (Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (towerData m).1.2
        (towerRatio_pos k m))) (towerData m).2.2⟩

/-- The primitive `N_m`-th root of unity `ζ_m`. -/
def towerZeta (m : ℕ) : Omega k := (towerData k m).1.1

/-- The `N_m`-th root `t_m` of `x`. -/
def towerRoot (m : ℕ) : Omega k := (towerData k m).1.2

/-- `ζ_m` is a primitive `N_m`-th root of unity. -/
theorem isPrimitiveRoot_towerZeta (m : ℕ) : IsPrimitiveRoot (towerZeta k m) (towerN k m) :=
  (towerData k m).2.1

/-- `t_m^{N_m} = x`. -/
theorem towerRoot_pow (m : ℕ) : towerRoot k m ^ towerN k m = xΩ k := (towerData k m).2.2

/-- `ζ_{m+1}^{N_{m+1}/N_m} = ζ_m`. -/
theorem towerZeta_succ_pow (m : ℕ) : towerZeta k (m + 1) ^ towerRatio k m = towerZeta k m :=
  (Classical.choose_spec (exists_isPrimitiveRoot_pow_eq (towerN_mul_ratio k m) (towerN_pos k m)
    (towerRatio_pos k m) (towerData k m).2.1)).2

/-- `t_{m+1}^{N_{m+1}/N_m} = t_m`. -/
theorem towerRoot_succ_pow (m : ℕ) : towerRoot k (m + 1) ^ towerRatio k m = towerRoot k m :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (towerData k m).1.2 (towerRatio_pos k m))

/-- `t_m` is nonzero. -/
theorem towerRoot_ne_zero (m : ℕ) : towerRoot k m ≠ 0 := by
  intro h
  apply xΩ_ne_zero k
  rw [← towerRoot_pow k m, h, zero_pow (towerN_pos k m).ne']

end Finite


end AlgebraicGeometry.TameMultiplicativeGroup

end
