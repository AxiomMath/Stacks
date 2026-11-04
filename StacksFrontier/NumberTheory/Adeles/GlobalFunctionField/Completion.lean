module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.PlacesOver
public import StacksFrontier.NumberTheory.Adeles.HeckeEigenform

/-!
# Completions at a discrete place

Let `v` be a discrete place of a field `K`, with completion `K_v` and ring of integers `O_v`. We
fix a uniformizer `ϖ ∈ K` of `v` and describe `K_v` through the balls
`ϖ^m O_v = {y ∈ K_v | v(y) ≤ v(ϖ)^m}`, `m ∈ ℤ`:

* an element `κ ∈ K` lies in `ϖ^m O_v` exactly when `κ = 0` or `ord_v κ ≥ m`;
* every element of `K_v` lies in some `ϖ^m O_v`, and `v(y) < v(ϖ)^m` forces `y ∈ ϖ^(m+1) O_v`;
* `ϖ^(m+1) O_v` has index `q_v` in `ϖ^m O_v`;
* `K` is dense in `K_v`, and the residue field of `O_v` is that of `v`.

## Main definitions

* `Stacks.Adeles.Place.unif` — a uniformizer of `v` in `K`.
* `Stacks.Adeles.Place.ball` — the subgroup `ϖ^m O_v` of `K_v`.

## Main results

* `Stacks.Adeles.Place.coeRingHom_mem_ball_iff`, `Stacks.Adeles.Place.exists_mem_ball`,
  `Stacks.Adeles.Place.mem_ball_succ_of_lt`.
* `Stacks.Adeles.Place.relIndex_ball` — `[ϖ^m O_v : ϖ^(m+1) O_v] = q_v`.
* `Stacks.Adeles.Place.residueCard_eq_resCard` — the residue fields of `v` and of `O_v` have the
  same cardinality.
-/

@[expose] public noncomputable section

open WithZero

universe u

namespace Stacks.Adeles.Place

variable {K : Type u} [Field K] (v : Place K)

/-- The valuation of the image of `y ∈ K` in `K_v` is the valuation of `y`. -/
public theorem valued_coeRingHom (y : K) : Valued.v (v.coeRingHom y) = v.1.valuation y := by
  show Valued.v ((WithVal.toVal v.1.valuation y : WithVal v.1.valuation) : v.completion) = _
  rw [Valued.valuedCompletion_apply]
  rfl

/-- `K` is dense in `K_v`: every element of `K_v` is within valuation `< 1` of an element of
`K`. -/
public theorem exists_sub_coeRingHom_lt_one (z : v.completion) :
    ∃ y : K, Valued.v (z - v.coeRingHom y) < 1 := by
  have hs : {w : v.completion | Valued.v.restrict (w - z) < 1} ∈ nhds z :=
    Valued.mem_nhds.2 ⟨1, fun w hw => hw⟩
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds hs
  refine ⟨WithVal.ofVal w, ?_⟩
  have : v.coeRingHom (WithVal.ofVal w) = (w : v.completion) := rfl
  rw [this, ← Valuation.map_neg, neg_sub]
  simpa [Valuation.restrict_lt_one_iff] using hw

/-- Every value of `K_v` is a value of `K`. -/
public theorem exists_valued_eq (z : v.completion) :
    ∃ y : K, Valued.v z = Valued.v (v.coeRingHom y) := by
  obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v z
  exact ⟨WithVal.ofVal r, hr.trans (by rw [valued_coeRingHom]; rfl)⟩

variable {v}

/-- The normalized valuation of a discrete place is equivalent to the valuation of the place. -/
public theorem normVal_isEquiv (hv : v.IsDiscrete) : v.normVal.IsEquiv v.1.valuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).2
    ((normVal_spec hv).1.trans v.1.valuationSubring_valuation.symm)

variable (v)

/-- A uniformizer of `v` in `K`: an element of normalized valuation `exp (-1)`. -/
public def unif : K := Classical.epsilon fun ϖ : K => v.normVal ϖ = exp (-1)

variable {v}

/-- The uniformizer has normalized valuation `exp (-1)`. -/
public theorem normVal_unif (hv : v.IsDiscrete) : v.normVal v.unif = exp (-1) :=
  Classical.epsilon_spec ((normVal_spec hv).2 (exp (-1)))

/-- The uniformizer is nonzero. -/
public theorem unif_ne_zero (hv : v.IsDiscrete) : v.unif ≠ 0 := by
  intro h
  have := normVal_unif hv
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

/-- The uniformizer has order `1`. -/
public theorem ord_unif (hv : v.IsDiscrete) : v.ord v.unif = 1 := by
  simp [ord, normVal_unif hv]

/-- `v(ϖ^m) = exp (-m)` for the normalized valuation. -/
public theorem normVal_unif_zpow (hv : v.IsDiscrete) (m : ℤ) :
    v.normVal (v.unif ^ m) = exp (-m) := by
  rw [map_zpow₀, normVal_unif hv, ← exp_zsmul]
  simp

/-- `v(y) = exp (-ord_v y)` for `y ≠ 0`. -/
public theorem normVal_eq_exp {y : K} (hy : y ≠ 0) : v.normVal y = exp (-v.ord y) := by
  rw [ord, neg_neg, exp_log (by simpa using hy)]

/-- An element `r ∈ K` has `v(r) ≤ v(ϖ)^m` exactly when `r = 0` or `ord_v r ≥ m`. -/
public theorem valuation_le_unif_zpow_iff (hv : v.IsDiscrete) (r : K) (m : ℤ) :
    v.1.valuation r ≤ v.1.valuation (v.unif ^ m) ↔ r = 0 ∨ m ≤ v.ord r := by
  rw [← (normVal_isEquiv hv).le_iff_le, normVal_unif_zpow hv]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [normVal_eq_exp hr, exp_le_exp]
    simp [hr]

/-- The value `v(ϖ)` of the uniformizer in `K_v`. -/
public def unifVal (v : Place K) : v.1.ValueGroup := v.1.valuation v.unif

/-- `v(ϖ) ≠ 0`. -/
public theorem unifVal_ne_zero (hv : v.IsDiscrete) : v.unifVal ≠ 0 := by
  simpa [unifVal] using unif_ne_zero hv

/-- `v(ϖ) < 1`. -/
public theorem unifVal_lt_one (hv : v.IsDiscrete) : v.unifVal < 1 := by
  rw [unifVal, ← (normVal_isEquiv hv).lt_one_iff_lt_one, normVal_unif hv]
  simp [← exp_zero]

/-- `0 < v(ϖ)`. -/
private theorem unifVal_pos (hv : v.IsDiscrete) : 0 < v.unifVal :=
  zero_lt_iff.2 (unifVal_ne_zero hv)

/-- `m < n` implies `v(ϖ)^n < v(ϖ)^m`. -/
private theorem zpow_unifVal_lt (hv : v.IsDiscrete) {m n : ℤ} (h : m < n) :
    v.unifVal ^ n < v.unifVal ^ m :=
  zpow_lt_zpow_right_of_lt_one₀ (unifVal_pos hv) (unifVal_lt_one hv) h

/-- `v(ϖ)^m = v(ϖ)^n` implies `m = n`. -/
private theorem eq_of_unifVal_zpow_eq (hv : v.IsDiscrete) {m n : ℤ}
    (h : v.unifVal ^ m = v.unifVal ^ n) : m = n :=
  zpow_right_injective₀ (unifVal_pos hv) (unifVal_lt_one hv).ne h

/-- The image of `ϖ^m` in `K_v` has valuation `v(ϖ)^m`. -/
public theorem valued_coeRingHom_unif_zpow (m : ℤ) :
    Valued.v (v.coeRingHom (v.unif ^ m)) = v.unifVal ^ m := by
  rw [valued_coeRingHom, map_zpow₀, unifVal]

/-- The subgroup `ϖ^m O_v = {y ∈ K_v | v(y) ≤ v(ϖ)^m}` of `K_v`. -/
public def ball (v : Place K) (m : ℤ) : AddSubgroup v.completion where
  carrier := {y | Valued.v y ≤ v.unifVal ^ m}
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact zero_le
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  neg_mem' {a} ha := by simpa using ha

/-- `y ∈ ϖ^m O_v` exactly when `v(y) ≤ v(ϖ)^m`. -/
public theorem mem_ball {m : ℤ} {y : v.completion} :
    y ∈ v.ball m ↔ Valued.v y ≤ v.unifVal ^ m := by
  rfl

/-- An element `κ ∈ K` lies in `ϖ^m O_v` exactly when `κ = 0` or `ord_v κ ≥ m`. -/
public theorem coeRingHom_mem_ball_iff (hv : v.IsDiscrete) {m : ℤ} {κ : K} :
    v.coeRingHom κ ∈ v.ball m ↔ κ = 0 ∨ m ≤ v.ord κ := by
  rw [mem_ball, valued_coeRingHom, unifVal, ← map_zpow₀, valuation_le_unif_zpow_iff hv]

/-- `m ≤ n` implies `v(ϖ)^n ≤ v(ϖ)^m`. -/
public theorem zpow_unifVal_anti (hv : v.IsDiscrete) {m n : ℤ} (h : m ≤ n) :
    v.unifVal ^ n ≤ v.unifVal ^ m :=
  zpow_le_zpow_right_of_le_one₀ (unifVal_pos hv) (unifVal_lt_one hv).le h

/-- The balls decrease: `m ≤ n` implies `ϖ^n O_v ⊆ ϖ^m O_v`. -/
public theorem ball_anti (hv : v.IsDiscrete) {m n : ℤ} (h : m ≤ n) : v.ball n ≤ v.ball m := by
  intro y hy
  rw [mem_ball] at hy ⊢
  exact hy.trans (zpow_unifVal_anti hv h)

/-- Every element of `K_v` lies in some `ϖ^m O_v`. -/
public theorem exists_mem_ball (hv : v.IsDiscrete) (z : v.completion) : ∃ m : ℤ, z ∈ v.ball m := by
  obtain ⟨r, hr⟩ := exists_valued_eq v z
  rcases eq_or_ne r 0 with rfl | hr0
  · refine ⟨0, ?_⟩
    rw [mem_ball, hr, map_zero, map_zero]
    exact zero_le
  · refine ⟨v.ord r, ?_⟩
    rw [mem_ball, hr, ← mem_ball]
    exact (coeRingHom_mem_ball_iff hv).2 (Or.inr le_rfl)

/-- Values are discrete: `v(y) < v(ϖ)^m` forces `y ∈ ϖ^(m+1) O_v`. -/
public theorem mem_ball_succ_of_lt (hv : v.IsDiscrete) {m : ℤ} {z : v.completion}
    (h : Valued.v z < v.unifVal ^ m) : z ∈ v.ball (m + 1) := by
  obtain ⟨r, hr⟩ := exists_valued_eq v z
  rw [mem_ball, hr, ← mem_ball, coeRingHom_mem_ball_iff hv]
  rw [hr, valued_coeRingHom, unifVal, ← map_zpow₀, ← (normVal_isEquiv hv).lt_iff_lt,
    normVal_unif_zpow hv] at h
  rcases eq_or_ne r 0 with rfl | hr0
  · exact Or.inl rfl
  rw [normVal_eq_exp hr0, exp_lt_exp] at h
  exact Or.inr (by omega)

/-- `ϖ^0 O_v` is `O_v`. -/
public theorem mem_ball_zero_iff {y : v.completion} : y ∈ v.ball 0 ↔ y ∈ v.integers := by
  rw [mem_ball, zpow_zero]
  rfl

/-- The valuation of `y ∈ O_v` for the valuation subring `O_v` is `< 1` exactly when `v(y) < 1`. -/
public theorem integers_valuation_lt_one_iff (y : v.integers) :
    v.integers.valuation (y : v.completion) < 1 ↔ Valued.v (y : v.completion) < 1 :=
  ((Valuation.isEquiv_iff_valuationSubring _ _).2
    v.integers.valuationSubring_valuation).lt_one_iff_lt_one

/-- The valuation of `y ∈ O_v` for the valuation subring `O_v` is `1` exactly when `v(y) = 1`. -/
public theorem integers_valuation_eq_one_iff (y : v.integers) :
    v.integers.valuation (y : v.completion) = 1 ↔ Valued.v (y : v.completion) = 1 :=
  ((Valuation.isEquiv_iff_valuationSubring _ _).2
    v.integers.valuationSubring_valuation).eq_one_iff_eq_one

variable (v) in
/-- The inclusion `v ⊆ O_v`. -/
public def toIntegers : v.1 →+* v.integers where
  toFun a := ⟨v.coeRingHom (a : K), by
    rw [Place.integers, Valuation.mem_valuationSubring_iff, valued_coeRingHom]
    exact v.1.valuation_le_one a⟩
  map_one' := Subtype.ext (map_one v.coeRingHom)
  map_mul' a b := Subtype.ext (map_mul v.coeRingHom (a : K) (b : K))
  map_zero' := Subtype.ext (map_zero v.coeRingHom)
  map_add' a b := Subtype.ext (map_add v.coeRingHom (a : K) (b : K))

/-- The inclusion `v ⊆ O_v` is the map `K → K_v` on elements. -/
@[simp]
public theorem coe_toIntegers (a : v.1) :
    (toIntegers v a : v.completion) = v.coeRingHom (a : K) := rfl

/-- The inclusion `v ⊆ O_v` is a local homomorphism. -/
public instance : IsLocalHom (toIntegers v) := by
  refine ⟨fun a ha => ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff] at ha ⊢
  rw [integers_valuation_eq_one_iff, coe_toIntegers, valued_coeRingHom] at ha
  exact ha

/-- The residue fields of `v` and of `O_v` have the same cardinality. -/
public theorem residueCard_eq_resCard : v.residueCard = v.resCard := by
  have hbij : Function.Bijective (IsLocalRing.ResidueField.map (toIntegers v)) := by
    refine ⟨(IsLocalRing.ResidueField.map (toIntegers v)).injective, fun z => ?_⟩
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨y, hy⟩ := exists_sub_coeRingHom_lt_one v (w : v.completion)
    have hyv : y ∈ v.1 := by
      rw [← ValuationSubring.valuation_le_one_iff, ← valued_coeRingHom]
      calc Valued.v (v.coeRingHom y) = Valued.v ((w : v.completion) - ((w : v.completion) -
            v.coeRingHom y)) := by rw [sub_sub_cancel]
        _ ≤ max (Valued.v (w : v.completion)) (Valued.v ((w : v.completion) - v.coeRingHom y)) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := max_le w.2 hy.le
    refine ⟨IsLocalRing.residue v.1 ⟨y, hyv⟩, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff,
      integers_valuation_lt_one_iff]
    push_cast
    rw [coe_toIntegers, Valuation.map_sub_swap]
    exact hy
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

/-- `ϖ^(m+1) O_v` has index `q_v` in `ϖ^m O_v`. -/
public theorem relIndex_ball (hv : v.IsDiscrete) (m : ℤ) :
    (v.ball (m + 1)).relIndex (v.ball m) = v.residueCard := by
  set ϖ : v.completion := v.coeRingHom v.unif
  set γ := v.unifVal
  have hγ0 : γ ≠ 0 := unifVal_ne_zero hv
  have hϖ : Valued.v ϖ = γ := valued_coeRingHom v v.unif
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact hγ0 hϖ.symm
  have hval : ∀ y : v.completion, Valued.v (y * ϖ ^ (-m)) = Valued.v y * (γ ^ m)⁻¹ := by
    intro y
    rw [map_mul, map_zpow₀, hϖ, zpow_neg]
  have hmem : ∀ y : v.ball m, (y : v.completion) * ϖ ^ (-m) ∈ v.integers := by
    intro y
    rw [Place.integers, Valuation.mem_valuationSubring_iff, hval]
    calc Valued.v (y : v.completion) * (γ ^ m)⁻¹ ≤ γ ^ m * (γ ^ m)⁻¹ :=
        mul_le_mul_left (mem_ball.1 y.2) _
      _ = 1 := mul_inv_cancel₀ (zpow_ne_zero _ hγ0)
  let φ : v.ball m →+ IsLocalRing.ResidueField v.integers :=
    { toFun := fun y => IsLocalRing.residue v.integers ⟨_, hmem y⟩
      map_zero' := by
        rw [← map_zero (IsLocalRing.residue v.integers)]
        congr 1
        exact Subtype.ext (by simp)
      map_add' := fun y z => by
        rw [← map_add]
        congr 1
        exact Subtype.ext (by simp [add_mul]) }
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
    have hw : (w : v.completion) * ϖ ^ m ∈ v.ball m := by
      rw [mem_ball, map_mul, map_zpow₀, hϖ]
      have : Valued.v (w : v.completion) ≤ 1 := w.2
      exact mul_le_of_le_one_left zero_le this
    refine ⟨⟨_, hw⟩, ?_⟩
    show IsLocalRing.residue v.integers _ = _
    congr 1
    refine Subtype.ext ?_
    show (w : v.completion) * ϖ ^ m * ϖ ^ (-m) = w
    rw [mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one]
  have hker : φ.ker = (v.ball (m + 1)).addSubgroupOf (v.ball m) := by
    ext y
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    show IsLocalRing.residue v.integers ⟨_, hmem y⟩ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff,
      integers_valuation_lt_one_iff]
    show Valued.v ((y : v.completion) * ϖ ^ (-m)) < 1 ↔ _
    rw [hval, mul_inv_lt_iff₀ (zpow_pos (unifVal_pos hv) _), one_mul]
    exact ⟨mem_ball_succ_of_lt hv,
      fun h => (mem_ball.1 h).trans_lt (zpow_unifVal_lt hv m.lt_succ_self)⟩
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    AddSubgroup.card_top]
  rfl

/-- The valuation of `y ∈ K` in terms of the uniformizer: `v(y) = v(ϖ)^(ord_v y)`. -/
public theorem valuation_eq_unifVal_zpow (hv : v.IsDiscrete) {y : K} (hy : y ≠ 0) :
    v.1.valuation y = v.unifVal ^ v.ord y := by
  have hϖ := unif_ne_zero hv
  set n := v.ord y
  have hunit : v.normVal (y / v.unif ^ n) = 1 := by
    rw [map_div₀, normVal_unif_zpow hv, normVal_eq_exp hy, div_self exp_ne_zero]
  have h1 : v.1.valuation (y / v.unif ^ n) = 1 := (normVal_isEquiv hv).eq_one_iff_eq_one.1 hunit
  have : y = y / v.unif ^ n * v.unif ^ n := by
    rw [div_mul_cancel₀ _ (zpow_ne_zero _ hϖ)]
  rw [this, map_mul, h1, one_mul, map_zpow₀, unifVal]

/-- Multiplication by `z` with `v(z) = v(ϖ)^k` maps `ϖ^m O_v` onto `ϖ^(m + k) O_v`. -/
private theorem mul_mem_ball_iff_of_valued_eq (hv : v.IsDiscrete) {z : v.completion} {k : ℤ}
    (hz : Valued.v z = v.unifVal ^ k) {m : ℤ} {y : v.completion} :
    z * y ∈ v.ball (m + k) ↔ y ∈ v.ball m := by
  rw [mem_ball, mem_ball, map_mul, hz, zpow_add₀ (unifVal_ne_zero hv), mul_comm (v.unifVal ^ m)]
  exact mul_le_mul_iff_right₀ (zpow_pos (unifVal_pos hv) _)

/-- Multiplication by `y ≠ 0` maps `ϖ^m O_v` onto `ϖ^(m + ord_v y) O_v`. -/
public theorem coeRingHom_mul_mem_ball_iff (hv : v.IsDiscrete) {y : K} (hy : y ≠ 0) {m : ℤ}
    {z : v.completion} : v.coeRingHom y * z ∈ v.ball (m + v.ord y) ↔ z ∈ v.ball m :=
  mul_mem_ball_iff_of_valued_eq hv (by rw [valued_coeRingHom, valuation_eq_unifVal_zpow hv hy])

variable (v) in
/-- The order of an element of `K_v`: the order of an element of `K` of the same valuation. -/
public def ordC (y : v.completion) : ℤ := v.ord (exists_valued_eq v y).choose

/-- The valuation of `y ∈ K_v` is that of the element of `K` defining `ord_v y`. -/
public theorem valued_eq_ordC (y : v.completion) :
    Valued.v y = Valued.v (v.coeRingHom (exists_valued_eq v y).choose) :=
  (exists_valued_eq v y).choose_spec

/-- `v(y) = v(ϖ)^(ord_v y)` for `y ≠ 0` in `K_v`. -/
public theorem valued_eq_unifVal_zpow_ordC (hv : v.IsDiscrete) {y : v.completion} (hy : y ≠ 0) :
    Valued.v y = v.unifVal ^ v.ordC y := by
  have h := valued_eq_ordC y
  have hr : (exists_valued_eq v y).choose ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at h
    exact hy ((Valuation.zero_iff _).1 h)
  rw [h, valued_coeRingHom, valuation_eq_unifVal_zpow hv hr]
  rfl

/-- `y ∈ ϖ^m O_v` exactly when `y = 0` or `ord_v y ≥ m`. -/
public theorem mem_ball_iff_ordC (hv : v.IsDiscrete) {m : ℤ} {y : v.completion} :
    y ∈ v.ball m ↔ y = 0 ∨ m ≤ v.ordC y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [(v.ball m).zero_mem]
  rw [mem_ball, valued_eq_unifVal_zpow_ordC hv hy]
  simp only [hy, false_or]
  exact zpow_le_zpow_iff_right_of_lt_one₀ (unifVal_pos hv) (unifVal_lt_one hv)

/-- The order on `K_v` extends the order on `K`. -/
public theorem ordC_coeRingHom (hv : v.IsDiscrete) {κ : K} (hκ : κ ≠ 0) :
    v.ordC (v.coeRingHom κ) = v.ord κ := by
  have hy : v.coeRingHom κ ≠ 0 := by simpa using hκ
  have h1 := valued_eq_unifVal_zpow_ordC hv hy
  rw [valued_coeRingHom, valuation_eq_unifVal_zpow hv hκ] at h1
  exact (eq_of_unifVal_zpow_eq hv h1).symm

/-- `ord_v (y z) = ord_v y + ord_v z` for nonzero `y, z ∈ K_v`. -/
public theorem ordC_mul (hv : v.IsDiscrete) {y z : v.completion} (hy : y ≠ 0) (hz : z ≠ 0) :
    v.ordC (y * z) = v.ordC y + v.ordC z := by
  have hyz : y * z ≠ 0 := mul_ne_zero hy hz
  have h1 := valued_eq_unifVal_zpow_ordC hv hyz
  rw [map_mul, valued_eq_unifVal_zpow_ordC hv hy, valued_eq_unifVal_zpow_ordC hv hz,
    ← zpow_add₀ (unifVal_ne_zero hv)] at h1
  exact (eq_of_unifVal_zpow_eq hv h1).symm

/-- Multiplication by `z ≠ 0` maps `ϖ^m O_v` onto `ϖ^(m + ord_v z) O_v`. -/
public theorem mul_mem_ball_iff (hv : v.IsDiscrete) {z : v.completion} (hz : z ≠ 0) {m : ℤ}
    {y : v.completion} : z * y ∈ v.ball (m + v.ordC z) ↔ y ∈ v.ball m :=
  mul_mem_ball_iff_of_valued_eq hv (valued_eq_unifVal_zpow_ordC hv hz)

/-- The balls `ϖ^m O_v` are open. -/
public theorem isOpen_ball (hv : v.IsDiscrete) (m : ℤ) : IsOpen (v.ball m : Set v.completion) := by
  set c : v.completion := v.coeRingHom (v.unif ^ (-m))
  have hc : c ≠ 0 := (_root_.map_ne_zero _).2 (zpow_ne_zero _ (unif_ne_zero hv))
  have hcord : v.ordC c = -m := by
    rw [ordC_coeRingHom hv (zpow_ne_zero _ (unif_ne_zero hv)), Place.ord, map_zpow₀,
      normVal_unif hv, ← exp_zsmul, log_exp]
    simp
  have : (v.ball m : Set v.completion) = (fun y => c * y) ⁻¹' (v.integers : Set v.completion) := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_preimage]
    rw [← mem_ball_zero_iff]
    have h := mul_mem_ball_iff hv hc (m := m) (y := y)
    rw [hcord, add_neg_cancel] at h
    exact h.symm
  rw [this]
  exact (Valued.isOpen_valuationSubring v.completion).preimage (continuous_const.mul continuous_id)

/-- The image of the uniformizer lies in `O_v`. -/
public theorem coeRingHom_unif_mem_integers (hv : v.IsDiscrete) :
    v.coeRingHom v.unif ∈ v.integers := by
  rw [← mem_ball_zero_iff]
  refine ball_anti hv (zero_le_one) ?_
  rw [coeRingHom_mem_ball_iff hv, ord_unif hv]
  exact Or.inr le_rfl

/-- The image of the uniformizer `ϖ ∈ K` generates the maximal ideal of `O_v`. -/
public theorem isUniformizer_unif (hv : v.IsDiscrete) :
    Place.IsUniformizer v ⟨v.coeRingHom v.unif, coeRingHom_unif_mem_integers hv⟩ := by
  set π : v.integers := ⟨v.coeRingHom v.unif, coeRingHom_unif_mem_integers hv⟩
  have hπv : Valued.v (π : v.completion) = v.unifVal := by
    show Valued.v (v.coeRingHom v.unif) = _
    rw [valued_coeRingHom]; rfl
  have hπ0 : (π : v.completion) ≠ 0 := by
    intro h; rw [h, map_zero] at hπv; exact unifVal_ne_zero hv hπv.symm
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      ValuationSubring.valuation_lt_one_iff, integers_valuation_lt_one_iff, hπv]
    exact unifVal_lt_one hv
  · intro y hy
    rw [ValuationSubring.valuation_lt_one_iff, integers_valuation_lt_one_iff] at hy
    have h1 : (y : v.completion) ∈ v.ball (0 + 1) :=
      mem_ball_succ_of_lt hv (by rwa [zpow_zero])
    rw [zero_add, mem_ball, zpow_one] at h1
    have hq : (y : v.completion) * (π : v.completion)⁻¹ ∈ v.integers := by
      refine (Valuation.mem_valuationSubring_iff _ _).2 ?_
      rw [map_mul, map_inv₀, hπv]
      calc Valued.v (y : v.completion) * v.unifVal⁻¹ ≤ v.unifVal * v.unifVal⁻¹ :=
            mul_le_mul_left h1 _
        _ = 1 := mul_inv_cancel₀ (unifVal_ne_zero hv)
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
    show (y : v.completion) * (π : v.completion)⁻¹ * π = y
    rw [inv_mul_cancel_right₀ hπ0]

/-- Every neighbourhood of `0` in `K_v` contains a ball `ϖ^m O_v`. -/
public theorem exists_ball_subset (hv : v.IsDiscrete) {s : Set v.completion}
    (hs : s ∈ nhds (0 : v.completion)) : ∃ m : ℤ, (v.ball m : Set v.completion) ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨r, hr⟩ := v.1.valuation_surjective (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hr
    exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ hr.symm
  refine ⟨v.ord r + 1, fun z hz => hγ ?_⟩
  show Valued.v.restrict z < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hr, valuation_eq_unifVal_zpow hv hr0]
  exact (mem_ball.1 hz).trans_lt (zpow_unifVal_lt hv (by omega))

end Stacks.Adeles.Place

end
