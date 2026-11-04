module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.DeckAction

/-!
# Properties of the action of `Γ` on the Kummer tower

The action `AlgebraicGeometry.TameMultiplicativeGroup.deck` of `Γ = Ẑ^(q) ⋊ Ẑ` on the layers
`𝔽_{m!}[X]_X` is by automorphisms over `k[x]_x`, compatible with the transition maps,
transitive on the fibre, faithful on the tower and locally constant.

## Main results

* `deck_kummerMap`: `Γ` acts by automorphisms over `k[x]_x`.
* `towerTransition_deck`: the action commutes with the transition maps.
* `exists_eq_towerPoint_comp_deck`: every ring map `𝔽_{m!}[X]_X → Ω` over `k[x]_x` is the base
  point composed with the action of some `γ ∈ Γ`.
* `eq_one_of_forall_deck_eq_one`: an element acting trivially on every layer is trivial.
* `isOpen_setOf_deck_eq`: the action on each layer is locally constant on `Γ`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.TraceFormula

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

section General

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F] (n : ℕ)

/-- If `c ^ n = 1`, the map `X ↦ c X` of `F[X]_X` fixes the image of the Kummer map
`k[x]_x → F[X]_X`, `x ↦ X^n`. -/
theorem scaleHom_kummerMap (c : Fˣ) (hc : c ^ n = 1) (z : Ring k) :
    scaleHom F c (kummerMap k F n z) = kummerMap k F n z := by
  have : (scaleHom F c).comp (kummerMap k F n) = kummerMap k F n := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X : k[X]))
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, kummerMap_C, scaleHom_C]
    · simp only [RingHom.comp_apply]
      show scaleHom F c (kummerMap k F n (coord k)) = kummerMap k F n (coord k)
      rw [kummerMap_coord, map_pow, scaleHom_coord, mul_pow, ← map_pow, ← C_pow,
        ← Units.val_pow_eq_pow_val, hc, Units.val_one, C_1, map_one, one_mul]
  exact RingHom.congr_fun this z

/-- If `σ : F → F` fixes `k`, the induced map of `F[X]_X` fixes the image of the Kummer map
`k[x]_x → F[X]_X`. -/
theorem coeffHom_kummerMap (σ : F →+* F) (hσ : ∀ a : k, σ (algebraMap k F a) = algebraMap k F a)
    (z : Ring k) : coeffHom F σ (kummerMap k F n z) = kummerMap k F n z := by
  have : (coeffHom F σ).comp (kummerMap k F n) = kummerMap k F n := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X : k[X]))
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, kummerMap_C, coeffHom_C, hσ]
    · simp only [RingHom.comp_apply]
      show coeffHom F σ (kummerMap k F n (coord k)) = kummerMap k F n (coord k)
      rw [kummerMap_coord, map_pow, coeffHom_coord]
  exact RingHom.congr_fun this z

end General

variable (k : Type u) [Field k] [Fintype k]

/-- `(ζ_m^x)^{N_m} = 1` for every `x ∈ ℤ/N_m`. -/
theorem zetaPow_pow_towerN (m : ℕ) (x : ZMod (towerN k m)) : zetaPow k m x ^ towerN k m = 1 := by
  rw [zetaPow, ← pow_mul, mul_comm, pow_mul, zetaUnit_pow, one_pow]

/-- **`Γ` acts by automorphisms over `k[x]_x`.** -/
theorem deck_kummerMap (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) (z : Ring k) :
    deck k m γ (kummerMap k (towerField k m) (towerN k m) z) =
      kummerMap k (towerField k m) (towerN k m) z := by
  rw [deck_apply]
  show scaleHom _ _ (coeffHom _ _ _) = _
  rw [coeffHom_kummerMap _ _ (fun a ↦ frobAut_inv_pow_algebraMap k m _ a),
    scaleHom_kummerMap _ _ (zetaPow_pow_towerN k m _)]

/-- The transition `T_m` sends `X` to `X^{N_{m+1}/N_m}`. -/
theorem towerTransition_coord (m : ℕ) :
    towerTransition k m (coord (towerField k m)) =
      coord (towerField k (m + 1)) ^ towerRatio k m := by
  rw [coord, towerTransition_algebraMap, eval₂_X, map_pow]

/-- The transition `T_m` sends a constant `a ∈ 𝔽_{m!}` to the constant `a ∈ 𝔽_{(m+1)!}`. -/
theorem towerTransition_C (m : ℕ) (a : towerField k m) :
    towerTransition k m (algebraMap _ (Ring (towerField k m)) (C a)) =
      algebraMap _ (Ring (towerField k (m + 1))) (C (towerIncl k m a)) := by
  rw [towerTransition_algebraMap, eval₂_C, RingHom.comp_apply]

/-- If `τ` extends `τ₀` along `𝔽_{m!} ⊆ 𝔽_{(m+1)!}`, the transition `T_m` intertwines the
induced maps of `𝔽_{m!}[X]_X` and `𝔽_{(m+1)!}[X]_X`. -/
theorem towerTransition_coeffHom (m : ℕ) (τ₀ : RingAut (towerField k m))
    (τ : RingAut (towerField k (m + 1))) (h : ∀ a, τ (towerIncl k m a) = towerIncl k m (τ₀ a))
    (z : Ring (towerField k m)) :
    towerTransition k m (coeffHom _ τ₀.toRingHom z) =
      coeffHom _ τ.toRingHom (towerTransition k m z) := by
  have : (towerTransition k m).comp (coeffHom _ τ₀.toRingHom) =
      (coeffHom _ τ.toRingHom).comp (towerTransition k m) := by
    refine ringHom_ext_ring _ (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, coeffHom_C, towerTransition_C]
      exact congrArg _ (congrArg C (h a).symm)
    · simp only [RingHom.comp_apply, coeffHom_coord, towerTransition_coord, map_pow]
  exact RingHom.congr_fun this z

/-- If `c'^{N_{m+1}/N_m} = c`, the transition `T_m` intertwines `X ↦ c X` with `X ↦ c' X`. -/
theorem towerTransition_scaleHom (m : ℕ) (c : (towerField k m)ˣ) (c' : (towerField k (m + 1))ˣ)
    (h : (c' : towerField k (m + 1)) ^ towerRatio k m = towerIncl k m c)
    (z : Ring (towerField k m)) :
    towerTransition k m (scaleHom _ c z) = scaleHom _ c' (towerTransition k m z) := by
  have : (towerTransition k m).comp (scaleHom _ c) =
      (scaleHom _ c').comp (towerTransition k m) := by
    refine ringHom_ext_ring _ (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, scaleHom_C, towerTransition_C]
    · simp only [RingHom.comp_apply, scaleHom_coord, map_mul, towerTransition_C,
        towerTransition_coord, map_pow, mul_pow, ← h, C_pow]
  exact RingHom.congr_fun this z

/-- For `a ∣ b` and `x ∈ ℤ/b`, the representative of the image of `x` in `ℤ/a` is the
representative of `x` reduced modulo `a`. -/
theorem val_castHom_mod {a b : ℕ} [NeZero a] [NeZero b] (hab : a ∣ b) (x : ZMod b) :
    x.val % a = (ZMod.castHom hab (ZMod a) x).val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

/-- The representative of `d mod (m+1)!` reduced modulo `m!` is the representative of
`d mod m!`. -/
theorem redF_val_mod (m : ℕ) (d : ProfiniteIntegers) :
    (redF (m + 1) d).val % m.factorial = (redF m d).val := by
  rw [val_castHom_mod (Nat.factorial_dvd_factorial (Nat.le_succ m)),
    castHom_restrictedMod_of_dvd]

/-- The representative of `z mod N_{m+1}` reduced modulo `N_m` is the representative of
`z mod N_m`. -/
theorem redN_val_mod (m : ℕ) (z : RestrictedProfiniteIntegers (Fintype.card k)) :
    (redN k (m + 1) z).val % towerN k m = (redN k m z).val := by
  rw [val_castHom_mod (towerN_dvd k m), castHom_restrictedMod_of_dvd]

/-- The Frobenius of `𝔽_{(m+1)!}` restricts to the Frobenius of `𝔽_{m!}`. -/
theorem frobAut_incl (m : ℕ) (a : towerField k m) :
    frobAut k (m + 1) (towerIncl k m a) = towerIncl k m (frobAut k m a) := by
  apply Subtype.ext
  simp only [frobAut_apply, IntermediateField.coe_pow, coe_towerIncl]

/-- The inverse Frobenius of `𝔽_{(m+1)!}` restricts to the inverse Frobenius of `𝔽_{m!}`. -/
theorem frobAut_inv_incl (m : ℕ) (a : towerField k m) :
    (frobAut k (m + 1))⁻¹ (towerIncl k m a) = towerIncl k m ((frobAut k m)⁻¹ a) := by
  show (frobAut k (m + 1)).symm _ = towerIncl k m ((frobAut k m).symm a)
  rw [RingEquiv.symm_apply_eq, frobAut_incl, RingEquiv.apply_symm_apply]

/-- Every power of the inverse Frobenius of `𝔽_{(m+1)!}` restricts to the same power of the
inverse Frobenius of `𝔽_{m!}`. -/
theorem frobAut_inv_pow_incl (m e : ℕ) (a : towerField k m) :
    ((frobAut k (m + 1))⁻¹ ^ e) (towerIncl k m a) = towerIncl k m (((frobAut k m)⁻¹ ^ e) a) := by
  induction e generalizing a with
  | zero => rfl
  | succ e ih =>
    rw [pow_succ, pow_succ]
    show ((frobAut k (m + 1))⁻¹ ^ e) ((frobAut k (m + 1))⁻¹ (towerIncl k m a)) =
      towerIncl k m (((frobAut k m)⁻¹ ^ e) ((frobAut k m)⁻¹ a))
    rw [frobAut_inv_incl, ih]

/-- **The action is compatible with the transitions.** -/
theorem towerTransition_deck (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k)))
    (z : Ring (towerField k m)) :
    towerTransition k m (deck k m γ z) = deck k (m + 1) γ (towerTransition k m z) := by
  rw [deck_apply, deck_apply]
  show towerTransition k m (scaleHom _ _ (coeffHom _ _ z)) =
    scaleHom _ _ (coeffHom _ _ (towerTransition k m z))
  rw [towerTransition_scaleHom k m _ (zetaPow k (m + 1) (redN k (m + 1)
    (Multiplicative.toAdd γ.left))), towerTransition_coeffHom k m _
      ((frobAut k (m + 1))⁻¹ ^ (redF (m + 1) (Multiplicative.toAdd γ.right)).val)]
  · intro a
    have hord : ((frobAut k m)⁻¹) ^ m.factorial = 1 := by
      rw [inv_pow, frobAut_pow_factorial, inv_one]
    rw [frobAut_inv_pow_incl, pow_eq_pow_mod _ hord, redF_val_mod]
  · apply Subtype.ext
    show (((zetaPow k (m + 1) _ : (towerField k (m + 1))ˣ) : towerField k (m + 1)) : Omega k) ^
      towerRatio k m = (((zetaPow k m _ : (towerField k m)ˣ) : towerField k m) : Omega k)
    rw [zetaPow, zetaPow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      IntermediateField.coe_pow, IntermediateField.coe_pow, coe_zetaUnit, coe_zetaUnit,
      ← pow_mul, mul_comm, pow_mul, towerZeta_succ_pow,
      pow_eq_pow_mod _ (isPrimitiveRoot_towerZeta k m).pow_eq_one, redN_val_mod]

/-! ### Cofinality of the moduli -/

/-- Every `n ≥ 1` prime to `q` divides some `N_m = q^{m!} - 1`. -/
private theorem exists_dvd_towerN_aux (n : ℕ) (hn0 : n ≠ 0) (hcop : (Fintype.card k).Coprime n) :
    ∃ m, n ∣ towerN k m := by
  have : NeZero n := ⟨hn0⟩
  refine ⟨Nat.totient n, ?_⟩
  have hu : IsUnit ((Fintype.card k : ℕ) : ZMod n) := (ZMod.unitOfCoprime _ hcop).isUnit
  have h1 : ((Fintype.card k : ℕ) : ZMod n) ^ (Nat.totient n).factorial = 1 := by
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.totient_pos.mpr (Nat.pos_of_neZero n)) le_rfl
    rw [hc, pow_mul, ← hu.unit_spec, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one,
      one_pow]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (one_lt_card_pow k (Nat.totient n)).le,
    Nat.cast_pow, h1, Nat.cast_one, sub_self]

/-- Every prime power `ℓ^e` with `ℓ ∤ q` divides some `N_m = q^{m!} - 1`. -/
theorem exists_dvd_towerN (ℓ : CoprimePrimes (Fintype.card k)) (e : ℕ) :
    ∃ m, ℓ.1 ^ e ∣ towerN k m :=
  exists_dvd_towerN_aux k _ (pow_ne_zero _ ℓ.2.1.ne_zero)
    (Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd ℓ.2.1).mpr ℓ.2.2)))

/-- Every integer `n ≥ 1` divides some `m!`. -/
theorem exists_dvd_factorial (n : ℕ) (hn : n ≠ 0) : ∃ m : ℕ, n ∣ m.factorial :=
  ⟨n, Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl⟩

/-! ### Transitivity, faithfulness, local constancy -/

/-- Every ring map `𝔽_{m!} → Ω` takes values in `𝔽_{m!}`. -/
theorem mem_towerField_of_ringHom (m : ℕ) (g : towerField k m →+* Omega k) (a : towerField k m) :
    g a ∈ towerField k m := by
  rw [mem_frobField, ← map_pow]
  congr 1
  refine Subtype.ext ?_
  rw [IntermediateField.coe_pow]
  exact (mem_frobField k).mp a.2

/-- **The action is transitive on the fibre.** Every ring map `𝔽_{m!}[X]_X → Ω` over `k[x]_x` is
the base point composed with the action of some `γ ∈ Γ`. -/
theorem exists_eq_towerPoint_comp_deck (m : ℕ) (ψ : Ring (towerField k m) →+* Omega k)
    (hψ : ∀ z, ψ (kummerMap k (towerField k m) (towerN k m) z) = baseHom k z) :
    ∃ γ : Gamma (inverseCharacter (Fintype.card k)),
      ψ = (towerPoint k m).comp (deck k m γ).toRingHom := by
  classical
  -- the coefficients
  let ψF : (towerField k m) →+* Omega k :=
    ψ.comp (algebraMap (towerField k m) (Ring (towerField k m)))
  have hψk : ∀ a : k, ψF (algebraMap k (towerField k m) a) = algebraMap k (Omega k) a := by
    intro a
    have : algebraMap (towerField k m) (Ring (towerField k m)) (algebraMap k (towerField k m) a) =
        kummerMap k (towerField k m) (towerN k m) (algebraMap k[X] (Ring k) (C a)) := by
      rw [kummerMap_C, IsScalarTower.algebraMap_apply (towerField k m) (towerField k m)[X]
        (Ring (towerField k m)), ← C_eq_algebraMap]
    show ψ (algebraMap (towerField k m) (Ring (towerField k m))
      (algebraMap k (towerField k m) a)) = _
    rw [this, hψ, algebraMap_C, algebraMap_omega]
  let ρ : (towerField k m) →ₐ[k] (towerField k m) :=
    { toFun := fun a ↦ ⟨ψF a, mem_towerField_of_ringHom k m ψF a⟩
      map_one' := Subtype.ext (map_one ψF)
      map_mul' := fun a b ↦ Subtype.ext (map_mul ψF a b)
      map_zero' := Subtype.ext (map_zero ψF)
      map_add' := fun a b ↦ Subtype.ext (map_add ψF a b)
      commutes' := fun a ↦ Subtype.ext (hψk a) }
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgHom_pow k (towerField k m)).2 ρ
  -- the coordinate
  set s := ψ (coord (towerField k m))
  have hs : s ^ towerN k m = xΩ k := by
    rw [← map_pow, ← kummerMap_coord k (towerField k m) (towerN k m), hψ]
  have hst : (s / towerRoot k m) ^ towerN k m = 1 := by
    rw [div_pow, hs, towerRoot_pow, div_self (xΩ_ne_zero k)]
  obtain ⟨j, hjN, hj⟩ := (isPrimitiveRoot_towerZeta k m).eq_pow_of_pow_eq_one hst
  -- the element of `Γ`
  refine ⟨⟨Multiplicative.ofAdd (j : RestrictedProfiniteIntegers (Fintype.card k)),
    Multiplicative.ofAdd (-((i.1 : ℕ) : ProfiniteIntegers))⟩, ?_⟩
  refine ringHom_ext_ring (towerField k m) (fun a ↦ ?_) ?_
  · have hτ : ((frobAut k m)⁻¹ ^ (redF m (-((i.1 : ℕ) : ProfiniteIntegers))).val) =
        frobAut k m ^ i.1 := by
      have hdvd : m.factorial ∣ i.1 + (redF m (-((i.1 : ℕ) : ProfiniteIntegers))).val := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val, map_neg, map_natCast,
          add_neg_cancel]
      obtain ⟨c, hc⟩ := hdvd
      have h1 : frobAut k m ^ i.1 *
          frobAut k m ^ (redF m (-((i.1 : ℕ) : ProfiniteIntegers))).val = 1 := by
        rw [← pow_add, hc, pow_mul, frobAut_pow_factorial, one_pow]
      rw [inv_pow, ← eq_inv_of_mul_eq_one_left h1]
    show ψ (algebraMap _ _ (C a)) =
      towerPoint k m (scaleHom _ _ (coeffHom _ _ (algebraMap _ (Ring (towerField k m)) (C a))))
    rw [coeffHom_C, scaleHom_C, towerPoint_algebraMap, eval₂_C]
    show ψ (algebraMap _ _ (C a)) = (((((frobAut k m)⁻¹ ^
      (redF m (-((i.1 : ℕ) : ProfiniteIntegers))).val) a : towerField k m)) : Omega k)
    rw [hτ, frobAut_pow_apply, IntermediateField.coe_pow]
    have hρ : ((ρ a : towerField k m) : Omega k) =
        ψ (algebraMap _ (Ring (towerField k m)) (C a)) := by
      show ψ (algebraMap (towerField k m) (Ring (towerField k m)) a) = _
      rw [IsScalarTower.algebraMap_apply (towerField k m) (towerField k m)[X]
        (Ring (towerField k m)), ← C_eq_algebraMap]
    rw [← hρ, ← hi, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate,
      IntermediateField.coe_pow]
  · show s = towerPoint k m (scaleHom _ _ (coeffHom _ _ (coord _)))
    rw [coeffHom_coord, scaleHom_coord, map_mul, towerPoint_algebraMap, eval₂_C, towerPoint_coord]
    show s = (((zetaPow k m (redN k m (j : RestrictedProfiniteIntegers (Fintype.card k))) :
      (towerField k m)ˣ) : towerField k m) : Omega k) * towerRoot k m
    rw [map_natCast, zetaPow_natCast, Units.val_pow_eq_pow_val, IntermediateField.coe_pow,
      coe_zetaUnit, hj, div_mul_cancel₀ _ (towerRoot_ne_zero k m)]

/-- The unit `ζ_m^x` of `𝔽_{m!}`, viewed in `Ω`, is `ζ_m` raised to the representative of `x`. -/
theorem coe_zetaPow (m : ℕ) (x : ZMod (towerN k m)) :
    (((zetaPow k m x : (towerField k m)ˣ) : towerField k m) : Omega k) = towerZeta k m ^ x.val := by
  rw [zetaPow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, coe_zetaUnit]

/-- The map `x ↦ ζ_m^x` on `ℤ/N_m` is injective. -/
theorem zetaPow_injective (m : ℕ) : Function.Injective (zetaPow k m) := by
  intro x y h
  have h' := congrArg (fun u : (towerField k m)ˣ ↦ ((u : towerField k m) : Omega k)) h
  simp only [coe_zetaPow] at h'
  exact ZMod.val_injective _ ((isPrimitiveRoot_towerZeta k m).pow_inj (ZMod.val_lt x)
    (ZMod.val_lt y) h')

/-- The base point sends the image of `X` under `γ = (z, d)` to `ζ_m^{z mod N_m} t_m`. -/
theorem deck_coord (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) :
    towerPoint k m (deck k m γ (coord (towerField k m))) =
      towerZeta k m ^ (redN k m (Multiplicative.toAdd γ.left)).val * towerRoot k m := by
  rw [deck_apply]
  show towerPoint k m (scaleHom _ _ (coeffHom _ _ (coord _))) = _
  rw [coeffHom_coord, scaleHom_coord, map_mul, towerPoint_algebraMap, eval₂_C, towerPoint_coord]
  exact congrArg (· * towerRoot k m) (coe_zetaPow k m _)

/-- The element `γ = (z, d)` sends a constant `a ∈ 𝔽_{m!}` to the constant obtained by applying
the inverse Frobenius `d mod m!` times. -/
theorem deck_C (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) (a : towerField k m) :
    deck k m γ (algebraMap _ (Ring (towerField k m)) (C a)) = algebraMap _ (Ring (towerField k m))
      (C (((frobAut k m)⁻¹ ^ (redF m (Multiplicative.toAdd γ.right)).val) a)) := by
  rw [deck_apply]
  show scaleHom _ _ (coeffHom _ _ _) = _
  rw [coeffHom_C, scaleHom_C]
  rfl

/-- **The action is faithful on the tower.** -/
theorem eq_one_of_forall_deck_eq_one (γ : Gamma (inverseCharacter (Fintype.card k)))
    (h : ∀ m, deck k m γ = 1) : γ = 1 := by
  have hl : ∀ m, redN k m (Multiplicative.toAdd γ.left) = 0 := by
    intro m
    have h1 := deck_coord k m γ
    rw [h m] at h1
    change towerPoint k m (coord _) = _ at h1
    rw [towerPoint_coord] at h1
    have h2 : towerZeta k m ^ (redN k m (Multiplicative.toAdd γ.left)).val = 1 := by
      have := h1.symm
      rwa [mul_eq_right₀ (towerRoot_ne_zero k m)] at this
    have h3 := ((isPrimitiveRoot_towerZeta k m).pow_eq_one_iff_dvd _).mp h2
    exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _))
  have hr : ∀ m, redF m (Multiplicative.toAdd γ.right) = 0 := by
    intro m
    set e := (redF m (Multiplicative.toAdd γ.right)).val with he
    have h1 := deck_C k m γ ⟨towerZeta k m, towerZeta_mem k m⟩
    rw [h m] at h1
    have h2 : ((frobAut k m)⁻¹ ^ e) ⟨towerZeta k m, towerZeta_mem k m⟩ =
        ⟨towerZeta k m, towerZeta_mem k m⟩ := by
      have h1' : algebraMap _ (Ring (towerField k m))
          (C (⟨towerZeta k m, towerZeta_mem k m⟩ : towerField k m)) =
          algebraMap _ (Ring (towerField k m)) (C (((frobAut k m)⁻¹ ^ e)
            (⟨towerZeta k m, towerZeta_mem k m⟩ : towerField k m))) := h1
      exact (C_injective (IsLocalization.injective (Ring (towerField k m))
        (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero) h1')).symm
    have h3 : zetaPow k m (qInvMod k m ^ e) = zetaPow k m 1 := by
      rw [← frobAut_inv_pow_zeta, zetaPow_one]
      exact Units.ext h2
    have h4 := zetaPow_injective k m h3
    have h5 : ((Fintype.card k : ℕ) : ZMod (towerN k m)) ^ e = 1 := by
      calc ((Fintype.card k : ℕ) : ZMod (towerN k m)) ^ e =
            ((Fintype.card k : ℕ) : ZMod (towerN k m)) ^ e * qInvMod k m ^ e := by rw [h4, mul_one]
        _ = 1 := by rw [← mul_pow, mul_comm, qInvMod_mul_card, one_pow]
    have h6 : towerN k m ∣ Fintype.card k ^ e - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos),
        Nat.cast_pow, h5, Nat.cast_one, sub_self]
    have he0 : e = 0 := by
      by_contra hne
      have hlt : e < m.factorial := ZMod.val_lt _
      have hpos : 0 < Fintype.card k ^ e - 1 :=
        Nat.sub_pos_of_lt (Nat.one_lt_pow hne Fintype.one_lt_card)
      have := Nat.le_of_dvd hpos h6
      have : Fintype.card k ^ m.factorial ≤ Fintype.card k ^ e := by
        have h7 := one_lt_card_pow k m
        have h8 : towerN k m = Fintype.card k ^ m.factorial - 1 := rfl
        omega
      exact absurd ((Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp this) (not_le.mpr hlt)
    exact (ZMod.val_eq_zero _).mp he0
  have hl' : γ.left = 1 := by
    have := eq_of_forall_restrictedMod_eq (Fintype.card k) (towerN k)
      (fun m ↦ (towerN_pos k m).ne') (towerN_coprime k) (exists_dvd_towerN k)
      (z := Multiplicative.toAdd γ.left) (w := 0) (fun m ↦ by rw [hl m, map_zero])
    exact toAdd_eq_zero.mp this
  have hr' : γ.right = 1 := by
    have := eq_of_forall_restrictedMod_eq 1 Nat.factorial (fun m ↦ Nat.factorial_ne_zero m)
      (fun m ↦ Nat.coprime_one_right _)
      (fun ℓ e ↦ exists_dvd_factorial _ (pow_ne_zero _ ℓ.2.1.ne_zero))
      (z := Multiplicative.toAdd γ.right) (w := 0) (fun m ↦ by rw [hr m, map_zero])
    exact toAdd_eq_zero.mp this
  exact SemidirectProduct.ext hl' hr'

/-- The action of `γ = (z, d)` on the `m`-th layer depends only on `z mod N_m` and `d mod m!`. -/
theorem deck_eq_of_red_eq (m : ℕ) {γ γ' : Gamma (inverseCharacter (Fintype.card k))}
    (hl : redN k m (Multiplicative.toAdd γ.left) = redN k m (Multiplicative.toAdd γ'.left))
    (hr : redF m (Multiplicative.toAdd γ.right) = redF m (Multiplicative.toAdd γ'.right)) :
    deck k m γ = deck k m γ' := RingEquiv.ext fun z ↦ by
  rw [deck_apply, deck_apply]
  show scaleHom _ (zetaPow k m (redN k m _)) (coeffHom _ (((frobAut k m)⁻¹ ^
      (redF m _).val : RingAut _)).toRingHom z) =
    scaleHom _ (zetaPow k m (redN k m _)) (coeffHom _ (((frobAut k m)⁻¹ ^
      (redF m _).val : RingAut _)).toRingHom z)
  rw [hl, hr]

/-- **The action is locally constant.** -/
theorem isOpen_setOf_deck_eq (m : ℕ) (γ₀ : Gamma (inverseCharacter (Fintype.card k))) :
    IsOpen {γ | deck k m γ = deck k m γ₀} := by
  rw [isOpen_iff_forall_mem_open]
  intro γ₁ hγ₁
  refine ⟨{γ | redN k m (Multiplicative.toAdd γ.left) = redN k m (Multiplicative.toAdd γ₁.left)} ∩
    {γ | redF m (Multiplicative.toAdd γ.right) = redF m (Multiplicative.toAdd γ₁.right)},
    fun γ hγ ↦ (deck_eq_of_red_eq k m hγ.1 hγ.2).trans hγ₁, ?_, ⟨rfl, rfl⟩⟩
  refine IsOpen.inter ?_ ?_
  · exact (isOpen_discrete {redN k m (Multiplicative.toAdd γ₁.left)}).preimage
      ((continuous_restrictedMod _ _ _ _).comp (continuous_toAdd.comp (continuous_left _)))
  · exact (isOpen_discrete {redF m (Multiplicative.toAdd γ₁.right)}).preimage
      ((continuous_restrictedMod _ _ _ _).comp (continuous_toAdd.comp (continuous_degree _)))

/-- Every `n ≥ 1` prime to `q` divides some `N_m = q^{m!} - 1`. -/
theorem exists_dvd_towerN_of_coprime (n : ℕ) (hn0 : n ≠ 0) (hcop : (Fintype.card k).Coprime n) :
    ∃ m, n ∣ towerN k m :=
  exists_dvd_towerN_aux k n hn0 hcop

/-- `N_m ∣ N_{m'}` whenever `m ≤ m'`. -/
theorem towerN_dvd_of_le {m m' : ℕ} (h : m ≤ m') : towerN k m ∣ towerN k m' := by
  induction h with
  | refl => exact dvd_rfl
  | step _ ih => exact ih.trans (towerN_dvd k _)

end AlgebraicGeometry.TameMultiplicativeGroup

end
