module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.LaurentAutomorphisms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.TowerPoints
public import StacksFrontier.NumberTheory.TraceFormula.RestrictedProfiniteMod

/-!
# The action of `Γ = Ẑ^(q) ⋊ Ẑ` on the Kummer tower

Let `k` be a finite field with `q` elements and `Γ = Ẑ^(q) ⋊ Ẑ` with `F x F⁻¹ = q⁻¹ x`
(`Stacks.TraceFormula.Gamma (Stacks.TraceFormula.inverseCharacter q)`). On the `m`-th layer
`𝔽_{m!}[X]_X` of the Kummer tower, `z ∈ Ẑ^(q)` acts by `X ↦ ζ_m^{z mod N_m} X` and the
generator `F` of `Ẑ` by the inverse of the Frobenius `a ↦ a^q` on the coefficients (the geometric
Frobenius). The relation `F x F⁻¹ = q⁻¹ x` holds because `Frob⁻¹(ζ) = ζ^{q⁻¹}`.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.deck k m : Γ →* RingAut 𝔽_{m!}[X]_X`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.TraceFormula

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable (k : Type u) [Field k] [Fintype k]

/-- The cardinality `q` of a finite field is nonzero. -/
instance : NeZero (Fintype.card k) := ⟨Fintype.card_ne_zero⟩

/-- The integer `N_m = q^{m!} - 1` is nonzero. -/
instance (m : ℕ) : NeZero (towerN k m) := ⟨(towerN_pos k m).ne'⟩

/-- `N_m = q^{m!} - 1` is coprime to `q`. -/
theorem towerN_coprime (m : ℕ) : (towerN k m).Coprime (Fintype.card k) := by
  have h1 : 1 ≤ Fintype.card k ^ m.factorial := (one_lt_card_pow k m).le
  have : Nat.Coprime (towerN k m) (Fintype.card k ^ m.factorial) := by
    have h := (Nat.coprime_self_add_right (m := towerN k m) (n := 1)).mpr (Nat.coprime_one_right _)
    rwa [Nat.sub_add_cancel h1] at h
  exact this.coprime_dvd_right (dvd_pow_self _ (Nat.factorial_ne_zero m))

/-- `q^{m!} = 1` in `ℤ/N_m`. -/
theorem card_pow_eq_one_zmod (m : ℕ) :
    ((Fintype.card k : ℕ) : ZMod (towerN k m)) ^ m.factorial = 1 := by
  have h1 : 1 ≤ Fintype.card k ^ m.factorial := (one_lt_card_pow k m).le
  rw [← Nat.cast_pow, ← Nat.sub_add_cancel h1, Nat.cast_add, ZMod.natCast_self, zero_add,
    Nat.cast_one]

/-- The reduction `Ẑ^(q) → ℤ/N_m`. -/
abbrev redN (m : ℕ) : RestrictedProfiniteIntegers (Fintype.card k) →+* ZMod (towerN k m) :=
  restrictedMod (Fintype.card k) (towerN k m) (towerN_pos k m).ne' (towerN_coprime k m)

/-- The reduction `Ẑ → ℤ/m!`. -/
abbrev redF (m : ℕ) : ProfiniteIntegers →+* ZMod m.factorial :=
  restrictedMod 1 m.factorial (Nat.factorial_ne_zero m) (Nat.coprime_one_right _)

/-- `ζ_m` as a unit of `𝔽_{m!}`. -/
def zetaUnit (m : ℕ) : (towerField k m)ˣ :=
  Units.mk0 ⟨towerZeta k m, towerZeta_mem k m⟩ (fun h ↦
    (isPrimitiveRoot_towerZeta k m).ne_zero (towerN_pos k m).ne' (congrArg Subtype.val h))

/-- The unit `zetaUnit k m` has underlying element `ζ_m`. -/
theorem coe_zetaUnit (m : ℕ) : ((zetaUnit k m : towerField k m) : Omega k) = towerZeta k m := rfl

/-- `ζ_m^{N_m} = 1`. -/
theorem zetaUnit_pow (m : ℕ) : zetaUnit k m ^ towerN k m = 1 := by
  ext
  show ((((zetaUnit k m) ^ towerN k m : (towerField k m)ˣ) : towerField k m) : Omega k) = 1
  rw [Units.val_pow_eq_pow_val, IntermediateField.coe_pow, coe_zetaUnit,
    (isPrimitiveRoot_towerZeta k m).pow_eq_one]

/-- `x ↦ ζ_m^{x}` on `ℤ/N_m`. -/
def zetaPow (m : ℕ) (x : ZMod (towerN k m)) : (towerField k m)ˣ := zetaUnit k m ^ x.val

/-- `ζ_m^{n mod N_m} = ζ_m^n` for a natural number `n`. -/
theorem zetaPow_natCast (m n : ℕ) : zetaPow k m n = zetaUnit k m ^ n := by
  rw [zetaPow, ZMod.val_natCast, ← pow_eq_pow_mod n (zetaUnit_pow k m)]

/-- `ζ_m^{x + y} = ζ_m^x ζ_m^y` for `x y : ℤ/N_m`. -/
theorem zetaPow_add (m : ℕ) (x y : ZMod (towerN k m)) :
    zetaPow k m (x + y) = zetaPow k m x * zetaPow k m y := by
  rw [zetaPow, zetaPow, zetaPow, ZMod.val_add, ← pow_eq_pow_mod _ (zetaUnit_pow k m), pow_add]

/-- `ζ_m^{x y} = (ζ_m^x)^y` for `x y : ℤ/N_m`, with `y` represented in `[0, N_m)`. -/
theorem zetaPow_mul (m : ℕ) (x y : ZMod (towerN k m)) :
    zetaPow k m (x * y) = zetaPow k m x ^ y.val := by
  rw [zetaPow, zetaPow, ZMod.val_mul, ← pow_eq_pow_mod _ (zetaUnit_pow k m), pow_mul]

/-- `ζ_m^0 = 1`. -/
theorem zetaPow_zero (m : ℕ) : zetaPow k m 0 = 1 := by rw [zetaPow, ZMod.val_zero, pow_zero]

/-- `ζ_m^1 = ζ_m`. -/
theorem zetaPow_one (m : ℕ) : zetaPow k m 1 = zetaUnit k m := by
  rw [← Nat.cast_one, zetaPow_natCast, pow_one]

/-- The Frobenius `a ↦ a^q` of `𝔽_{m!}`. -/
def frobAut (m : ℕ) : RingAut (towerField k m) :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic k (towerField k m)).toRingEquiv

/-- The Frobenius sends `a` to `a^q`. -/
theorem frobAut_apply (m : ℕ) (a : towerField k m) : frobAut k m a = a ^ Fintype.card k := rfl

/-- The `n`-th power of the Frobenius sends `a` to `a^{q^n}`. -/
theorem frobAut_pow_apply (m n : ℕ) (a : towerField k m) :
    (frobAut k m ^ n) a = a ^ Fintype.card k ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    show frobAut k m ((frobAut k m ^ n) a) = _
    rw [ih, frobAut_apply, ← pow_mul, ← pow_succ]

/-- The Frobenius of `𝔽_{m!}` has order dividing `m!`. -/
theorem frobAut_pow_factorial (m : ℕ) : frobAut k m ^ m.factorial = 1 := RingEquiv.ext fun a ↦ by
  rw [frobAut_pow_apply]
  exact Subtype.ext (by rw [IntermediateField.coe_pow]; exact (mem_frobField k).mp a.2)

/-- The Frobenius fixes the elements of `k`. -/
theorem frobAut_algebraMap (m : ℕ) (a : k) :
    frobAut k m (algebraMap k (towerField k m) a) = algebraMap k (towerField k m) a :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic k (towerField k m)).commutes a

/-- Every power of the inverse Frobenius fixes the elements of `k`. -/
theorem frobAut_inv_pow_algebraMap (m e : ℕ) (a : k) :
    ((frobAut k m)⁻¹ ^ e) (algebraMap k (towerField k m) a) = algebraMap k (towerField k m) a := by
  have h : frobAut k m ∈ MulAction.stabilizer (RingAut (towerField k m))
      (algebraMap k (towerField k m) a) := frobAut_algebraMap k m a
  exact (pow_mem (inv_mem h) e : _ ∈ MulAction.stabilizer _ _)

/-- `ζ_m^{x n} = (ζ_m^x)^n` for `x : ℤ/N_m` and a natural number `n`. -/
theorem zetaPow_mul_natCast (m : ℕ) (x : ZMod (towerN k m)) (n : ℕ) :
    zetaPow k m (x * n) = zetaPow k m x ^ n := by
  have hx : zetaPow k m x ^ towerN k m = 1 := by
    rw [zetaPow, ← pow_mul, mul_comm, pow_mul, zetaUnit_pow, one_pow]
  rw [zetaPow_mul, ZMod.val_natCast, ← pow_eq_pow_mod n hx]

/-- `q⁻¹ mod N_m`. -/
abbrev qInvMod (m : ℕ) : ZMod (towerN k m) :=
  redN k m (qInv (Fintype.card k) : RestrictedProfiniteIntegers (Fintype.card k))

/-- `q⁻¹ · q = 1` in `ℤ/N_m`. -/
theorem qInvMod_mul_card (m : ℕ) : qInvMod k m * (Fintype.card k : ZMod (towerN k m)) = 1 := by
  rw [qInvMod, ← map_natCast (redN k m), ← map_mul, mul_comm, natCast_mul_qInv, map_one]

/-- `Frob⁻¹(ζ) = ζ^{q⁻¹}`. -/
theorem frobAut_inv_zeta (m : ℕ) :
    Units.map ((frobAut k m)⁻¹ : RingAut (towerField k m)).toMonoidHom (zetaUnit k m) =
      zetaPow k m (qInvMod k m) := by
  have h : Units.map (frobAut k m : RingAut (towerField k m)).toMonoidHom
      (zetaPow k m (qInvMod k m)) = zetaUnit k m := by
    apply Units.ext
    show frobAut k m ((zetaPow k m (qInvMod k m) : (towerField k m)ˣ) : towerField k m) = _
    rw [frobAut_apply, ← Units.val_pow_eq_pow_val, ← zetaPow_mul_natCast, qInvMod_mul_card,
      zetaPow_one]
  rw [← h]
  apply Units.ext
  show (frobAut k m).symm (frobAut k m _) = _
  rw [RingEquiv.symm_apply_apply]

/-- `Frob⁻ᵉ(ζ_m) = ζ_m^{q⁻ᵉ}`. -/
theorem frobAut_inv_pow_zeta (m e : ℕ) :
    Units.map (((frobAut k m)⁻¹ ^ e : RingAut (towerField k m))).toMonoidHom (zetaUnit k m) =
      zetaPow k m (qInvMod k m ^ e) := by
  induction e with
  | zero =>
    rw [pow_zero, pow_zero, zetaPow_one]
    rfl
  | succ e ih =>
    have h1 : Units.map (((frobAut k m)⁻¹ ^ (e + 1) : RingAut (towerField k m))).toMonoidHom
        (zetaUnit k m) = Units.map ((frobAut k m)⁻¹ : RingAut (towerField k m)).toMonoidHom
          (Units.map (((frobAut k m)⁻¹ ^ e : RingAut (towerField k m))).toMonoidHom
            (zetaUnit k m)) := by
      rw [pow_succ']
      rfl
    rw [h1, ih, zetaPow, map_pow, frobAut_inv_zeta, ← zetaPow_mul, pow_succ', mul_comm]

/-- `Frob⁻ᵉ(ζ_m) = ζ_m^{q⁻ᵉ}`, with `Frob⁻ᵉ` viewed through its underlying ring homomorphism. -/
theorem frobAut_inv_pow_zeta' (m e : ℕ) :
    Units.map (((frobAut k m)⁻¹ ^ e : RingAut (towerField k m))).toRingHom.toMonoidHom
      (zetaUnit k m) = zetaPow k m (qInvMod k m ^ e) :=
  frobAut_inv_pow_zeta k m e

/-- The action of `Ẑ^(q)`: `z ↦ (X ↦ ζ_m^{z mod N_m} X)`. -/
def actN (m : ℕ) :
    Multiplicative (RestrictedProfiniteIntegers (Fintype.card k)) →*
      RingAut (Ring (towerField k m)) where
  toFun z := scaleAut _ (zetaPow k m (redN k m (Multiplicative.toAdd z)))
  map_one' := by
    rw [toAdd_one, map_zero, zetaPow_zero, map_one]
  map_mul' z w := by
    rw [toAdd_mul, map_add, zetaPow_add, map_mul]

/-- The action of `Ẑ`: `d ↦ Frob^{-(d mod m!)}` on the coefficients. -/
def actF (m : ℕ) : Multiplicative ProfiniteIntegers →* RingAut (Ring (towerField k m)) where
  toFun d := coeffAut _ ((frobAut k m)⁻¹ ^ (redF m (Multiplicative.toAdd d)).val)
  map_one' := by
    rw [toAdd_one, map_zero, ZMod.val_zero, pow_zero, map_one]
  map_mul' d d' := by
    have hord : ((frobAut k m)⁻¹) ^ m.factorial = 1 := by
      rw [inv_pow, frobAut_pow_factorial, inv_one]
    rw [toAdd_mul, map_add, ZMod.val_add, ← pow_eq_pow_mod _ hord, pow_add, map_mul]

/-- For `d ∈ Ẑ` and `x ∈ Ẑ^(q)`, the action of `F^d x F^{-d} = q^{-d} x` is the conjugate of the
action of `x` by the action of `d`. -/
theorem actN_actF_compat (m : ℕ) (g : Multiplicative ProfiniteIntegers) :
    (actN k m).comp (frobeniusAut (inverseCharacter (Fintype.card k)) g).toMonoidHom =
      (MulAut.conj (actF k m g)).toMonoidHom.comp (actN k m) := by
  refine MonoidHom.ext fun n ↦ ?_
  show scaleAut _ (zetaPow k m (redN k m (Multiplicative.toAdd
      (frobeniusAut (inverseCharacter (Fintype.card k)) g n)))) =
    coeffAut _ ((frobAut k m)⁻¹ ^ (redF m (Multiplicative.toAdd g)).val) *
      scaleAut _ (zetaPow k m (redN k m (Multiplicative.toAdd n))) *
        (coeffAut _ ((frobAut k m)⁻¹ ^ (redF m (Multiplicative.toAdd g)).val))⁻¹
  have hφ : Multiplicative.toAdd (frobeniusAut (inverseCharacter (Fintype.card k)) g n) =
      ((inverseCharacter (Fintype.card k) g : (RestrictedProfiniteIntegers (Fintype.card k))ˣ) :
        RestrictedProfiniteIntegers (Fintype.card k)) * Multiplicative.toAdd n := rfl
  rw [coeffAut_mul_scaleAut_mul_inv, hφ, map_mul,
    restrictedMod_inverseCharacter (Fintype.card k) (towerN k m) (towerN_pos k m).ne'
      (towerN_coprime k m) (Nat.factorial_ne_zero m) (card_pow_eq_one_zmod k m)]
  congr 1
  rw [zetaPow_mul]
  conv_rhs => rw [zetaPow, map_pow, frobAut_inv_pow_zeta']

/-- **The action of `Γ` on the `m`-th layer** `𝔽_{m!}[X]_X` of the Kummer tower. -/
def deck (m : ℕ) : Gamma (inverseCharacter (Fintype.card k)) →* RingAut (Ring (towerField k m)) :=
  SemidirectProduct.lift (actN k m) (actF k m) (actN_actF_compat k m)

/-- An element `γ = (z, d)` of `Γ` acts by first applying the action of `d ∈ Ẑ`, then that of
`z ∈ Ẑ^(q)`. -/
theorem deck_apply (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k)))
    (z : Ring (towerField k m)) :
    deck k m γ z = actN k m γ.left (actF k m γ.right z) := rfl

end AlgebraicGeometry.TameMultiplicativeGroup

end
