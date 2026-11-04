module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.EulerProduct

/-!
# The central character attached to the eigenvalues `u_v`

An eigenform `f` with `U_v f = u_v f` at every place has a central character `ω`, an idele
character trivial on `Oˣ` and on `Kˣ` with `ω(ϖ_v⁻¹) = u_v`
(`IsEigenform.exists_centralChar`). Conversely, for the converse construction of an eigenform
with prescribed eigenvalues one needs such an `ω` built from the `u_v`. An idele character
trivial on `Oˣ` factors through the divisor `div c = (ord_v c_v)_v`, so `ω` is
`c ↦ ∏_v u_v ^ (- ord_v c_v)`; it is trivial on `Kˣ` exactly when `∏_v u_v ^ (ord_v ξ) = 1`
for every `ξ ∈ Kˣ`, i.e. when `v ↦ u_v` is a character of the divisor class group.

For `u_v = q_v⁻¹ d_v` (the normalization `u_v = q_v⁻¹ det ρ(F_v)` of Stacks Tag 03VU) the factor
`q_v⁻¹` is harmless: `∏_v q_v ^ (ord_v ξ) = q ^ (deg div ξ) = 1` because principal divisors have
degree `0` (`centralCharacter_diagUnit_of_mul`). What remains is that `v ↦ d_v` kills principal
divisors, which for `d_v = det ρ(F_v)` is the unramified reciprocity law.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.divisorCharacter` — the character `D ↦ ∏_v a_v ^ D(v)` of
  the divisor group.
* `Stacks.Adeles.GlobalFunctionField.idelCharacter` — the idele character `c ↦ χ(div c)`.
* `Stacks.Adeles.GlobalFunctionField.centralCharacter` — `c ↦ ∏_v u_v ^ (- ord_v c_v)`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.centralCharacter_integral` — `ω` is trivial on `Oˣ`.
* `Stacks.Adeles.GlobalFunctionField.centralCharacter_localIdele_inv` — `ω(ϖ_v⁻¹) = u_v`.
* `Stacks.Adeles.GlobalFunctionField.centralCharacter_diagUnit` — `ω` is trivial on `Kˣ` when
  `v ↦ u_v` kills principal divisors.
* `Stacks.Adeles.GlobalFunctionField.divisorCharacter_residueCard_principalDivisor` —
  `∏_v q_v ^ (ord_v ξ) = 1`.
* `Stacks.Adeles.GlobalFunctionField.centralCharacter_diagUnit_of_mul` — for `u_v = q_v⁻¹ d_v`,
  `ω` is trivial on `Kˣ` when `v ↦ d_v` kills principal divisors.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, §11.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section KFree

variable {K : Type u} [Field K] {Λ : Type w} [CommRing Λ]

/-- The character `D ↦ ∏_v a_v ^ D(v)` of the divisor group, with value `a_v` at the prime
divisor `v`. -/
public def divisorCharacter (a : Place K → Λˣ) : Multiplicative (Place K →₀ ℤ) →* Λˣ where
  toFun D := (Multiplicative.toAdd D).prod fun v n => a v ^ n
  map_one' := Finsupp.prod_zero_index
  map_mul' _ _ := Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

/-- `divisorCharacter a` sends the divisor `D` to `∏_v a_v ^ D(v)`. -/
public theorem divisorCharacter_ofAdd (a : Place K → Λˣ) (D : Place K →₀ ℤ) :
    divisorCharacter a (Multiplicative.ofAdd D) = D.prod fun v n => a v ^ n := rfl

/-- The value of `divisorCharacter a` at the prime divisor `v` is `a_v`. -/
@[simp]
public theorem primeValue_divisorCharacter (a : Place K → Λˣ) (v : Place K) :
    primeValue (divisorCharacter a) v = a v := by
  rw [primeValue, divisorCharacter_ofAdd, Finsupp.prod_single_index (zpow_zero _), zpow_one]

/-- `divisorCharacter` is multiplicative in the values `a_v`. -/
public theorem divisorCharacter_mul (a b : Place K → Λˣ) :
    divisorCharacter (a * b) = divisorCharacter a * divisorCharacter b := by
  refine MonoidHom.ext fun D => ?_
  change (Multiplicative.toAdd D).prod (fun v n => (a * b) v ^ n) =
    (Multiplicative.toAdd D).prod (fun v n => a v ^ n) * (Multiplicative.toAdd D).prod
      (fun v n => b v ^ n)
  simp only [Pi.mul_apply, mul_zpow, Finsupp.prod_mul]

/-- `divisorCharacter` of the inverse values is the inverse character. -/
public theorem divisorCharacter_inv (a : Place K → Λˣ) :
    divisorCharacter a⁻¹ = (divisorCharacter a)⁻¹ := by
  refine MonoidHom.ext fun D => ?_
  change (Multiplicative.toAdd D).prod (fun v n => a⁻¹ v ^ n) =
    ((Multiplicative.toAdd D).prod (fun v n => a v ^ n))⁻¹
  simp only [Pi.inv_apply, inv_zpow, Finsupp.prod_inv]

/-- Every character of the divisor group is `divisorCharacter` of its values at the prime
divisors. -/
public theorem divisorCharacter_primeValue (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ) :
    divisorCharacter (primeValue χ) = χ := by
  refine MonoidHom.ext fun D => ?_
  induction D using Multiplicative.rec with | ofAdd D => ?_
  induction D using Finsupp.induction_linear with
  | zero => rw [ofAdd_zero, map_one, map_one]
  | add D E hD hE => rw [ofAdd_add, map_mul, map_mul, hD, hE]
  | single v n =>
    rw [divisorCharacter_ofAdd, Finsupp.prod_single_index (zpow_zero _), primeValue, ← map_zpow,
      ← ofAdd_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [CommRing Λ]

/-- The idele character `c ↦ χ(div c)` attached to a character `χ` of the divisor group. -/
public def idelCharacter (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ) : (AdeleRing K)ˣ →* Λˣ where
  toFun c := χ (Multiplicative.ofAdd (idelDiv k K c))
  map_one' := by rw [idelDiv_one k, ofAdd_zero, map_one]
  map_mul' c c' := by rw [idelDiv_mul k, ofAdd_add, map_mul]

/-- `idelCharacter k χ` sends the idele `c` to `χ(div c)`. -/
public theorem idelCharacter_apply (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (c : (AdeleRing K)ˣ) : idelCharacter k χ c = χ (Multiplicative.ofAdd (idelDiv k K c)) := rfl

/-- `χ(div c)` is trivial on `Oˣ`. -/
public theorem idelCharacter_integral (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (o : (integralAdeles K)ˣ) :
    idelCharacter k χ (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1 := by
  rw [idelCharacter_apply, idelDiv_units_map_integralAdeles, ofAdd_zero, map_one]

/-- `χ(div ϖ_v⁻¹) = χ(v)⁻¹` for a uniformizer `ϖ_v`. -/
public theorem idelCharacter_localIdele_inv (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (v : Place K) {π : v.integers} (hπ : Place.IsUniformizer v π) :
    idelCharacter k χ (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) =
      (primeValue χ v)⁻¹ := by
  rw [idelCharacter_apply, idelDiv_localIdele k,
    ordC_inv_of_isUniformizer (isDiscrete k v) hπ (coe_ne_zero_of_isUniformizer k hπ),
    map_ofAdd_single_neg_one]

/-- `χ(div c)` is trivial on `Kˣ` when `χ` kills principal divisors. -/
public theorem idelCharacter_diagUnit {χ : Multiplicative (Place K →₀ ℤ) →* Λˣ}
    (hχ : ∀ κ : K, κ ≠ 0 → χ (Multiplicative.ofAdd (principalDivisor k K κ)) = 1) {κ : K}
    (hκ : κ ≠ 0) : idelCharacter k χ (diagUnit k hκ) = 1 := by
  rw [idelCharacter_apply, idelDiv_diagUnit, hχ κ hκ]

variable (K) in
/-- **The central character attached to `u`**: the idele character
`c ↦ ∏_v u_v ^ (- ord_v c_v)`, trivial on `Oˣ`, with `ω(ϖ_v⁻¹) = u_v`. -/
public def centralCharacter (u : Place K → Λˣ) : (AdeleRing K)ˣ →* Λˣ :=
  idelCharacter k (divisorCharacter u⁻¹)

/-- The central character is trivial on `Oˣ`. -/
public theorem centralCharacter_integral (u : Place K → Λˣ) (o : (integralAdeles K)ˣ) :
    centralCharacter k K u (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1 :=
  idelCharacter_integral k _ o

/-- `ω(ϖ_v⁻¹) = u_v`. -/
public theorem centralCharacter_localIdele_inv (u : Place K → Λˣ) (v : Place K) {π : v.integers}
    (hπ : Place.IsUniformizer v π) :
    centralCharacter k K u (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) =
      u v := by
  rw [centralCharacter, idelCharacter_localIdele_inv k _ v hπ, primeValue_divisorCharacter,
    Pi.inv_apply, inv_inv]

/-- `ω` is trivial on `Kˣ` when `v ↦ u_v` kills principal divisors. -/
public theorem centralCharacter_diagUnit {u : Place K → Λˣ}
    (hu : ∀ κ : K, κ ≠ 0 → divisorCharacter u (Multiplicative.ofAdd (principalDivisor k K κ)) = 1)
    {κ : K} (hκ : κ ≠ 0) : centralCharacter k K u (diagUnit k hκ) = 1 := by
  refine idelCharacter_diagUnit k (fun κ hκ => ?_) hκ
  rw [divisorCharacter_inv, MonoidHom.inv_apply, hu κ hκ, inv_one]

/-- `∏_v q_v ^ D(v) = q ^ (deg D)`. -/
public theorem divisorCharacter_residueCard (hq : ∀ v : Place K, IsUnit (v.residueCard : Λ))
    (hk : IsUnit (Nat.card k : Λ)) (D : Place K →₀ ℤ) :
    divisorCharacter (fun v => (hq v).unit) (Multiplicative.ofAdd D) =
      hk.unit ^ Stacks.Drinfeld.divisorDegree k K D := by
  induction D using Finsupp.induction_linear with
  | zero => rw [ofAdd_zero, map_one, map_zero, zpow_zero]
  | add D E hD hE => rw [ofAdd_add, map_mul, hD, hE, map_add, zpow_add]
  | single v n =>
    rw [divisorCharacter_ofAdd, Finsupp.prod_single_index (zpow_zero _),
      Stacks.Drinfeld.divisorDegree, Finsupp.linearCombination_single, smul_eq_mul,
      _root_.mul_comm, zpow_mul, zpow_natCast]
    congr 1
    ext
    rw [IsUnit.unit_spec, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Place.residueCard_eq_resCard,
      Stacks.Drinfeld.resCard_eq_pow_placeDegree k v, Nat.cast_pow]

/-- **`∏_v q_v ^ (ord_v ξ) = 1` for `ξ ∈ Kˣ`**: principal divisors have degree `0`. -/
public theorem divisorCharacter_residueCard_principalDivisor
    (hq : ∀ v : Place K, IsUnit (v.residueCard : Λ)) (hk : IsUnit (Nat.card k : Λ)) {κ : K}
    (hκ : κ ≠ 0) :
    divisorCharacter (fun v => (hq v).unit) (Multiplicative.ofAdd (principalDivisor k K κ)) =
      1 := by
  rw [divisorCharacter_residueCard k hq hk, Stacks.Drinfeld.divisorDegree_principalDivisor k hκ,
    zpow_zero]

/-- **The central character for `u_v = q_v⁻¹ d_v`.** If `p` is invertible in `Λ`, `q_v u_v = d_v`
and `v ↦ d_v` kills principal divisors, then `ω = centralCharacter u` is trivial on `Kˣ`. -/
public theorem centralCharacter_diagUnit_of_mul (hp : IsUnit (ringChar k : Λ))
    {u d : Place K → Λˣ}
    (hud : ∀ v, (v.residueCard : Λ) * u v = d v)
    (hd : ∀ κ : K, κ ≠ 0 → divisorCharacter d (Multiplicative.ofAdd (principalDivisor k K κ)) = 1)
    {κ : K} (hκ : κ ≠ 0) : centralCharacter k K u (diagUnit k hκ) = 1 := by
  have hq : ∀ v : Place K, IsUnit (v.residueCard : Λ) := isUnit_residueCard k hp
  have hk : IsUnit (Nat.card k : Λ) := by
    have := Fintype.ofFinite k
    have := ringChar.charP k
    obtain ⟨n, -, hn⟩ := FiniteField.card k (ringChar k)
    rw [Nat.card_eq_fintype_card, hn, Nat.cast_pow]
    exact hp.pow _
  have hu : u = (fun v => (hq v).unit)⁻¹ * d := by
    funext v
    rw [Pi.mul_apply, Pi.inv_apply, eq_inv_mul_iff_mul_eq]
    ext
    rw [Units.val_mul, IsUnit.unit_spec, hud]
  refine centralCharacter_diagUnit k (fun κ hκ => ?_) hκ
  rw [hu, divisorCharacter_mul, divisorCharacter_inv, MonoidHom.mul_apply, MonoidHom.inv_apply,
    divisorCharacter_residueCard_principalDivisor k hq hk hκ, hd κ hκ, inv_one, one_mul]

end Stacks.Adeles.GlobalFunctionField

end
