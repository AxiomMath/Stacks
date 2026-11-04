module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilChernCharacter

/-!
# The comparison of all twists along a field extension

For the comparison data `Φ` of Tag 0FVT between data `𝔇` for `(k, F)` and `𝔇'` for `(k', F')`,
the comparison `H^*(X) → (H')^*(X_{k'})`, `v ↦ ψ(1 ⊗ v)`, extends to every twist
`H^*(X)(n) → (H')^*(X_{k'})(n)`. In the canonical coordinates `κ` of the twists it is the
comparison of the untwisted algebras times `u^n`, where `u ∈ F'` is the nonzero scalar
`Stacks.WeilCohomology.FieldExtensionComparison.tateUnit` comparing the coordinates of `F(1)` and
`F'(1)`; for `n = 1` this is the comparison `twistOne` of the first twists.

## Main definitions

* `Stacks.WeilCohomology.FieldExtensionComparison.twist`: the comparison of `n`-th twists.
* `Stacks.WeilCohomology.FieldExtensionComparison.twistFamily`: the comparison of twists applied
  degreewise to a family in `∏_{n ≥ 0} H^*(X)(n)`.

## Main results

* `Stacks.WeilCohomology.FieldExtensionComparison.twist_one_eq_twistOne`: at `n = 1` it is the
  comparison of first twists.
* `twist_pullTw`, `twist_tateCup`, `twist_unitTw`: it commutes with pullbacks and cup products and
  preserves the unit.
* `twistFamily_cupConv`, `twistFamily_oneConv`, `twistFamily_expTw`: degreewise it commutes with
  the cup product of `∏_{n ≥ 0} H^*(X)(n)`, preserves its unit and commutes with the exponential.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- **The comparison of `n`-th twists** `H^*(X)(n) → (H')^*(X_{k'})(n)`, in coordinates
`κ'(x') = u^n ψ(1 ⊗ κ(x))`. -/
def twist (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (x : tateTwist F 𝔇.tate (𝔇.H X) n) :
    tateTwist F' 𝔇'.tate (𝔇'.H ((baseChange k k').obj X)) n :=
  (𝔇'.κ _ n).symm (Φ.tateUnit ^ n • Φ.ρ X (𝔇.κ X n x))

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- In the coordinates `κ` and `κ'`, the comparison of `n`-th twists is `x ↦ u^n ρ(κ(x))`. -/
theorem κ_twist (n : ℤ) (x : tateTwist F 𝔇.tate (𝔇.H X) n) :
    𝔇'.κ _ n (Φ.twist X n x) = Φ.tateUnit ^ n • Φ.ρ X (𝔇.κ X n x) :=
  LinearEquiv.apply_symm_apply _ _

/-- To identify `Φ.twist X n x` with `y`, it suffices to compare coordinates. -/
private theorem twist_eq_of_κ_eq {n : ℤ} {x : tateTwist F 𝔇.tate (𝔇.H X) n}
    {y : tateTwist F' 𝔇'.tate (𝔇'.H ((baseChange k k').obj X)) n}
    (h : Φ.tateUnit ^ n • Φ.ρ X (𝔇.κ X n x) = 𝔇'.κ _ n y) : Φ.twist X n x = y :=
  (𝔇'.κ _ n).injective (by rw [κ_twist, h])

/-- The comparison of `n`-th twists is injective. -/
theorem twist_injective (n : ℤ) : Function.Injective (Φ.twist X n) := by
  intro x y h
  have h1 := congrArg (𝔇'.κ _ n) h
  rw [κ_twist, κ_twist] at h1
  exact (𝔇.κ X n).injective <| injective_one_tmul (F := F) (V := 𝔇.H X) F' <|
    (Φ.iso X).injective <| smul_right_injective _ (zpow_ne_zero n Φ.tateUnit_ne_zero) h1

/-- The comparison of `n`-th twists sends `0` to `0`. -/
@[simp]
theorem twist_zero (n : ℤ) : Φ.twist X n 0 = 0 := by
  apply twist_eq_of_κ_eq
  rw [map_zero, map_zero, smul_zero, map_zero]

/-- The comparison of `n`-th twists is additive. -/
theorem twist_add (n : ℤ) (x y : tateTwist F 𝔇.tate (𝔇.H X) n) :
    Φ.twist X n (x + y) = Φ.twist X n x + Φ.twist X n y := by
  apply twist_eq_of_κ_eq
  rw [map_add, map_add, map_add, κ_twist, κ_twist, smul_add]

/-- `ρ` is semilinear along `algebraMap F F'`. -/
theorem ρ_smul (c : F) (v : 𝔇.H X) : Φ.ρ X (c • v) = algebraMap F F' c • Φ.ρ X v :=
  Φ.iso_one_tmul_smul X c v

/-- The comparison of `n`-th twists is semilinear along `algebraMap F F'`. -/
theorem twist_smul (n : ℤ) (c : F) (x : tateTwist F 𝔇.tate (𝔇.H X) n) :
    Φ.twist X n (c • x) = algebraMap F F' c • Φ.twist X n x := by
  apply twist_eq_of_κ_eq
  rw [map_smul, ρ_smul, map_smul, κ_twist, smul_comm]

/-- The comparison of `n`-th twists commutes with finite sums. -/
theorem twist_sum (n : ℤ) {ι : Type*} (s : Finset ι) (x : ι → tateTwist F 𝔇.tate (𝔇.H X) n) :
    Φ.twist X n (∑ i ∈ s, x i) = ∑ i ∈ s, Φ.twist X n (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, twist_add, ih, Finset.sum_insert hi]

/-- `ρ` preserves the grading. -/
theorem ρ_mem_grade (n : ℤ) (v : 𝔇.H X) (hv : v ∈ 𝔇.grade X n) :
    Φ.ρ X v ∈ 𝔇'.grade ((baseChange k k').obj X) n :=
  Φ.iso_grade X n v hv

/-- `ρ` commutes with pullbacks. -/
theorem ρ_pull {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (v : 𝔇.H Y) :
    Φ.ρ X (𝔇.pull f v) = 𝔇'.pull ((baseChange k k').map f) (Φ.ρ Y v) :=
  Φ.iso_natural f v

/-- **At `n = 1` the comparison of twists is that of first twists.** -/
theorem twist_one_eq_twistOne (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    Φ.twist X 1 x = Φ.twistOne X x := by
  apply twist_eq_of_κ_eq
  rw [κ_twistOne, zpow_one]
  rfl

/-- The comparison of twists commutes with pullbacks. -/
theorem twist_pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (x : tateTwist F 𝔇.tate (𝔇.H Y) n) :
    Φ.twist X n (𝔇.pullTw f n x) = 𝔇'.pullTw ((baseChange k k').map f) n (Φ.twist Y n x) := by
  apply twist_eq_of_κ_eq
  rw [FirstChernClassData.κ_pullTw, FirstChernClassData.κ_pullTw, κ_twist, map_smul,
    ρ_pull]

/-- The comparison of twists commutes with cup products. -/
theorem twist_tateCup (n m l : ℤ) (h : n + m = l) (x : tateTwist F 𝔇.tate (𝔇.H X) n)
    (y : tateTwist F 𝔇.tate (𝔇.H X) m) :
    Φ.twist X l (tateCup 𝔇.finrank_tate (𝔇.cup X) n m l h x y) =
      tateCup 𝔇'.finrank_tate (𝔇'.cup _) n m l h (Φ.twist X n x) (Φ.twist X m y) := by
  apply twist_eq_of_κ_eq
  rw [FirstChernClassData.κ_tateCup, FirstChernClassData.κ_tateCup, κ_twist, κ_twist, map_mul,
    smul_mul_smul_comm, ← h, zpow_add₀ Φ.tateUnit_ne_zero]

/-- The comparison of twists sends the unit to the unit. -/
theorem twist_unitTw : Φ.twist X 0 (𝔇.unitTw X) = 𝔇'.unitTw _ := by
  apply twist_eq_of_κ_eq
  rw [FirstChernClassData.κ_unitTw, FirstChernClassData.κ_unitTw, map_one, zpow_zero, one_smul]

/-- The comparison of twists applied degreewise to a family `(a_n)_{n ≥ 0}`. -/
def twistFamily (a : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n) :
    ∀ n : ℕ, tateTwist F' 𝔇'.tate (𝔇'.H ((baseChange k k').obj X)) n :=
  fun n => Φ.twist X n (a n)

/-- The coordinate formula `κ'(x') = u^n ρ(κ(x))` for a natural number `n`. -/
theorem κ_twist_nat (n : ℕ) (x : tateTwist F 𝔇.tate (𝔇.H X) n) :
    𝔇'.κ _ n (Φ.twist X n x) = Φ.tateUnit ^ n • Φ.ρ X (𝔇.κ X n x) := by
  rw [κ_twist, zpow_natCast]

/-- The comparison of twists commutes with the cup product of `∏_{n ≥ 0} H^*(X)(n)`. -/
theorem twistFamily_cupConv (a b : ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n) :
    Φ.twistFamily X (𝔇.cupConv X a b) =
      𝔇'.cupConv _ (Φ.twistFamily X a) (Φ.twistFamily X b) := by
  funext n
  simp only [twistFamily, FirstChernClassData.cupConv]
  rw [twist_sum]
  exact Finset.sum_congr rfl fun i _ => Φ.twist_tateCup X _ _ _ _ _ _

/-- The comparison of twists sends the unit of `∏_{n ≥ 0} H^*(X)(n)` to the unit. -/
theorem twistFamily_oneConv : Φ.twistFamily X (𝔇.oneConv X) = 𝔇'.oneConv _ := by
  funext n
  rcases n with _ | n
  · exact Φ.twist_unitTw X
  · simp only [twistFamily, FirstChernClassData.oneConv]
    rw [Pi.single_eq_of_ne (Nat.succ_ne_zero n), Pi.single_eq_of_ne (Nat.succ_ne_zero n),
      twist_zero]

/-- The comparison of twists commutes with the exponential. -/
theorem twistFamily_expTw (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    Φ.twistFamily X (𝔇.expTw X x) = 𝔇'.expTw _ (Φ.twist X 1 x) := by
  funext n
  apply twist_eq_of_κ_eq
  rw [FirstChernClassData.expTw, FirstChernClassData.expTw,
    LinearEquiv.map_smul (𝔇.κ X n), LinearEquiv.map_smul (𝔇'.κ _ n),
    FirstChernClassData.κ_twistPow, FirstChernClassData.κ_twistPow, κ_twist, zpow_one, ρ_smul,
    zpow_natCast, map_pow, smul_pow, map_inv₀, map_natCast, smul_comm]

end FieldExtensionComparison

end Stacks.WeilCohomology
