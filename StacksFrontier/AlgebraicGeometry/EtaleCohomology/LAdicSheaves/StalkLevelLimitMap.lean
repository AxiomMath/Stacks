module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkMatrix

/-!
# Maps from the ℓ-adic stalk to `ℤ_ℓ^r` given level by level

Let `F` be an ℓ-adic sheaf and `s̄` a geometric point. Additive maps `Sₙ : (Fₙ)_s̄ → (ℤ/ℓⁿ⁺¹)^r`,
`ℤ_ℓ`-semilinear and compatible with the transitions and the reductions, have a limit: a
`ℤ_ℓ`-linear map `F_s̄ → ℤ_ℓ^r` whose reduction modulo `ℓⁿ⁺¹` is `Sₙ` on the `n`-th component
(`Stacks.EtaleCohomology.LAdicSheaf.stalkLevelLimitMap`). If the kernels of the `Sₙ` are killed by
`ℓᴹ`, so is the kernel of the limit. This is how the level maps
`(Gₙ)_ȳ → (j_* ℱ_{ρ,n})_ȳ ↪ (ℤ/ℓⁿ⁺¹)^r` of the specialization map of Laumon's degeneration
(`Stacks.EtaleCohomology.CurveSpecializationInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) assemble.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.stalkLevelLimitMap`: the `ℤ_ℓ`-linear map `F_s̄ → ℤ_ℓ^r`
  whose reductions are the level maps `Sₙ`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.toZModPow_stalkLevelLimitMap`: the reduction modulo `ℓⁿ⁺¹`
  of the limit map is `Sₙ`.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkLevelLimitMap_eq_iff`: the limit map is characterised by
  its reductions.
* `Stacks.EtaleCohomology.LAdicSheaf.pow_smul_eq_zero_of_stalkLevelLimitMap_eq_zero`: if `ℓᴹ`
  kills the kernel of every `Sₙ`, it kills the kernel of the limit map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime] {r : ℕ}
  {F : LAdicSheaf B X ℓ} {s : GeometricPoint X.1}
  (S : ∀ n, finiteLevelStalk B X ℓ F s n →+ (Fin r → ZMod (ℓ ^ (n + 1))))
  (hS : ∀ n (c : ℤ_[ℓ]) (w : finiteLevelStalk B X ℓ F s n),
    S n (c • w) = PadicInt.toZModPow (n + 1) c • S n w)
  (hT : ∀ n (y : finiteLevelStalk B X ℓ F s (n + 1)),
    S n (LAdicSheaf.stalkTransition B X ℓ F s n y) = levelReduction (n + 1) (S (n + 1) y))

include hT in
/-- For `v` in the stalk `F_s̄` and a coordinate `i`, there is `t : ℤ_ℓ` whose reduction modulo
`ℓⁿ⁺¹` is the `i`-th coordinate of `Sₙ` applied to the `n`-th component of `v`, for every `n`. -/
theorem LAdicSheaf.exists_toZModPow_eq_levelMap (v : LAdicSheaf.stalk B X ℓ F s) (i : Fin r) :
    ∃ t : ℤ_[ℓ], ∀ n, PadicInt.toZModPow (n + 1) t = S n (v.1 n) i :=
  exists_toZModPow_eq (fun n => S n (v.1 n) i) (fun n => by
    have := congrFun (hT n (v.1 (n + 1))) i
    rw [v.2 n] at this
    exact this.symm)

/-- **The limit `F_s̄ → ℤ_ℓ^r` of compatible level maps `(Fₙ)_s̄ → (ℤ/ℓⁿ⁺¹)^r`.** -/
public def LAdicSheaf.stalkLevelLimitMap :
    LAdicSheaf.stalk B X ℓ F s →ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ]) where
  toFun v i := (LAdicSheaf.exists_toZModPow_eq_levelMap S hT v i).choose
  map_add' v w := by
    funext i
    apply eq_of_toZModPow_succ_eq
    intro n
    rw [Pi.add_apply, map_add, (LAdicSheaf.exists_toZModPow_eq_levelMap S hT (v + w) i).choose_spec,
      (LAdicSheaf.exists_toZModPow_eq_levelMap S hT v i).choose_spec,
      (LAdicSheaf.exists_toZModPow_eq_levelMap S hT w i).choose_spec]
    change S n (v.1 n + w.1 n) i = _
    rw [map_add, Pi.add_apply]
  map_smul' c v := by
    funext i
    apply eq_of_toZModPow_succ_eq
    intro n
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul,
      (LAdicSheaf.exists_toZModPow_eq_levelMap S hT (c • v) i).choose_spec,
      (LAdicSheaf.exists_toZModPow_eq_levelMap S hT v i).choose_spec]
    change S n (c • v.1 n) i = _
    rw [hS, Pi.smul_apply, smul_eq_mul]

/-- The limit map reduces to the level maps. -/
public theorem LAdicSheaf.toZModPow_stalkLevelLimitMap (v : LAdicSheaf.stalk B X ℓ F s) (n : ℕ)
    (i : Fin r) :
    PadicInt.toZModPow (n + 1) (LAdicSheaf.stalkLevelLimitMap S hS hT v i) = S n (v.1 n) i :=
  (LAdicSheaf.exists_toZModPow_eq_levelMap S hT v i).choose_spec n

/-- **The limit map is characterised by its reductions.** -/
public theorem LAdicSheaf.stalkLevelLimitMap_eq_iff (v : LAdicSheaf.stalk B X ℓ F s)
    (w : Fin r → ℤ_[ℓ]) :
    LAdicSheaf.stalkLevelLimitMap S hS hT v = w ↔
      ∀ n, S n (v.1 n) = fun i => PadicInt.toZModPow (n + 1) (w i) := by
  refine ⟨fun h n => funext fun i => ?_, fun h => funext fun i => eq_of_toZModPow_succ_eq
    fun n => ?_⟩
  · rw [← toZModPow_stalkLevelLimitMap S hS hT, h]
  · rw [toZModPow_stalkLevelLimitMap S hS hT, h n]

/-- **A kernel bound on the levels bounds the kernel of the limit.** -/
public theorem LAdicSheaf.pow_smul_eq_zero_of_stalkLevelLimitMap_eq_zero (M : ℕ)
    (hM : ∀ n (w : finiteLevelStalk B X ℓ F s n), S n w = 0 → (ℓ ^ M : ℤ_[ℓ]) • w = 0)
    (v : LAdicSheaf.stalk B X ℓ F s) (hv : LAdicSheaf.stalkLevelLimitMap S hS hT v = 0) :
    (ℓ ^ M : ℤ_[ℓ]) • v = 0 := by
  rw [stalkLevelLimitMap_eq_iff] at hv
  refine Subtype.ext (funext fun n => ?_)
  show (ℓ ^ M : ℤ_[ℓ]) • v.1 n = 0
  refine hM n _ ((hv n).trans (funext fun i => ?_))
  simp

end Stacks.EtaleCohomology

end
