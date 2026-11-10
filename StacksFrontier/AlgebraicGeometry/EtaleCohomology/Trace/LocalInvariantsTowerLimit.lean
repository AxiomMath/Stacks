module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsLimit

/-!
# Integral invariant vectors into the limit of a tower, and their rationalization

Let `n ↦ Cₙ` be an inverse system of `ℤ_ℓ`-modules and let `Sₙ` be `ℤ_ℓ`-modules with transition
maps `Sₙ₊₁ → Sₙ` and injective maps `Ψₙ : Sₙ → Cₙ` compatible with the transitions. Suppose that
each `Sₙ` embeds into `(ℤ/ℓⁿ⁺¹)^r` by an injective semilinear `εₙ`, compatibly with the
transitions, and that a submodule `I ⊆ ℤ_ℓ^r` reduces into the images of the `εₙ`. Then
`v ↦ (Ψₙ (εₙ⁻¹ (v mod ℓⁿ⁺¹)))ₙ` is an injective `ℤ_ℓ`-linear map `I → lim Cₙ`
(`Stacks.EtaleCohomology.towerLimitLift`), and an integral matrix acting on both sides through
the levels is intertwined (`Stacks.EtaleCohomology.towerLimitLift_mulVec`).

For `I` the integral vectors of a `ℚ_ℓ`-subspace `I_ℚ ⊆ ℚ_ℓ^r`, `I_ℚ` is the base change of `I`
to `ℚ_ℓ`, and an injective `ℤ_ℓ`-linear `I → H` gives an injective `ℚ_ℓ`-linear
`I_ℚ → H ⊗ ℚ_ℓ` (`Stacks.EtaleCohomology.rationalLift`), since `ℚ_ℓ` is flat over `ℤ_ℓ`.

These are the algebraic steps from the levels `(j_* ℱₙ)_ȳ ↪ H¹_c(V_k̄, ℱₙ)` to the inclusion
`H⁰_loc ⊆ H¹_c(V_k̄, ℱ ⊗ ℚ_ℓ)` of Weil II 1.8
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.towerLimitLift`: the map `I → lim Cₙ`, `v ↦ (Ψₙ (εₙ⁻¹ (v mod ℓⁿ⁺¹)))ₙ`.
* `Stacks.EtaleCohomology.integralSubmodule`: the integral vectors of a `ℚ_ℓ`-subspace of `ℚ_ℓ^r`.
* `Stacks.EtaleCohomology.rationalLift`: the rationalization `I_ℚ → H ⊗ ℚ_ℓ` of a `ℤ_ℓ`-linear
  map `I → H`.

## Main results

* `Stacks.EtaleCohomology.injective_towerLimitLift`: the lift into the limit is injective when
  every `Ψₙ` is.
* `Stacks.EtaleCohomology.towerLimitLift_mulVec`: the lift into the limit intertwines an integral
  matrix acting through the levels.
* `Stacks.EtaleCohomology.injective_rationalLift`: the rationalization of an injective map is
  injective.
* `Stacks.EtaleCohomology.rationalLift_mulVec`: the rationalization intertwines an integral matrix.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Matrix TensorProduct ChangeOfRings

universe w

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-! ### The tower -/

section Tower

variable {S : ℕ → ModuleCat.{w} ℤ_[ℓ]} (ε : ∀ n, S n →+ (Fin r → ZMod (ℓ ^ (n + 1))))
  (hε : ∀ n, Function.Injective (ε n))
  (hεs : ∀ n (c : ℤ_[ℓ]) (w : S n), ε n (c • w) = PadicInt.toZModPow (n + 1) c • ε n w)
  (I : Submodule ℤ_[ℓ] (Fin r → ℤ_[ℓ]))
  (hI : ∀ v ∈ I, ∀ n, (fun i => PadicInt.toZModPow (n + 1) (v i)) ∈ Set.range (ε n))

/-- **The level-`n` lift** `v ↦ εₙ⁻¹ (v mod ℓⁿ⁺¹)` of an integral vector of `I`. -/
public def towerLevelLift (n : ℕ) : I →ₗ[ℤ_[ℓ]] S n where
  toFun v := (hI v.1 v.2 n).choose
  map_add' v v' := hε n (by
    rw [map_add, (hI _ (v + v').2 n).choose_spec, (hI _ v.2 n).choose_spec,
      (hI _ v'.2 n).choose_spec]
    funext i
    simp only [Submodule.coe_add, Pi.add_apply, map_add])
  map_smul' c v := hε n (by
    rw [RingHom.id_apply, hεs, (hI _ (c • v).2 n).choose_spec, (hI _ v.2 n).choose_spec]
    funext i
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, map_mul])

/-- `εₙ` takes the level-`n` lift of `v` to the reduction of `v` modulo `ℓⁿ⁺¹`. -/
public theorem towerLevelLift_spec (n : ℕ) (v : I) :
    ε n (towerLevelLift ε hε hεs I hI n v) = fun i => PadicInt.toZModPow (n + 1) (v.1 i) :=
  (hI v.1 v.2 n).choose_spec

/-- The level-`n` lift of `v` is any `w` with `εₙ w = v mod ℓⁿ⁺¹`. -/
public theorem towerLevelLift_eq (n : ℕ) (v : I) (w : S n)
    (h : ε n w = fun i => PadicInt.toZModPow (n + 1) (v.1 i)) :
    towerLevelLift ε hε hεs I hI n v = w :=
  hε n (by rw [towerLevelLift_spec, h])

variable (t : ∀ n, S (n + 1) ⟶ S n)
  (hεt : ∀ n (w : S (n + 1)), ε n ((t n).hom w) = fun i =>
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1))) (ε (n + 1) w i))

include hεt in
/-- The level lifts are compatible with the transitions. -/
public theorem towerLevelLift_transition (n : ℕ) (v : I) :
    (t n).hom (towerLevelLift ε hε hεs I hI (n + 1) v) = towerLevelLift ε hε hεs I hI n v := by
  refine (towerLevelLift_eq ε hε hεs I hI n v _ ?_).symm
  rw [hεt, towerLevelLift_spec]
  funext i
  rw [ZMod.castHom_apply]
  exact PadicInt.cast_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ (n + 1)) (v.1 i)

variable (C : ℕᵒᵖ ⥤ ModuleCat.{w} ℤ_[ℓ]) (Ψ : ∀ n, S n ⟶ C.obj (op n))
  (hΨ : ∀ n, t n ≫ Ψ n = Ψ (n + 1) ≫ C.map (homOfLE (n.le_add_right 1)).op)

/-- The cone over `n ↦ Cₙ` with vertex `I`, by `v ↦ Ψₙ (εₙ⁻¹ (v mod ℓⁿ⁺¹))`. -/
public def towerLimitCone : Cone C where
  pt := ModuleCat.of ℤ_[ℓ] (ULift.{w} I)
  π := NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom ((Ψ n).hom ∘ₗ towerLevelLift ε hε hεs I hI n ∘ₗ
      (ULift.moduleEquiv (R := ℤ_[ℓ]) (M := I)).toLinearMap))
    (fun n => by
      ext ⟨v⟩
      have h := congrArg (fun g => g.hom (towerLevelLift ε hε hεs I hI (n + 1) v)) (hΨ n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      change (Ψ n).hom (towerLevelLift ε hε hεs I hI n v) =
        (C.map (homOfLE (n.le_add_right 1)).op).hom
          ((Ψ (n + 1)).hom (towerLevelLift ε hε hεs I hI (n + 1) v))
      rw [← h, towerLevelLift_transition ε hε hεs I hI t hεt])

variable [HasLimit C]

/-- **The integral vectors of `I` into `lim Cₙ`**, `v ↦ (Ψₙ (εₙ⁻¹ (v mod ℓⁿ⁺¹)))ₙ`. -/
public def towerLimitLift : I →ₗ[ℤ_[ℓ]] (limit C : ModuleCat.{w} ℤ_[ℓ]) :=
  (limit.lift C (towerLimitCone ε hε hεs I hI t hεt C Ψ hΨ)).hom ∘ₗ
    (ULift.moduleEquiv (R := ℤ_[ℓ]) (M := I)).symm.toLinearMap

/-- The `n`-th component of the lift of `v` into the limit is `Ψₙ` of the level-`n` lift of `v`. -/
public theorem towerLimitLift_π (n : ℕ) (v : I) :
    (limit.π C (op n)).hom (towerLimitLift ε hε hεs I hI t hεt C Ψ hΨ v) =
      (Ψ n).hom (towerLevelLift ε hε hεs I hI n v) := by
  change ((limit.lift C (towerLimitCone ε hε hεs I hI t hεt C Ψ hΨ) ≫ limit.π C (op n)).hom
    (ULift.up v)) = _
  rw [limit.lift_π]
  rfl

/-- The `n`-th component of the lift of `v` into the limit is `Ψₙ w`, for any `w` with
`εₙ w = v mod ℓⁿ⁺¹`. -/
public theorem towerLimitLift_π_of_eq (n : ℕ) (v : I) (w : S n)
    (h : ε n w = fun i => PadicInt.toZModPow (n + 1) (v.1 i)) :
    (limit.π C (op n)).hom (towerLimitLift ε hε hεs I hI t hεt C Ψ hΨ v) = (Ψ n).hom w := by
  rw [towerLimitLift_π, towerLevelLift_eq ε hε hεs I hI n v w h]

/-- **The lift into the limit is injective** when every `Ψₙ` is. -/
public theorem injective_towerLimitLift (hΨi : ∀ n, Function.Injective (Ψ n).hom) :
    Function.Injective (towerLimitLift ε hε hεs I hI t hεt C Ψ hΨ) := by
  intro v v' h
  have hn : ∀ n, towerLevelLift ε hε hεs I hI n v = towerLevelLift ε hε hεs I hI n v' := fun n =>
    hΨi n (by rw [← towerLimitLift_π ε hε hεs I hI t hεt C Ψ hΨ,
      ← towerLimitLift_π ε hε hεs I hI t hεt C Ψ hΨ, h])
  refine Subtype.ext (funext fun i => PadicInt.ext_of_toZModPow.1 fun k => ?_)
  cases k with
  | zero =>
    have : Subsingleton (ZMod (ℓ ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ k =>
    have := congrArg (ε k) (hn k)
    rw [towerLevelLift_spec, towerLevelLift_spec] at this
    exact congrFun this i

/-- **The lift into the limit intertwines an integral matrix** `A` acting on the levels through
`aₙ` (by `A mod ℓⁿ⁺¹` on the `εₙ`-coordinates) with an endomorphism `c` of the limit lying over
endomorphisms `cₙ` of the `Cₙ` with `Ψₙ ∘ aₙ = cₙ ∘ Ψₙ`. -/
public theorem towerLimitLift_mulVec [PreservesLimit C (forget (ModuleCat.{w} ℤ_[ℓ]))]
    (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (a : ∀ n, S n ⟶ S n)
    (ha : ∀ n w, ε n ((a n).hom w) = (A.map (PadicInt.toZModPow (n + 1))) *ᵥ ε n w)
    (c : (limit C : ModuleCat.{w} ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] (limit C : ModuleCat.{w} ℤ_[ℓ]))
    (cn : ∀ n, C.obj (op n) →ₗ[ℤ_[ℓ]] C.obj (op n))
    (hc : ∀ n x, (limit.π C (op n)).hom (c x) = cn n ((limit.π C (op n)).hom x))
    (hac : ∀ n w, (Ψ n).hom ((a n).hom w) = cn n ((Ψ n).hom w))
    (v : I) (hv : A *ᵥ v.1 ∈ I) :
    towerLimitLift ε hε hεs I hI t hεt C Ψ hΨ ⟨_, hv⟩ =
      c (towerLimitLift ε hε hεs I hI t hεt C Ψ hΨ v) := by
  refine Concrete.limit_ext C _ _ fun n => ?_
  induction n using Opposite.rec with | op n => ?_
  change (limit.π C (op n)).hom _ = (limit.π C (op n)).hom _
  rw [hc, towerLimitLift_π, towerLimitLift_π, ← hac]
  congr 1
  refine towerLevelLift_eq ε hε hεs I hI n _ _ ?_
  rw [ha, towerLevelLift_spec]
  funext i
  exact (RingHom.map_mulVec (PadicInt.toZModPow (n + 1)) A v.1 i).symm

end Tower

/-! ### Rationalization -/

section Rational

variable (Irat : Submodule ℚ_[ℓ] (Fin r → ℚ_[ℓ]))

/-- **The integral vectors of a `ℚ_ℓ`-subspace** `I_ℚ ⊆ ℚ_ℓ^r`. -/
public abbrev integralSubmodule : Submodule ℤ_[ℓ] (Fin r → ℤ_[ℓ]) :=
  (Irat.restrictScalars ℤ_[ℓ]).comap padicVecInclusion

/-- The inclusion of the integral vectors into `I_ℚ`. -/
public def integralSubmoduleInclusion : integralSubmodule Irat →ₗ[ℤ_[ℓ]] Irat where
  toFun v := ⟨padicVecInclusion v.1, v.2⟩
  map_add' v v' := Subtype.ext (map_add padicVecInclusion v.1 v'.1)
  map_smul' c v := Subtype.ext (map_smul padicVecInclusion c v.1)

/-- The inclusion of the integral vectors into `I_ℚ` is `padicVecInclusion` on vectors. -/
public theorem integralSubmoduleInclusion_apply (v : integralSubmodule Irat) :
    (integralSubmoduleInclusion Irat v : Fin r → ℚ_[ℓ]) = padicVecInclusion v.1 :=
  rfl

/-- Some `ℓ`-power multiple of every rational vector is integral. -/
public theorem exists_padicVecInclusion_eq_pow_smul (z : Fin r → ℚ_[ℓ]) :
    ∃ (N : ℕ) (v : Fin r → ℤ_[ℓ]), padicVecInclusion v = ((ℓ : ℚ_[ℓ]) ^ N) • z := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ i, ‖z i‖)
    (Nat.one_lt_cast.2 (Fact.out : ℓ.Prime).one_lt : (1 : ℝ) < ℓ)
  have hle : ∀ i, ‖((ℓ : ℚ_[ℓ]) ^ N) * z i‖ ≤ 1 := fun i => by
    have hi : ‖z i‖ ≤ ∑ i, ‖z i‖ :=
      Finset.single_le_sum (f := fun i => ‖z i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow,
      inv_mul_le_iff₀ (pow_pos (Nat.cast_pos.2 (Fact.out : ℓ.Prime).pos) N), mul_one]
    exact hi.trans hN.le
  exact ⟨N, fun i => ⟨_, hle i⟩, funext fun i => rfl⟩

/-- **`I_ℚ` is the localization of its integral vectors.** -/
public instance isLocalizedModule_integralSubmoduleInclusion :
    IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) (integralSubmoduleInclusion Irat) where
  map_units s := by
    have hs : ((s : ℤ_[ℓ]) : ℚ_[ℓ]) ≠ 0 := by
      rw [ne_eq, PadicInt.coe_eq_zero]
      exact nonZeroDivisors.coe_ne_zero s
    refine (Module.End.isUnit_iff _).2 ⟨fun x y h => ?_, fun y => ?_⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at h
      exact Subtype.ext (smul_right_injective _ hs (congrArg Subtype.val h))
    · refine ⟨((s : ℤ_[ℓ]) : ℚ_[ℓ])⁻¹ • y, Subtype.ext ?_⟩
      rw [Module.algebraMap_end_apply]
      change ((s : ℤ_[ℓ]) : ℚ_[ℓ]) • (((s : ℤ_[ℓ]) : ℚ_[ℓ])⁻¹ • (y : Fin r → ℚ_[ℓ])) = y
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  surj y := by
    obtain ⟨N, v, hv⟩ := exists_padicVecInclusion_eq_pow_smul (y : Fin r → ℚ_[ℓ])
    have hvI : v ∈ integralSubmodule Irat := by
      change padicVecInclusion v ∈ Irat
      rw [hv]
      exact Irat.smul_mem _ y.2
    have hℓ : ((ℓ : ℤ_[ℓ]) ^ N) ∈ nonZeroDivisors ℤ_[ℓ] :=
      mem_nonZeroDivisors_of_ne_zero
        (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero))
    refine ⟨(⟨v, hvI⟩, ⟨_, hℓ⟩), Subtype.ext ?_⟩
    change ((ℓ : ℤ_[ℓ]) ^ N) • (y : Fin r → ℚ_[ℓ]) = padicVecInclusion v
    rw [hv, ← algebraMap_smul ℚ_[ℓ] ((ℓ : ℤ_[ℓ]) ^ N)]
    simp
  exists_of_eq {v v'} h := ⟨1, by
    rw [one_smul, one_smul]
    exact Subtype.ext (funext fun i => PadicInt.ext (congrFun (congrArg Subtype.val h) i))⟩

/-- **`I_ℚ = I ⊗ ℚ_ℓ`.** -/
public theorem isBaseChange_integralSubmoduleInclusion :
    IsBaseChange ℚ_[ℓ] (integralSubmoduleInclusion Irat) :=
  IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ_[ℓ]) ℚ_[ℓ] _

variable {Irat} (H : ModuleCat.{w} ℤ_[ℓ]) (L : integralSubmodule Irat →ₗ[ℤ_[ℓ]] H)

/-- `H ⊗_{ℤ_ℓ} ℚ_ℓ` as the extension of scalars of `H` and as a tensor product. -/
public def extendScalarsPadicEquiv :
    ((ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj H : Type w) ≃ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] H :=
  let f := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  let X := (ModuleCat.restrictScalars f).obj (ModuleCat.of ℚ_[ℓ] ℚ_[ℓ])
  letI : IsScalarTower ℤ_[ℓ] ℚ_[ℓ] X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ_[ℓ] ℚ_[ℓ]) (LinearEquiv.refl ℤ_[ℓ] H)

/-- The inverse of `extendScalarsPadicEquiv` sends `1 ⊗ m` to `1 ⊗ m`. -/
public theorem extendScalarsPadicEquiv_symm_tmul (m : H) :
    (extendScalarsPadicEquiv H).symm ((1 : ℚ_[ℓ]) ⊗ₜ m) =
      ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] m) :=
  rfl

/-- **The rationalization `I_ℚ → H ⊗ ℚ_ℓ`** of a `ℤ_ℓ`-linear `L : I → H`. -/
public def rationalLift :
    Irat →ₗ[ℚ_[ℓ]] ((ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj H : Type w) :=
  (extendScalarsPadicEquiv H).symm.toLinearMap ∘ₗ L.baseChange ℚ_[ℓ] ∘ₗ
    (isBaseChange_integralSubmoduleInclusion Irat).equiv.symm.toLinearMap

/-- The rationalization of `L` sends an integral vector `v` to `1 ⊗ L v`. -/
public theorem rationalLift_integralSubmoduleInclusion (v : integralSubmodule Irat) :
    rationalLift H L (integralSubmoduleInclusion Irat v) =
      ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] L v) := by
  simp only [rationalLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    IsBaseChange.equiv_symm_apply, LinearMap.baseChange_tmul]
  rfl

/-- **The rationalization of an injective map is injective**: `ℚ_ℓ` is flat over `ℤ_ℓ`. -/
public theorem injective_rationalLift (hL : Function.Injective L) :
    Function.Injective (rationalLift H L) := by
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  have h : Function.Injective (L.baseChange ℚ_[ℓ]) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap L hL
  exact (extendScalarsPadicEquiv H).symm.injective.comp
    (h.comp (isBaseChange_integralSubmoduleInclusion Irat).equiv.symm.injective)

/-- **The rationalization intertwines an integral matrix**: if `L (A v) = c (L v)` on the integral
vectors, then the rationalization carries `A` on `I_ℚ` to `c ⊗ ℚ_ℓ`. -/
public theorem rationalLift_mulVec (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (c : H ⟶ H)
    (hc : ∀ (v : integralSubmodule Irat) (hv : A *ᵥ v.1 ∈ integralSubmodule Irat),
      L ⟨_, hv⟩ = c.hom (L v))
    (z : Irat) (hz : (A.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) *ᵥ (z : Fin r → ℚ_[ℓ]) ∈ Irat) :
    rationalLift H L ⟨_, hz⟩ =
      ((ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map c).hom
        (rationalLift H L z) := by
  obtain ⟨N, v, hv⟩ := exists_padicVecInclusion_eq_pow_smul (z : Fin r → ℚ_[ℓ])
  have hvI : v ∈ integralSubmodule Irat := by
    change padicVecInclusion v ∈ Irat
    rw [hv]
    exact Irat.smul_mem _ z.2
  have hAv : padicVecInclusion (A *ᵥ v) =
      ((ℓ : ℚ_[ℓ]) ^ N) • ((A.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) *ᵥ (z : Fin r → ℚ_[ℓ])) := by
    rw [← Matrix.mulVec_smul, ← hv]
    funext i
    exact RingHom.map_mulVec (algebraMap ℤ_[ℓ] ℚ_[ℓ]) A v i
  have hAvI : A *ᵥ v ∈ integralSubmodule Irat := by
    change padicVecInclusion (A *ᵥ v) ∈ Irat
    rw [hAv]
    exact Irat.smul_mem _ hz
  have hℓ : ((ℓ : ℚ_[ℓ]) ^ N) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  refine smul_right_injective _ hℓ ?_
  change ((ℓ : ℚ_[ℓ]) ^ N) • rationalLift H L ⟨_, hz⟩ =
    ((ℓ : ℚ_[ℓ]) ^ N) • ((ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map c).hom
      (rationalLift H L z)
  rw [← map_smul, ← map_smul, ← map_smul]
  have e₁ : ((ℓ : ℚ_[ℓ]) ^ N) • (⟨_, hz⟩ : Irat) = integralSubmoduleInclusion Irat ⟨_, hAvI⟩ :=
    Subtype.ext hAv.symm
  have e₂ : ((ℓ : ℚ_[ℓ]) ^ N) • z = integralSubmoduleInclusion Irat ⟨_, hvI⟩ :=
    Subtype.ext hv.symm
  rw [e₁, e₂, rationalLift_integralSubmoduleInclusion, rationalLift_integralSubmoduleInclusion,
    hc ⟨v, hvI⟩ hAvI]
  rfl

end Rational

end Stacks.EtaleCohomology
