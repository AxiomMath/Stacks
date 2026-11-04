module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower

/-!
# The powers of the endomorphism of a tower of perfect complexes

Let `(Kₙ, πₙ, φₙ)` be a tower of perfect complexes over `ℤ/ℓⁿ⁺¹ℤ` in the sense of
[Stacks, Tag 03V4].  For every `m` the powers `πₙ ^ m` are again compatible with the
comparisons, so `(Kₙ, πₙ ^ m, φₙ)` is a tower, `PerfectTower.pow`.  Its limit cohomology is that
of the original tower, with endomorphism `(πⁱ_∞) ^ m`, so part (3) of Tag 03V4 applied to it reads

`∑ᵢ (-1)ⁱ Tr((πⁱ_∞) ^ m | Hⁱ_∞ ⊗ ℚ_ℓ) = t_∞(πᵐ)`,

where `t_∞(πᵐ) ∈ ℤ_ℓ` is the `ℓ`-adic limit of the traces `Tr(πₙ ^ m | Kₙ)`.  These are the
coefficients of the logarithmic derivative of the characteristic series of the tower.

## Main definitions

* `Stacks.InverseSystem.PerfectTower.pow`: the tower `(Kₙ, πₙ ^ m, φₙ)`.

## Main results

* `Stacks.InverseSystem.limitCohomologyEndo_pow`: its limit endomorphism is `(πⁱ_∞) ^ m`.
* `Stacks.InverseSystem.alternating_trace_pow_eq_padicTrace`: Tag 03V4 (3) for the powers.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe v

namespace Stacks.InverseSystem

attribute [local instance] HasDerivedCategory.standard

variable {ℓ : ℕ}

/-- `πᵐ⁺¹ = π ≫ πᵐ` for the powers of an endomorphism. -/
theorem _root_.CategoryTheory.End.asHom_of_pow_succ {C : Type*} [Category* C] {Y : C}
    (e : Y ⟶ Y) (m : ℕ) : End.asHom (End.of e ^ (m + 1)) = e ≫ End.asHom (End.of e ^ m) :=
  rfl

/-- The compatibility of the comparisons with the powers of the endomorphisms. -/
theorem PerfectTower.endo_pow_compatible (T : PerfectTower.{v} ℓ) (n m : ℕ) :
    End.asHom (End.of (T.endo (n + 1)) ^ m) ≫ T.transition n =
      T.transition n ≫ (levelRestrict.{v} ℓ n).map (End.asHom (End.of (T.endo n) ^ m)) := by
  induction m with
  | zero =>
    show 𝟙 _ ≫ T.transition n = T.transition n ≫ (levelRestrict.{v} ℓ n).map (𝟙 _)
    simp
  | succ m ih =>
    rw [End.asHom_of_pow_succ, End.asHom_of_pow_succ, Category.assoc, ih, ← Category.assoc,
      T.endo_compatible n, Functor.map_comp, Category.assoc]

/-- The tower `(Kₙ, πₙ ^ m, φₙ)`. -/
public def PerfectTower.pow (T : PerfectTower.{v} ℓ) (m : ℕ) : PerfectTower.{v} ℓ where
  obj := T.obj
  isPerfect := T.isPerfect
  endo n := End.asHom (End.of (T.endo n) ^ m)
  transition := T.transition
  comparison_isIso := T.comparison_isIso
  endo_compatible n := T.endo_pow_compatible n m

/-- On level cohomology the endomorphism of `T.pow m` is the `m`-th power of `Hⁱ(πₙ)`. -/
theorem levelCohomologyEndoHom_pow (T : PerfectTower.{v} ℓ) (m : ℕ) (i : ℤ) (n : ℕ) :
    levelCohomologyEndoHom (T.pow m) i n =
      End.asHom (End.of (levelCohomologyEndoHom T i n) ^ m) :=
  map_pow (Functor.mapEnd (T.obj n)
    (DerivedCategory.homologyFunctor (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) i)) _ m

variable [Fact ℓ.Prime]

/-- The powers of `Hⁱ(πₙ)`, read as `ℤ_ℓ`-linear maps. -/
theorem levelCohomologyEndoₗ_pow_apply (T : PerfectTower.{v} ℓ) (m : ℕ) (i : ℤ) (n : ℕ)
    (x : levelCohomology T i n) :
    (levelCohomologyEndoₗ T i n ^ m) x =
      (End.asHom (End.of (levelCohomologyEndoHom T i n) ^ m)).hom x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ (levelCohomologyEndoₗ T i n), Module.End.mul_apply, ih, End.asHom_of_pow_succ,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl

/-- The `ℤ_ℓ`-linear endomorphism of the level cohomology of `T.pow m` is the `m`-th power of
that of `T`. -/
theorem levelCohomologyEndoₗ_pow (T : PerfectTower.{v} ℓ) (m : ℕ) (i : ℤ) (n : ℕ)
    (x : levelCohomology T i n) :
    levelCohomologyEndoₗ (T.pow m) i n x = (levelCohomologyEndoₗ T i n ^ m) x := by
  have h : (levelCohomologyEndoHom (T.pow m) i n).hom x =
      (End.asHom (End.of (levelCohomologyEndoHom T i n) ^ m)).hom x := by
    rw [levelCohomologyEndoHom_pow]
    rfl
  exact h.trans (levelCohomologyEndoₗ_pow_apply T m i n x).symm

/-- The powers of `πⁱ_∞` act levelwise by the powers of `Hⁱ(πₙ)`. -/
theorem limitCohomologyEndo_pow_apply (T : PerfectTower.{v} ℓ) (m : ℕ) (i : ℤ) (n : ℕ)
    (a : limitCohomology T i) :
    ((limitCohomologyEndo T i ^ m) a).1 n = (levelCohomologyEndoₗ T i n ^ m) (a.1 n) := by
  rw [Module.End.pow_apply, Module.End.pow_apply]
  exact Function.Semiconj.iterate_right (f := fun a : limitCohomology T i => a.1 n)
    (fun _ => rfl) m a

/-- The limit cohomology of `T.pow m` is that of `T`, with limit endomorphism `(πⁱ_∞) ^ m`. -/
public theorem limitCohomologyEndo_pow (T : PerfectTower.{v} ℓ) (m : ℕ) (i : ℤ) :
    limitCohomologyEndo (T.pow m) i = limitCohomologyEndo T i ^ m := by
  ext a n
  exact (levelCohomologyEndoₗ_pow T m i n (a.1 n)).trans
    (limitCohomologyEndo_pow_apply T m i n a).symm

/-- **Tag 03V4, part (3), for the powers of the endomorphism.** The alternating sum of the traces
of `(πⁱ_∞) ^ m` on `Hⁱ_∞ ⊗_{ℤ_ℓ} ℚ_ℓ` is the `ℓ`-adic trace `t_∞(πᵐ)` of the tower
`(Kₙ, πₙ ^ m)`. -/
public theorem alternating_trace_pow_eq_padicTrace (T : PerfectTower.{v} ℓ) (m : ℕ) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] limitCohomology T i)
          (LinearMap.baseChange ℚ_[ℓ] (limitCohomologyEndo T i) ^ m) =
      (padicTrace (T.pow m) : ℚ_[ℓ]) := by
  refine Eq.trans (finsum_congr fun i => ?_) (alternating_trace_eq_padicTrace (T.pow m))
  rw [← LinearMap.baseChange_pow]
  exact congrArg (fun g : limitCohomology T i →ₗ[ℤ_[ℓ]] limitCohomology T i =>
    (if Even i then (1 : ℚ_[ℓ]) else -1) *
      LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] limitCohomology T i) (LinearMap.baseChange ℚ_[ℓ] g))
    (limitCohomologyEndo_pow T m i).symm

end Stacks.InverseSystem

end
