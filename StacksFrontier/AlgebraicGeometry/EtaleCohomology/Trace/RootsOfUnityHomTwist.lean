module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTateTwistCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantSecondCohomology

/-!
# The Tate twist `M(-1) = Hom(μ_n, M)` without a choice of root of unity

Let `k^{sep}` be a separably closed extension of `k` in which `n` is invertible and `M` a
`Λ`-module with an action `τ` of `Gal(k^{sep}/k)`.  The canonical model of the Tate twist `M(-1)`
is `Hom(μ_n(k^{sep}), M)` with `σ` acting by `f ↦ τ(σ) ∘ f ∘ σ⁻¹`.  Evaluation at any `n`-th root
of unity `ζ` is equivariant from it to the twist `Stacks.EtaleCohomology.tateTwistNegOne` of the
source (the same module, `σ` acting by `χ_cycl(σ)⁻¹ τ(σ)`), and at a primitive `ζ` it is bijective
when `n M = 0`.  So the two forms of `(-1)` agree, the first one with no choice made.

## Main definitions

* `Stacks.EtaleCohomology.rootsOfUnityLog` — `μ_n ≅ ℤ/n`, `ζ^a ↦ a`, for a primitive `ζ`.
* `Stacks.EtaleCohomology.rootsOfUnityHomRepresentation` — the action on `Hom(μ_n, M)`.
* `Stacks.EtaleCohomology.rootsOfUnityHomEvalEquiv` — `Hom(μ_n, M) ≅ M`, `f ↦ f(ζ)`.

## Main results

* `Stacks.EtaleCohomology.rootsOfUnityHomRepresentation_apply_ofMul` — evaluation at `ζ`
  intertwines the action on `Hom(μ_n, M)` with `tateTwistNegOne`.
* `Stacks.EtaleCohomology.rootsOfUnityHomEvalEquiv_symm_apply_of_pow_eq` — the inverse of
  evaluation at `ζ`, at `ζ^b`.
-/

@[expose] public noncomputable section

universe u r w

namespace Stacks.EtaleCohomology

section Log

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)

/-- **`μ_n ≅ ℤ/n`, `ζ^a ↦ a`**, for a primitive `n`-th root of unity `ζ`. -/
def rootsOfUnityLog : Additive (rootsOfUnity n K) ≃+ ZMod n :=
  (MulEquiv.subgroupCongr (hζ.isUnit_unit (NeZero.ne n)).zpowers_eq.symm).toAdditive.trans
    (hζ.isUnit_unit (NeZero.ne n)).zmodEquivZPowers.symm

/-- `rootsOfUnityLog` sends a root of unity equal to `ζ ^ b` to `b`. -/
theorem rootsOfUnityLog_ofMul_of_pow_eq (b : ℕ) (z : rootsOfUnity n K)
    (hz : ((z : Kˣ) : K) = ζ ^ b) :
    rootsOfUnityLog hζ (Additive.ofMul z) = b := by
  have hu : (z : Kˣ) = (hζ.isUnit (NeZero.ne n)).unit ^ b := Units.ext (by simp [hz])
  rw [rootsOfUnityLog, AddEquiv.trans_apply, AddEquiv.symm_apply_eq,
    ← Int.cast_natCast, IsPrimitiveRoot.zmodEquivZPowers_apply_coe_int]
  exact congrArg Additive.ofMul (Subtype.ext (hu.trans (zpow_natCast _ _).symm))

/-- `rootsOfUnityLog` sends `ζ` itself to `1`. -/
theorem rootsOfUnityLog_toRootsOfUnity :
    rootsOfUnityLog hζ (Additive.ofMul hζ.toRootsOfUnity) = 1 := by
  rw [rootsOfUnityLog_ofMul_of_pow_eq hζ 1 _ (by simp), Nat.cast_one]

end Log

section Representation

variable (k : Type u) [Field k] (ksep : Type u) [Field ksep] [Algebra k ksep] (n : ℕ)
  (Λ : Type r) [Ring Λ] {M : Type w} [AddCommGroup M] [Module Λ M]

/-- `f ↦ τ(σ) ∘ f ∘ σ⁻¹` on `Hom(μ_n, M)`, for one `σ`. -/
def rootsOfUnityHomMap (τ : Representation Λ (ksep ≃ₐ[k] ksep) M) (σ : ksep ≃ₐ[k] ksep) :
    (Additive (rootsOfUnity n ksep) →+ M) →ₗ[Λ] (Additive (rootsOfUnity n ksep) →+ M) where
  toFun g := (τ σ).toAddMonoidHom.comp (g.comp (galoisRootsOfUnity k ksep n σ⁻¹).toAdditive)
  map_add' g g' := by ext z; simp
  map_smul' a g := by ext z; simp

/-- `rootsOfUnityHomMap τ σ g` sends `z` to `τ(σ)(g(σ⁻¹ z))`. -/
@[simp]
theorem rootsOfUnityHomMap_apply (τ : Representation Λ (ksep ≃ₐ[k] ksep) M)
    (σ : ksep ≃ₐ[k] ksep) (g : Additive (rootsOfUnity n ksep) →+ M)
    (z : Additive (rootsOfUnity n ksep)) :
    rootsOfUnityHomMap k ksep n Λ τ σ g z =
      τ σ (g (Additive.ofMul (galoisRootsOfUnity k ksep n σ⁻¹ z.toMul))) := rfl

/-- **The Galois action on `M(-1) = Hom(μ_n, M)`**: `σ` acts by `f ↦ τ(σ) ∘ f ∘ σ⁻¹`. -/
def rootsOfUnityHomRepresentation (τ : Representation Λ (ksep ≃ₐ[k] ksep) M) :
    Representation Λ (ksep ≃ₐ[k] ksep) (Additive (rootsOfUnity n ksep) →+ M) where
  toFun := rootsOfUnityHomMap k ksep n Λ τ
  map_one' := by
    refine LinearMap.ext fun g => AddMonoidHom.ext fun z => ?_
    rw [rootsOfUnityHomMap_apply, map_one, inv_one]
    have h1 : galoisRootsOfUnity k ksep n 1 (Additive.toMul z) = Additive.toMul z :=
      rootsOfUnity.coe_injective (by simp)
    rw [h1]
    rfl
  map_mul' σ σ' := by
    refine LinearMap.ext fun g => AddMonoidHom.ext fun z => ?_
    simp only [rootsOfUnityHomMap_apply, Module.End.mul_apply, map_mul]
    have h2 : galoisRootsOfUnity k ksep n (σ * σ')⁻¹ (Additive.toMul z) =
        galoisRootsOfUnity k ksep n σ'⁻¹ (galoisRootsOfUnity k ksep n σ⁻¹ (Additive.toMul z)) :=
      rootsOfUnity.coe_injective (by simp [mul_inv_rev, AlgEquiv.mul_apply])
    rw [h2]
    rfl

/-- `σ` sends `g ∈ Hom(μ_n, M)` to `z ↦ τ(σ)(g(σ⁻¹ z))`. -/
theorem rootsOfUnityHomRepresentation_apply (τ : Representation Λ (ksep ≃ₐ[k] ksep) M)
    (σ : ksep ≃ₐ[k] ksep) (g : Additive (rootsOfUnity n ksep) →+ M)
    (z : Additive (rootsOfUnity n ksep)) :
    rootsOfUnityHomRepresentation k ksep n Λ τ σ g z =
      τ σ (g (Additive.ofMul (galoisRootsOfUnity k ksep n σ⁻¹ z.toMul))) := rfl

variable [IsSepClosed ksep] [NeZero n] [NeZero (n : ksep)] [Algebra (ZMod n) Λ]

/-- **Evaluation at a root of unity is equivariant into the source's twist**: for every
`ζ ∈ μ_n`, `f ↦ f(ζ)` turns the action on `Hom(μ_n, M)` into `χ_cycl(σ)⁻¹ τ(σ)`. -/
theorem rootsOfUnityHomRepresentation_apply_ofMul (τ : Representation Λ (ksep ≃ₐ[k] ksep) M)
    (σ : ksep ≃ₐ[k] ksep) (g : Additive (rootsOfUnity n ksep) →+ M) (ζ : rootsOfUnity n ksep) :
    rootsOfUnityHomRepresentation k ksep n Λ τ σ g (Additive.ofMul ζ) =
      tateTwistNegOne k ksep n Λ τ σ (g (Additive.ofMul ζ)) := by
  rw [rootsOfUnityHomRepresentation_apply, tateTwistNegOne_apply, toMul_ofMul,
    galoisRootsOfUnity_eq_pow, ofMul_pow, map_nsmul, map_nsmul, map_inv, ← Nat.cast_smul_eq_nsmul Λ,
    ← map_natCast (algebraMap (ZMod n) Λ), ZMod.natCast_zmod_val]

end Representation

section Eval

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  (Λ : Type r) [Ring Λ] {M : Type w} [AddCommGroup M] [Module Λ M] (hM : ∀ m : M, n • m = 0)

/-- **`Hom(μ_n, M) ≅ M`, `f ↦ f(ζ)`**, for a primitive `ζ` and `n M = 0`. -/
def rootsOfUnityHomEvalEquiv : (Additive (rootsOfUnity n K) →+ M) ≃ₗ[Λ] M where
  toFun g := g (Additive.ofMul hζ.toRootsOfUnity)
  invFun m := (ZMod.lift n ⟨zmultiplesHom M m, by simp [hM m]⟩).comp
    (rootsOfUnityLog hζ).toAddMonoidHom
  left_inv g := by
    refine AddMonoidHom.ext fun z => ?_
    obtain ⟨c, hc⟩ := ZMod.intCast_surjective (rootsOfUnityLog hζ z)
    have hz : z = c • Additive.ofMul hζ.toRootsOfUnity := by
      apply (rootsOfUnityLog hζ).injective
      rw [map_zsmul, rootsOfUnityLog_toRootsOfUnity, ← hc, zsmul_eq_mul, mul_one]
    subst hz
    dsimp only
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, map_zsmul,
      rootsOfUnityLog_toRootsOfUnity, zsmul_eq_mul, mul_one, ZMod.lift_coe, map_zsmul]
    rfl
  right_inv m := by
    dsimp only
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, rootsOfUnityLog_toRootsOfUnity,
      ← Int.cast_one, ZMod.lift_coe]
    exact one_zsmul m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse of evaluation at `ζ`, at `ζ^b`, is `b` times. -/
theorem rootsOfUnityHomEvalEquiv_symm_apply_of_pow_eq (m : M) (b : ℕ) (z : rootsOfUnity n K)
    (hz : ((z : Kˣ) : K) = ζ ^ b) :
    (rootsOfUnityHomEvalEquiv hζ Λ hM).symm m (Additive.ofMul z) = b • m := by
  rw [show (rootsOfUnityHomEvalEquiv hζ Λ hM).symm m =
      (ZMod.lift n ⟨zmultiplesHom M m, by simp [hM m]⟩).comp (rootsOfUnityLog hζ).toAddMonoidHom
      from rfl, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    rootsOfUnityLog_ofMul_of_pow_eq hζ b z hz, ← Int.cast_natCast b, ZMod.lift_coe]
  exact natCast_zsmul m b

end Eval

end Stacks.EtaleCohomology

end
