module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.HomTwistDual
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RootsOfUnityHomTwist
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricGaloisProjection

/-!
# The cyclotomic representation `μ_n(k^{sep})` of `π₁(X, x̄)` and the dual `Hom(M, μ_n)`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k` which is separable over `k` (for instance `k` finite), `η̄` a geometric point of `X_k̄` and
`x̄` its image in `X`. The group `π₁(X, x̄)` acts on the `n`-th roots of unity `μ_n(k̄)` through
the projection `π₁(X, x̄) ⟶ π₁(Spec k) ≅ Gal(k^{sep}/k) ≅ Aut(k̄/k)` of the fundamental exact
sequence (`AlgebraicGeometry.geometricGaloisProjection`). This is the representation `ρ_μ` with
`ℱ_{ρ_μ} = μ_n` of the Trace Formula chapter, and for a finite `Λ`-module `M` with continuous
action `ρ` the module `Hom(M, μ_n(k̄))` with `γ` acting by `φ ↦ γ ∘ φ ∘ γ⁻¹` is its dual `M^∨(1)`
([Stacks, Tag 03VM]). Since `μ_n(k̄)` has exactly the `n`-th roots of unity of `k^{sep}`, nothing
depends on the choice of `k̄` over `k^{sep}`.

The action is continuous: `σ ∈ Aut(k̄/k)` fixes `ζ` as soon as it fixes the finite extension
`k(ζ)`, and the fixing group of a finite extension is open for the Krull topology.

## Main definitions

* `Stacks.EtaleCohomology.rootsOfUnityGaloisRepresentation` — `Aut(K/k)` acting on `μ_n(K)`, over
  `ℤ`; `Stacks.EtaleCohomology.rootsOfUnityZModRepresentation` — the same over `ℤ/n`.
* `Stacks.EtaleCohomology.rootsOfUnityFiniteTypeContinuousModule` — `μ_n(K)` as a finite
  `ℤ/n`-module with a continuous action of `G`, for a continuous homomorphism
  `G →ₜ* Aut(K/k)`.
* `AlgebraicGeometry.cyclotomicContinuousModule` — **`ρ_μ`**: `μ_n(k̄)` as a finite `ℤ/n`-module
  with continuous action of `π₁(X, x̄)`.
* `AlgebraicGeometry.cyclotomicIntContinuousModule` — `μ_n(k̄)` as a discrete
  `ℤ`-`π₁(X, x̄)`-module, the underlying module of `ρ_μ`.
* `AlgebraicGeometry.cyclotomicDual` — **`M ↦ Hom(M, μ_n(k̄))`**, a functor from finite
  `Λ`-modules with continuous `π₁(X, x̄)`-action to finite `Λᵐᵒᵖ`-modules with continuous action.

## Main results

* `Stacks.EtaleCohomology.isOpen_setOf_rootsOfUnityGaloisRepresentation_eq` — stabilizers are
  open for the Krull topology.
* `AlgebraicGeometry.cyclotomicContinuousModule_ρ_apply` — `γ` acts on `ζ` by its image in
  `Aut(k̄/k)`.
* `AlgebraicGeometry.cyclotomicContinuousModule_ρ_eq_one_of_mem_range` — the image of
  `π₁(X_k̄, η̄)` acts trivially.
* `Stacks.EtaleCohomology.rootsOfUnityHomRepresentation_rootsOfUnityZModRepresentation` — the
  Galois action on `Hom(μ_n, μ_n) = ℤ/n` is trivial.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.DiscreteModuleTopology IntermediateField

universe u v w

namespace Stacks.EtaleCohomology

section Galois

variable (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K] (n : ℕ)

variable {K n} in
/-- Two elements of `μ_n(K)`, written additively, agree when they agree in `K`. -/
lemma additive_rootsOfUnity_ext {a b : Additive (rootsOfUnity n K)}
    (h : ((a.toMul : Kˣ) : K) = ((b.toMul : Kˣ) : K)) : a = b :=
  Additive.toMul.injective (rootsOfUnity.coe_injective h)

/-- **`Aut(K/k)` acting on the `n`-th roots of unity of `K`**, as a representation over `ℤ` on
the additive group `μ_n(K)`. -/
def rootsOfUnityGaloisRepresentation :
    Representation ℤ (K ≃ₐ[k] K) (Additive (rootsOfUnity n K)) where
  toFun σ := (MonoidHom.toAdditive (galoisRootsOfUnity k K n σ)).toIntLinearMap
  map_one' := LinearMap.ext fun z ↦ additive_rootsOfUnity_ext (by
    change ((galoisRootsOfUnity k K n 1 z.toMul : Kˣ) : K) = _
    rw [galoisRootsOfUnity_coe, AlgEquiv.one_apply]
    rfl)
  map_mul' σ τ := LinearMap.ext fun z ↦ additive_rootsOfUnity_ext (by
    change ((galoisRootsOfUnity k K n (σ * τ) z.toMul : Kˣ) : K) =
      ((galoisRootsOfUnity k K n σ (galoisRootsOfUnity k K n τ z.toMul) : Kˣ) : K)
    rw [galoisRootsOfUnity_coe, galoisRootsOfUnity_coe, galoisRootsOfUnity_coe,
      AlgEquiv.mul_apply])

/-- `σ ∈ Aut(K/k)` acts on `μ_n(K)` by `galoisRootsOfUnity k K n σ`. -/
lemma rootsOfUnityGaloisRepresentation_apply (σ : K ≃ₐ[k] K) (z : Additive (rootsOfUnity n K)) :
    rootsOfUnityGaloisRepresentation k K n σ z =
      Additive.ofMul (galoisRootsOfUnity k K n σ z.toMul) :=
  rfl

/-- `σ` fixes `ζ ∈ μ_n(K)` exactly when it fixes `ζ` as an element of `K`. -/
lemma rootsOfUnityGaloisRepresentation_eq_iff (σ : K ≃ₐ[k] K) (z : Additive (rootsOfUnity n K)) :
    rootsOfUnityGaloisRepresentation k K n σ z = z ↔
      σ ((z.toMul : Kˣ) : K) = ((z.toMul : Kˣ) : K) := by
  refine ⟨fun h ↦ ?_, fun h ↦ additive_rootsOfUnity_ext ?_⟩
  · simpa [rootsOfUnityGaloisRepresentation_apply] using
      congrArg (fun w : Additive (rootsOfUnity n K) ↦ ((w.toMul : Kˣ) : K)) h
  · rwa [rootsOfUnityGaloisRepresentation_apply, toMul_ofMul, galoisRootsOfUnity_coe]

variable [NeZero n]

/-- **The stabilizers of the action on `μ_n(K)` are open** for the Krull topology: the stabilizer
of `ζ` is the fixing group of the finite extension `k(ζ)`, `ζ` being a root of `X^n - 1`. -/
theorem isOpen_setOf_rootsOfUnityGaloisRepresentation_eq (z : Additive (rootsOfUnity n K)) :
    IsOpen {σ : K ≃ₐ[k] K | rootsOfUnityGaloisRepresentation k K n σ z = z} := by
  set α : K := ((z.toMul : Kˣ) : K)
  have hpow : α ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n _).mp z.toMul.2, Units.val_one]
  have hα : IsIntegral k α := IsIntegral.of_pow (NeZero.pos n) (by rw [hpow]; exact isIntegral_one)
  have : FiniteDimensional k k⟮α⟯ := IntermediateField.adjoin.finiteDimensional hα
  have hset : {σ : K ≃ₐ[k] K | rootsOfUnityGaloisRepresentation k K n σ z = z} =
      (MulAction.stabilizer (K ≃ₐ[k] K) α : Set (K ≃ₐ[k] K)) := by
    ext σ
    rw [Set.mem_setOf_eq, rootsOfUnityGaloisRepresentation_eq_iff, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  rw [hset]
  refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_) k⟮α⟯.fixingSubgroup_isOpen
  rw [MulAction.mem_stabilizer_iff]
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ α
    (IntermediateField.mem_adjoin_simple_self k α)

/-- `μ_n(K)` is killed by `n`, so it is a `ℤ/n`-module. -/
instance rootsOfUnityZModModule : Module (ZMod n) (Additive (rootsOfUnity n K)) :=
  AddCommGroup.zmodModule fun z ↦ congrArg Additive.ofMul <|
    Subtype.ext ((mem_rootsOfUnity n _).mp z.toMul.2)

/-- **`Aut(K/k)` acting on the `n`-th roots of unity of `K`**, as a representation over `ℤ/n`. -/
def rootsOfUnityZModRepresentation :
    Representation (ZMod n) (K ≃ₐ[k] K) (Additive (rootsOfUnity n K)) where
  toFun σ := (MonoidHom.toAdditive (galoisRootsOfUnity k K n σ)).toZModLinearMap n
  map_one' := LinearMap.ext fun z ↦ additive_rootsOfUnity_ext (by
    change ((galoisRootsOfUnity k K n 1 z.toMul : Kˣ) : K) = _
    rw [galoisRootsOfUnity_coe, AlgEquiv.one_apply]
    rfl)
  map_mul' σ τ := LinearMap.ext fun z ↦ additive_rootsOfUnity_ext (by
    change ((galoisRootsOfUnity k K n (σ * τ) z.toMul : Kˣ) : K) =
      ((galoisRootsOfUnity k K n σ (galoisRootsOfUnity k K n τ z.toMul) : Kˣ) : K)
    rw [galoisRootsOfUnity_coe, galoisRootsOfUnity_coe, galoisRootsOfUnity_coe,
      AlgEquiv.mul_apply])

omit [NeZero n] in
/-- `σ ∈ Aut(K/k)` acts on `μ_n(K)`, over `ℤ/n`, by `galoisRootsOfUnity k K n σ`. -/
lemma rootsOfUnityZModRepresentation_apply (σ : K ≃ₐ[k] K) (z : Additive (rootsOfUnity n K)) :
    rootsOfUnityZModRepresentation k K n σ z =
      Additive.ofMul (galoisRootsOfUnity k K n σ z.toMul) :=
  rfl

/-- **The Galois action on `Hom(μ_n, μ_n) = ℤ/n` is trivial**: `μ_n(K)` is cyclic, so every
endomorphism is multiplication by an integer and commutes with the action. -/
theorem rootsOfUnityHomRepresentation_rootsOfUnityZModRepresentation (σ : K ≃ₐ[k] K)
    (φ : Additive (rootsOfUnity n K) →+ Additive (rootsOfUnity n K)) :
    rootsOfUnityHomRepresentation k K n (ZMod n) (rootsOfUnityZModRepresentation k K n) σ φ =
      φ := by
  obtain ⟨c, hc⟩ := AddMonoidHom.map_addCyclic φ
  refine AddMonoidHom.ext fun z ↦ ?_
  rw [rootsOfUnityHomRepresentation_apply, hc, map_zsmul, hc]
  refine congrArg (c • ·) ?_
  rw [rootsOfUnityZModRepresentation_apply]
  refine additive_rootsOfUnity_ext ?_
  show ((galoisRootsOfUnity k K n σ (galoisRootsOfUnity k K n σ⁻¹ z.toMul) : Kˣ) : K) = _
  rw [galoisRootsOfUnity_coe, galoisRootsOfUnity_coe, ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

end Galois

section ContinuousModule

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] (n : ℕ) [NeZero n]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →ₜ* (K ≃ₐ[k] K))

/-- The action of `Aut(K/k)` on `μ_n(K)` over `ℤ/n`, moved to the universe lift
`ULift.{w} μ_n(K)` and pulled back along `π`. -/
def rootsOfUnityULiftRepresentation :
    Representation (ZMod n) G (ULift.{w} (Additive (rootsOfUnity n K))) where
  toFun g := (ULift.moduleEquiv.symm.toLinearMap.comp
    ((rootsOfUnityZModRepresentation k K n (π g)).comp ULift.moduleEquiv.toLinearMap))
  map_one' := LinearMap.ext fun z ↦ by
    change ULift.up (rootsOfUnityZModRepresentation k K n (π 1) z.down) = z
    rw [map_one, map_one]
    rfl
  map_mul' g h := LinearMap.ext fun z ↦ by
    change ULift.up (rootsOfUnityZModRepresentation k K n (π (g * h)) z.down) =
      ULift.up (rootsOfUnityZModRepresentation k K n (π g)
        (rootsOfUnityZModRepresentation k K n (π h) z.down))
    rw [map_mul, map_mul]
    rfl

omit [NeZero n] [IsTopologicalGroup G] in
/-- `g ∈ G` acts on `ULift.{w} μ_n(K)` by `galoisRootsOfUnity k K n (π g)`. -/
lemma rootsOfUnityULiftRepresentation_apply (g : G) (z : ULift.{w} (Additive (rootsOfUnity n K))) :
    rootsOfUnityULiftRepresentation.{u, v, w} n π g z =
      ULift.up (Additive.ofMul (galoisRootsOfUnity k K n (π g) z.down.toMul)) :=
  rfl

/-- **`μ_n(K)` as a finite `ℤ/n`-module with a continuous action of `G`**, through a continuous
homomorphism `π : G →ₜ* Aut(K/k)`; the underlying module is the universe lift
`ULift.{w} μ_n(K)`, so that it lives in the module universe of the representations of `G`. -/
def rootsOfUnityFiniteTypeContinuousModule :
    Stacks.GroupCohomology.FiniteTypeContinuousModule.{0, v, max u w} (ZMod n) G :=
  ⟨Stacks.GroupCohomology.ofRepresentation (rootsOfUnityULiftRepresentation.{u, v, w} n π)
      ((Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff _).mpr fun z ↦ by
        have h := (isOpen_setOf_rootsOfUnityGaloisRepresentation_eq k K n z.down).preimage
          (map_continuous π)
        convert h using 1
        ext g
        change ULift.up (Additive.ofMul (galoisRootsOfUnity k K n (π g) z.down.toMul)) = z ↔
          Additive.ofMul (galoisRootsOfUnity k K n (π g) z.down.toMul) = z.down
        exact ⟨fun e ↦ congrArg ULift.down e, fun e ↦ ULift.ext e⟩), by
    change Module.Finite (ZMod n) (ULift.{w} (Additive (rootsOfUnity n K)))
    exact Module.Finite.of_finite⟩

/-- The underlying `ℤ/n`-module of `rootsOfUnityFiniteTypeContinuousModule n π` is
`ULift.{w} μ_n(K)`. -/
lemma rootsOfUnityFiniteTypeContinuousModule_V :
    (rootsOfUnityFiniteTypeContinuousModule.{u, v, w} n π).obj.obj.obj.V =
      ModuleCat.of (ZMod n) (ULift.{w} (Additive (rootsOfUnity n K))) :=
  rfl

/-- `g ∈ G` acts on `rootsOfUnityFiniteTypeContinuousModule n π` by
`galoisRootsOfUnity k K n (π g)`. -/
lemma rootsOfUnityFiniteTypeContinuousModule_ρ_apply (g : G)
    (z : ULift.{w} (Additive (rootsOfUnity n K))) :
    (((rootsOfUnityFiniteTypeContinuousModule.{u, v, w} n π).obj.obj.obj.ρ g).asHom.hom z :
        ULift.{w} (Additive (rootsOfUnity n K))) =
      ULift.up (Additive.ofMul (galoisRootsOfUnity k K n (π g) z.down.toMul)) :=
  rfl

end ContinuousModule

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.Frobenius Stacks.EtaleCohomology Stacks.GroupCohomology

section Curve

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]

/-- **`ρ_μ`: the `n`-th roots of unity `μ_n(k̄)` as a finite `ℤ/n`-module with a continuous action
of `π₁(X, x̄)`**, acting through `π₁(X, x̄) ⟶ π₁(Spec k) ≅ Gal(k^{sep}/k) ≅ Aut(k̄/k)`
(`AlgebraicGeometry.geometricGaloisProjection`). Its underlying module is `ULift μ_n(k̄)`, in the
module universe of the representations of Tag 0DV5. -/
def cyclotomicContinuousModule :
    letI := connectedSpace_of_isCurve B X f
    FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :=
  letI := connectedSpace_of_isCurve B X f
  rootsOfUnityFiniteTypeContinuousModule.{u, u + 1, u + 1} n
    (geometricGaloisProjection B X f kbar y)

/-- `γ ∈ π₁(X, x̄)` acts on `ζ ∈ μ_n(k̄)` by its image in `Aut(k̄/k)`. -/
lemma cyclotomicContinuousModule_ρ_apply
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (z : ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar))) :
    (((cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.ρ γ).asHom.hom z :
        ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar))) =
      ULift.up (Additive.ofMul
        (galoisRootsOfUnity k kbar n (geometricGaloisProjection B X f kbar y γ) z.down.toMul)) :=
  rfl

/-- **The image of `π₁(X_k̄, η̄)` acts trivially on `μ_n(k̄)`**: it is the kernel of
`π₁(X, x̄) ⟶ Aut(k̄/k)` (`AlgebraicGeometry.ker_geometricGaloisProjection`). -/
lemma cyclotomicContinuousModule_ρ_eq_one_of_mem_range
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (hγ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      γ ∈ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range) :
    (cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.ρ γ = 1 := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have h1 : geometricGaloisProjection B X f kbar y γ = 1 :=
    MonoidHom.mem_ker.mp ((ker_geometricGaloisProjection B X f kbar y).symm ▸ hγ)
  refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_))
  show ULift.up (Additive.ofMul
    (galoisRootsOfUnity k kbar n (geometricGaloisProjection B X f kbar y γ) z.down.toMul)) = z
  rw [h1]
  refine ULift.ext (additive_rootsOfUnity_ext ?_)
  show ((galoisRootsOfUnity k kbar n 1 z.down.toMul : kbarˣ) : kbar) = _
  rw [galoisRootsOfUnity_coe, AlgEquiv.one_apply]

/-- **`μ_n(k̄)` as a discrete `ℤ`-module with the action of `π₁(X, x̄)` through `Aut(k̄/k)`**: the
underlying `π₁(X, x̄)`-module of `ρ_μ` (`AlgebraicGeometry.cyclotomicContinuousModule`), obtained
by forgetting its `ℤ/n`-module structure. It is the coefficient module of
`AlgebraicGeometry.cyclotomicDual`. -/
def cyclotomicIntContinuousModule :
    letI := connectedSpace_of_isCurve B X f
    Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} ℤ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :=
  letI := connectedSpace_of_isCurve B X f
  (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) _).obj
    (cyclotomicContinuousModule B X f kbar y n).obj

/-- The underlying module `μ_n(k̄)` of `AlgebraicGeometry.cyclotomicIntContinuousModule` is
finite. -/
instance finite_cyclotomicIntContinuousModule :
    Finite (cyclotomicIntContinuousModule B X f kbar y n).obj.obj.V :=
  inferInstanceAs (Finite (ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar))))

/-- `γ ∈ π₁(X, x̄)` acts on `ζ ∈ μ_n(k̄)`, in `AlgebraicGeometry.cyclotomicIntContinuousModule`, by
its image in `Aut(k̄/k)`. -/
lemma cyclotomicIntContinuousModule_ρ_apply
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (z : ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar))) :
    (((cyclotomicIntContinuousModule B X f kbar y n).obj.obj.ρ γ).asHom.hom z :
        ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar))) =
      ULift.up (Additive.ofMul
        (galoisRootsOfUnity k kbar n (geometricGaloisProjection B X f kbar y γ) z.down.toMul)) :=
  rfl

/-- **`M ↦ Hom(M, μ_n(k̄))`**, for finite `Λ`-modules `M` with a continuous action `ρ` of
`π₁(X, x̄)`: the additive maps `M → μ_n(k̄)`, with `γ` acting by `(γ · φ)(m) = γ · φ(ρ(γ)⁻¹ m)`
(`γ` acting on `μ_n` through `Aut(k̄/k)`) and `op a ∈ Λᵐᵒᵖ` by `(op a · φ)(m) = φ(a m)`, as a
finite `Λᵐᵒᵖ`-module with a continuous action, contravariantly in `M`. For `n = #Λ` this is the
dual `M^∨(1)` of the Trace Formula chapter. -/
def cyclotomicDual (Λ : Type) [Ring Λ] [Finite Λ] :
    letI := connectedSpace_of_isCurve B X f
    (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))ᵒᵖ ⥤
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λᵐᵒᵖ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :=
  letI := connectedSpace_of_isCurve B X f
  homDualFunctor.{0, u + 1, u + 1, u + 1} Λ (cyclotomicIntContinuousModule B X f kbar y n)

end Curve

end AlgebraicGeometry

end
