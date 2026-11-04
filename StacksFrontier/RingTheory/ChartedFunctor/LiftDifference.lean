module

public import StacksFrontier.RingTheory.ChartedFunctor.Basic

/-!
# Differences of lifts along a square-zero extension

Let `π : Q ⟶ P` be a surjection of commutative `R`-algebras whose kernel `I` has square zero,
and let `σ : C ⟶ Q` be an algebra map. The `R`-linear maps `δ : C → Q` with values in `I` which
satisfy the Leibniz rule `δ(c c') = σ(c) δ(c') + σ(c') δ(c)` form a `Q`-module
`Stacks.ChartedFunctor.LiftDer π σ`, which depends only on the composite `σ ≫ π`. Adding such a
`δ` to `σ` is again an algebra map, and the difference of two algebra maps agreeing after `π` is
such a `δ`: the lifts of a fixed map `C ⟶ P` along `π` form a torsor under `LiftDer π σ`.

## Main definitions

* `Stacks.ChartedFunctor.LiftDer`: the module of derivations along `σ` valued in the kernel of `π`.
* `Stacks.ChartedFunctor.addLift`: the translate `σ + δ`.
* `Stacks.ChartedFunctor.liftSub`: the difference `τ - σ` of two lifts.

## Main results

* `Stacks.ChartedFunctor.LiftDer.eq_of_comp_eq`: the module depends only on `σ ≫ π`.
* `Stacks.ChartedFunctor.addLift_liftSub` and `Stacks.ChartedFunctor.liftSub_addLift`: the
  translation and the difference are mutually inverse.

## References

* [Stacks Project, Tag 00UO](https://stacks.math.columbia.edu/tag/00UO)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.ChartedFunctor

variable {R : Type u} [CommRing R] {κ : Cardinal.{u}}

variable {Q P : BoundedAlg R κ} (π : Q ⟶ P) {C : CommAlgCat.{u} R}

/-- **The derivations along a lift**, valued in the kernel of `π`: the `R`-linear maps
`δ : C → Q` with values in the kernel of `π` satisfying the Leibniz rule along `σ`. -/
def LiftDer (σ : C ⟶ Q.obj) : Submodule Q.obj (C →ₗ[R] Q.obj) where
  carrier := {δ | (∀ c, BoundedAlg.toAlgHom π (δ c) = 0) ∧
    ∀ c c', δ (c * c') = σ.hom c * δ c' + σ.hom c' * δ c}
  add_mem' {δ δ'} hδ hδ' := ⟨fun c => by simp [hδ.1 c, hδ'.1 c], fun c c' => by
    simp only [LinearMap.add_apply, hδ.2, hδ'.2]; ring⟩
  zero_mem' := ⟨fun c => by simp, fun c c' => by simp⟩
  smul_mem' q {δ} hδ := ⟨fun c => by simp [hδ.1 c], fun c c' => by
    simp only [LinearMap.smul_apply, smul_eq_mul, hδ.2]; ring⟩

variable {π}

/-- A derivation along a lift takes values in the kernel of `π`. -/
lemma LiftDer.map_eq_zero {σ : C ⟶ Q.obj} (δ : LiftDer π σ) (c : C) :
    BoundedAlg.toAlgHom π (δ.1 c) = 0 := δ.2.1 c

/-- The Leibniz rule `δ(c c') = σ(c) δ(c') + σ(c') δ(c)` for a derivation along `σ`. -/
lemma LiftDer.leibniz {σ : C ⟶ Q.obj} (δ : LiftDer π σ) (c c' : C) :
    δ.1 (c * c') = σ.hom c * δ.1 c' + σ.hom c' * δ.1 c := δ.2.2 c c'

/-- A derivation along a lift vanishes at `1`. -/
lemma LiftDer.map_one_eq_zero {σ : C ⟶ Q.obj} (δ : LiftDer π σ) : δ.1 1 = 0 := by
  have h := LiftDer.leibniz δ 1 1
  simp only [mul_one, map_one, one_mul] at h
  linear_combination -h

/-- **The module of derivations depends only on the reduction of the lift.** -/
lemma LiftDer.eq_of_comp_eq (hπ : IsSqZeroExt π) {σ₁ σ₂ : C ⟶ Q.obj}
    (h : σ₁ ≫ π.hom = σ₂ ≫ π.hom) : LiftDer π σ₁ = LiftDer π σ₂ := by
  have key : ∀ (μ₁ μ₂ : C ⟶ Q.obj), μ₁ ≫ π.hom = μ₂ ≫ π.hom →
      ∀ δ ∈ LiftDer π μ₁, δ ∈ LiftDer π μ₂ := by
    intro μ₁ μ₂ hμ δ hδ
    have hk : ∀ c, BoundedAlg.toAlgHom π (μ₂.hom c - μ₁.hom c) = 0 := fun c => by
      have := congrArg (fun g : C ⟶ P.obj => g.hom c) hμ
      simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at this
      simp [map_sub, this]
    refine ⟨hδ.1, fun c c' => ?_⟩
    rw [hδ.2]
    have e₁ := hπ.mul_eq_zero (hk c) (hδ.1 c')
    have e₂ := hπ.mul_eq_zero (hk c') (hδ.1 c)
    linear_combination -e₁ - e₂
  ext δ
  exact ⟨key _ _ h δ, key _ _ h.symm δ⟩

variable (hπ : IsSqZeroExt π)
include hπ

/-- **The translate of a lift by a derivation along it.** -/
def addLift (σ : C ⟶ Q.obj) (δ : LiftDer π σ) : C ⟶ Q.obj :=
  CommAlgCat.ofHom
    { toFun := fun c => σ.hom c + δ.1 c
      map_one' := by simp [LiftDer.map_one_eq_zero δ]
      map_mul' := fun c c' => by
        have := hπ.mul_eq_zero (LiftDer.map_eq_zero δ c) (LiftDer.map_eq_zero δ c')
        simp only [map_mul, LiftDer.leibniz δ]
        linear_combination -this
      map_zero' := by simp
      map_add' := fun c c' => by simp only [map_add]; ring
      commutes' := fun r => by
        simp only [AlgHom.commutes]
        have : δ.1 (algebraMap R C r) = 0 := by
          rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, LiftDer.map_one_eq_zero δ,
            smul_zero]
        rw [this, add_zero] }

/-- The translate `σ + δ` sends `c` to `σ(c) + δ(c)`. -/
lemma addLift_apply (σ : C ⟶ Q.obj) (δ : LiftDer π σ) (c : C) :
    (addLift hπ σ δ).hom c = σ.hom c + δ.1 c := rfl

/-- The translate of a lift has the same reduction. -/
lemma addLift_comp (σ : C ⟶ Q.obj) (δ : LiftDer π σ) :
    addLift hπ σ δ ≫ π.hom = σ ≫ π.hom := by
  ext c
  show BoundedAlg.toAlgHom π (σ.hom c + δ.1 c) = BoundedAlg.toAlgHom π (σ.hom c)
  rw [map_add, LiftDer.map_eq_zero δ, add_zero]

/-- **The difference of two lifts with the same reduction**, as a derivation along the first. -/
def liftSub (σ₁ σ₂ : C ⟶ Q.obj) (h : σ₁ ≫ π.hom = σ₂ ≫ π.hom) : LiftDer π σ₁ :=
  ⟨σ₂.hom.toLinearMap - σ₁.hom.toLinearMap, fun c => by
      have := congrArg (fun g : C ⟶ P.obj => g.hom c) h
      simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at this
      simp [this],
    fun c c' => by
      have hk : ∀ c, BoundedAlg.toAlgHom π (σ₂.hom c - σ₁.hom c) = 0 := fun c => by
        have := congrArg (fun g : C ⟶ P.obj => g.hom c) h
        simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at this
        simp [map_sub, this]
      have e := hπ.mul_eq_zero (hk c) (hk c')
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_mul]
      linear_combination e⟩

/-- The difference of two lifts `σ₁` and `σ₂` sends `c` to `σ₂(c) - σ₁(c)`. -/
lemma liftSub_apply (σ₁ σ₂ : C ⟶ Q.obj) (h : σ₁ ≫ π.hom = σ₂ ≫ π.hom) (c : C) :
    (liftSub hπ σ₁ σ₂ h).1 c = σ₂.hom c - σ₁.hom c := rfl

/-- Translating by the difference recovers the second lift. -/
lemma addLift_liftSub (σ₁ σ₂ : C ⟶ Q.obj) (h : σ₁ ≫ π.hom = σ₂ ≫ π.hom) :
    addLift hπ σ₁ (liftSub hπ σ₁ σ₂ h) = σ₂ := by
  ext c
  show σ₁.hom c + (σ₂.hom c - σ₁.hom c) = σ₂.hom c
  ring

/-- The difference from a translate is the translating derivation. -/
lemma liftSub_addLift (σ : C ⟶ Q.obj) (δ : LiftDer π σ) :
    liftSub hπ σ (addLift hπ σ δ) (addLift_comp hπ σ δ).symm = δ := by
  ext c
  show σ.hom c + δ.1 c - σ.hom c = δ.1 c
  ring

/-- Two lifts with the same reduction are equal exactly when their difference vanishes. -/
lemma eq_of_liftSub_eq_zero (σ₁ σ₂ : C ⟶ Q.obj) (h : σ₁ ≫ π.hom = σ₂ ≫ π.hom)
    (h0 : liftSub hπ σ₁ σ₂ h = 0) : σ₁ = σ₂ := by
  ext c
  have := congrArg (fun δ : LiftDer π σ₁ => δ.1 c) h0
  simp only [liftSub_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply] at this
  exact (sub_eq_zero.1 this).symm

end Stacks.ChartedFunctor

end
