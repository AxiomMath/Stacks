module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CyclotomicRepresentation
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.HomTwistDual
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelDerivedHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedHomologyDelta

/-!
# `LH₀(π₁(X_k̄, η̄), M(-1))` in `D(Λ[[Aut(k̄/k)]])`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k` separable over `k` (so `k` is perfect, e.g. finite), `η̄` a geometric point of `X_k̄`, `Λ` a
finite ring with `n = #Λ` invertible in `k`, and `M` a finite `Λ`-module with a continuous action
of `π₁(X, η̄)`. This file assembles the right-hand side of the derived clause of
[Stacks, Tag 03VM]:

`LH₀(π₁(X_k̄, η̄), M(-1)) ∈ D(Λ[[Aut(k̄/k)]])`,

where

* `M(-1) = Hom(μ_n(k̄), M)` is the Tate twist (`AlgebraicGeometry.geometricTateTwist`), `π₁(X, η̄)`
  acting by conjugation, through `Aut(k̄/k)` on `μ_n(k̄)`; on a module with trivial geometric
  action `σ` acts as `χ_cycl(σ)⁻¹ σ`, which is the twist `(-1)` of Section 03VJ;
* `LH₀(G, -)` is `Stacks.ContinuousCohomology.kernelDerivedHomology` for the continuous surjection
  `π₁(X, η̄) ⟶ Aut(k̄/k)` with kernel the image of `π₁(X_k̄, η̄)`
  (`AlgebraicGeometry.geometricGaloisProjection`): the dual of the derived invariants of the dual,
  read in `D(Λ[[Aut(k̄/k)]])`. For `k` finite, `Aut(k̄/k) ≅ Ẑ` by the Frobenius, so this is the
  source's `D(Λ[[Ẑ]])`.

The dual of `M(-1)` is `Hom(M, μ_n(k̄))` (`AlgebraicGeometry.cyclotomicDual`) without any choice
(`AlgebraicGeometry.geometricTateTwistDualNatIso`), so
`LH₀(G, M(-1)) = (RH⁰(G, Hom(M, μ_n)))^∨` (`AlgebraicGeometry.geometricDerivedHomologyTwistIso`);
this is the form in which it meets the étale side.

## Main definitions

* `AlgebraicGeometry.geometricTateTwist`: `M ↦ M(-1)`.
* `AlgebraicGeometry.geometricDerivedHomology`: `M ↦ LH₀(π₁(X_k̄, η̄), M)`.
* `AlgebraicGeometry.geometricDerivedHomologyTwistIso`:
  `LH₀(G, M(-1)) ≅ (RH⁰(G, Hom(M, μ_n)))^∨`, naturally in `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
open Stacks.GroupHomology
open Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (Λ : Type) [Ring Λ] [Finite Λ]

/-- `#Λ ≠ 0`. -/
instance neZero_natCard_of_ring : NeZero (Nat.card Λ) :=
  ⟨Nat.card_pos.ne'⟩

/-- **The Tate twist `M ↦ M(-1) = Hom(μ_n(k̄), M)`**, `n = #Λ`, of finite `Λ`-modules with a
continuous action of `π₁(X, η̄)`. -/
def geometricTateTwist :
    letI := connectedSpace_of_isCurve B X f
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) ⥤
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :=
  letI := connectedSpace_of_isCurve B X f
  homTwistFunctor.{0, u + 1, u + 1, u + 1} Λ
    (cyclotomicIntContinuousModule B X f kbar y (Nat.card Λ))

/-- `μ_n(k̄)` is cyclic. -/
instance isAddCyclic_cyclotomicIntContinuousModule (n : ℕ) [NeZero n] :
    IsAddCyclic (cyclotomicIntContinuousModule B X f kbar y n).obj.obj.V :=
  isAddCyclic_of_surjective
    (AddEquiv.ulift.{u, u + 1} (α := Additive (_root_.rootsOfUnity n kbar))).symm.toAddMonoidHom
    (AddEquiv.ulift.{u, u + 1} (α := Additive (_root_.rootsOfUnity n kbar))).symm.surjective

omit [Smooth f] in
/-- `#μ_n(k̄) = n` for `n` invertible in `k̄`. -/
theorem natCard_cyclotomicIntContinuousModule (n : ℕ) [NeZero n] (hn : IsUnit (n : kbar)) :
    Nat.card (cyclotomicIntContinuousModule B X f kbar y n).obj.obj.V = n := by
  obtain ⟨ζ, hζ⟩ := Stacks.EtaleCohomology.exists_isPrimitiveRoot_of_isUnit hn
  change Nat.card (ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar))) = n
  rw [Nat.card_ulift]
  exact hζ.card_rootsOfUnity

/-- A `Λ`-module is killed by `#Λ`. -/
theorem natCard_nsmul_eq_zero {V : Type*} [AddCommGroup V] [Module Λ V] (m : V) :
    Nat.card Λ • m = 0 := by
  let : Fintype Λ := Fintype.ofFinite Λ
  rw [Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul Λ, Nat.cast_card_eq_zero, zero_smul]

/-- **`M(-1)^∨ ≅ Hom(M, μ_n)`**, naturally in `M`, for `n = #Λ` invertible in `k`: the composition
pairing `Hom(μ_n, M) × Hom(M, μ_n) → End(μ_n) = ℤ/n ⊂ ℚ/ℤ`
(`Stacks.GroupCohomology.homTwistDualNatIso`). -/
def geometricTateTwistDualNatIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k)) :
    letI := connectedSpace_of_isCurve B X f
    (geometricTateTwist B X f kbar y Λ).op ⋙
        finiteTypeContinuousModuleDual.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) ≅
      cyclotomicDual B X f kbar y (Nat.card Λ) Λ :=
  letI := connectedSpace_of_isCurve B X f
  homTwistDualNatIso.{0, u + 1, u + 1, u + 1} Λ
    (cyclotomicIntContinuousModule B X f kbar y (Nat.card Λ))
    (natCard_cyclotomicIntContinuousModule B X f kbar y (Nat.card Λ)
      (by rw [← map_natCast (algebraMap k kbar)]; exact hΛ.map _))
    (fun M m ↦ natCard_nsmul_eq_zero Λ m)

/-- **`M ↦ LH₀(π₁(X_k̄, η̄), M)`** in `D(Λ[[Aut(k̄/k)]])`:
`Stacks.ContinuousCohomology.kernelDerivedHomology`
for the projection `π₁(X, η̄) ⟶ Aut(k̄/k)`, whose kernel is the image of `π₁(X_k̄, η̄)`. -/
def geometricDerivedHomology :
    letI := connectedSpace_of_isCurve B X f
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ (kbar ≃ₐ[k] kbar))) :=
  letI := connectedSpace_of_isCurve B X f
  haveI := compactSpace_etaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
  haveI : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k kbar := { to_isSeparable := inferInstance, to_normal := inferInstance }
  kernelDerivedHomology Λ (geometricGaloisProjection B X f kbar y)
    (surjective_geometricGaloisProjection B X f kbar y)

/-- **`M ↦ RH⁰(π₁(X_k̄, η̄), Hom(M, μ_n))`**, contravariant, in `D` of discrete
`Λᵐᵒᵖ[Aut(k̄/k)]`-modules: the derived invariants of the image of `π₁(X_k̄, η̄)` with their
residual action of `Aut(k̄/k)`. This is the object compared with `RΓ(X_k̄, ℋom(ℱ_ρ, μ_n))` on the
étale side. -/
def geometricDualDerivedInvariants :
    letI := connectedSpace_of_isCurve B X f
    (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))ᵒᵖ ⥤
      DerivedCategory (Stacks.Injectives.ContinuousModule.{0, u, u + 1} Λᵐᵒᵖ (kbar ≃ₐ[k] kbar)) :=
  letI := connectedSpace_of_isCurve B X f
  haveI := compactSpace_etaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
  haveI : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k kbar := { to_isSeparable := inferInstance, to_normal := inferInstance }
  cyclotomicDual B X f kbar y (Nat.card Λ) Λ ⋙
    finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λᵐᵒᵖ _ ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedKernelInvariants.{0, u + 1, u, u + 1} Λᵐᵒᵖ (geometricGaloisProjection B X f kbar y)
      (surjective_geometricGaloisProjection B X f kbar y) ⋙ DerivedCategory.Plus.ι

/-- **`LH₀(π₁(X_k̄, η̄), M(-1)) ≅ (RH⁰(π₁(X_k̄, η̄), Hom(M, μ_n)))^∨`** in `D(Λ[[Aut(k̄/k)]])`,
naturally in `M`, for `n = #Λ` invertible in `k`: the definition of `LH₀` as the dual of the
derived invariants of the dual, and `M(-1)^∨ = Hom(M, μ_n)`
(`AlgebraicGeometry.geometricTateTwistDualNatIso`). -/
def geometricDerivedHomologyTwistIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
    haveI : IsGalois k kbar := { to_isSeparable := inferInstance, to_normal := inferInstance }
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := kbar ≃ₐ[k] kbar))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := kbar ≃ₐ[k] kbar))
    geometricTateTwist B X f kbar y Λ ⋙ geometricDerivedHomology B X f kbar y Λ ≅
      (geometricDualDerivedInvariants B X f kbar y Λ).rightOp ⋙
        derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (kbar ≃ₐ[k] kbar) ⋙
        (ModuleCat.restrictScalars.{u + 1}
          (completedGroupAlgebraOpOp Λ (Q := kbar ≃ₐ[k] kbar))).mapDerivedCategory :=
  letI := connectedSpace_of_isCurve B X f
  haveI := compactSpace_etaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
  haveI : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k kbar := { to_isSeparable := inferInstance, to_normal := inferInstance }
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := kbar ≃ₐ[k] kbar))
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := kbar ≃ₐ[k] kbar))
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (natIsoRightOp (Functor.isoWhiskerRight (geometricTateTwistDualNatIso B X f kbar y Λ hΛ)
        (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λᵐᵒᵖ _ ⋙
          DerivedCategory.Plus.singleFunctor _ 0 ⋙
          derivedKernelInvariants.{0, u + 1, u, u + 1} Λᵐᵒᵖ (geometricGaloisProjection B X f kbar y)
            (surjective_geometricGaloisProjection B X f kbar y) ⋙ DerivedCategory.Plus.ι)).symm)
      _

end AlgebraicGeometry

end
