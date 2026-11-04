module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricDerivedHomologyTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricDerivedGaloisInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafHomOp

/-!
# The derived clause of Tag 03VM: `RΓ_c(X_k̄, ℱ_ρ) = LH₀(π₁(X_k̄), M(-1))` in `D(Λ[[Ẑ]])`

Assembly of the homological derived clause of [Stacks, Tag 03VM]. This file is work in progress:
it currently contains the group-theoretic step, identifying `RH⁰(π₁(X_k̄), Hom(M, μ_n))` with the
Galois-equivariant cohomology of the sheaf attached to `Hom(M, μ_n)`.

## Main definitions

* `AlgebraicGeometry.geometricDualDerivedInvariantsIso`:
  `RH⁰(π₁(X_k̄), Hom(M, μ_n)) ≅ RΓ^{Gal}(X_k̄, ℱ_{Hom(M, μ_n)})`, naturally in `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
open Stacks.GroupHomology Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] [Algebra.IsSeparable k K]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (Λ : Type) [Ring Λ] [Finite Λ]

/-- **`RH⁰(π₁(X_k̄), Hom(M, μ_n)) ≅ RΓ^{Gal}(X_k̄, ℱ_{Hom(M, μ_n)})`**, naturally in `M`, in `D` of
discrete `Λᵐᵒᵖ`-modules with a continuous action of `Aut(k̄/k)`: the cohomological derived clause
of Tag 03VM (`AlgebraicGeometry.geometricGaloisDerivedInvariantsIso`) at the coefficient ring
`Λᵐᵒᵖ`, applied to `Hom(M, μ_n)` (`AlgebraicGeometry.cyclotomicDual`). -/
def geometricDualDerivedInvariantsIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    geometricDualDerivedInvariants B X f K y Λ ≅
      cyclotomicDual B X f K y (Nat.card Λ) Λ ⋙
        representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λᵐᵒᵖ ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        Stacks.EtaleCohomology.galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) K ⋙
        DerivedCategory.Plus.ι :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have hΛop : IsUnit ((Nat.card Λᵐᵒᵖ : ℕ) : k) := by
    rwa [Nat.card_congr MulOpposite.opEquiv.symm]
  Functor.isoWhiskerLeft (cyclotomicDual B X f K y (Nat.card Λ) Λ)
    (Functor.isoWhiskerRight
      (geometricGaloisDerivedInvariantsIso B X f K Λᵐᵒᵖ y hΛop hP) DerivedCategory.Plus.ι)

/-- **`Λ` is an algebra over `ℤ/#Λ`**: the characteristic of `Λ` divides `#Λ`, and the image of
`ℤ` is central. This is the `ℤ/n`-structure, `n = #Λ`, along which `ℋom(ℱ_M, μ_n)` is formed. -/
@[instance_reducible]
def zmodNatCardAlgebra : Algebra (ZMod (Nat.card Λ)) Λ :=
  letI : Fintype Λ := Fintype.ofFinite Λ
  have h : ringChar Λ ∣ Nat.card Λ := ringChar.dvd (by
    rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero Λ)
  (ZMod.castHom h Λ).toAlgebra' fun c x ↦ by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact (Nat.cast_commute _ x).eq

/-- **`RH⁰(π₁(X_k̄), Hom(M, μ_n)) ≅ RΓ^{Gal}(X_k̄, ℋom(ℱ_M, μ_n))`**, naturally in `M`: the
previous isomorphism followed by `ℱ_{Hom(M, μ_n)} ≅ ℋom(ℱ_M, μ_n)`
(`AlgebraicGeometry.representationSheafHomOpNatIso`), as sheaves of `Λᵐᵒᵖ`-modules. -/
def geometricDualDerivedInvariantsHomOpIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    letI := zmodNatCardAlgebra Λ
    geometricDualDerivedInvariants B X f K y Λ ≅
      etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ (Nat.card Λ)
          (cyclotomicContinuousModule B X f K y (Nat.card Λ)) ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        Stacks.EtaleCohomology.galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) K ⋙
        DerivedCategory.Plus.ι :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  letI := zmodNatCardAlgebra Λ
  geometricDualDerivedInvariantsIso B X f K y Λ hΛ hP ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representationSheafHomOpNatIso B X _ Λ (Nat.card Λ)
      (cyclotomicContinuousModule B X f K y (Nat.card Λ))).symm _

/-- **`LH₀(π₁(X_k̄), M(-1)) ≅ (RΓ^{Gal}(X_k̄, ℋom(ℱ_M, μ_n)))^∨`** in `D(Λ[[Aut(k̄/k)]])`,
naturally in `M`: the group side of the derived clause of Tag 03VM, in the form in which it meets
the derived Poincaré duality. -/
def geometricDerivedHomologyTwistGaloisIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    letI := zmodNatCardAlgebra Λ
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
    geometricTateTwist B X f K y Λ ⋙ geometricDerivedHomology B X f K y Λ ≅
      (etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ (Nat.card Λ)
          (cyclotomicContinuousModule B X f K y (Nat.card Λ)) ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        Stacks.EtaleCohomology.galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) K ⋙
        DerivedCategory.Plus.ι).rightOp ⋙
        derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K) ⋙
        (ModuleCat.restrictScalars.{u + 1}
          (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))).mapDerivedCategory :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  letI := zmodNatCardAlgebra Λ
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  geometricDerivedHomologyTwistIso B X f K y Λ hΛ ≪≫
    Functor.isoWhiskerRight
      (natIsoRightOp (geometricDualDerivedInvariantsHomOpIso B X f K y Λ hΛ hP).symm) _

section Sides

variable (j : CompactificationOf (Over.mk f))

/-- **The left-hand side `M ↦ RΓ_c(X_k̄, ℱ_ρ)` in `D(Λ[[Aut(k̄/k)]])`**: the Galois-equivariant
compactly supported cohomology `RΓ^{Gal}_c(X_k̄, ℱ_ρ)`
(`Stacks.EtaleCohomology.galoisDerivedCompactSupport`, Remark 03UI (2)) of the sheaf attached to
`ρ`, a complex of discrete `Λ[Aut(k̄/k)]`-modules, read as a complex of `Λ[[Aut(k̄/k)]]`-modules.
Forgetting the action it is the base's `galoisCompactSupportCohomology`, with
`galoisCompactSupportAction` as the action of `σ`
(`Stacks.EtaleCohomology.galoisCompactSupportForgetIso`,
`Stacks.EtaleCohomology.galoisForgetAction_app_comp_galoisCompactSupportForgetIso`). -/
def geometricGaloisCompactSupportDerived :
    letI := connectedSpace_of_isCurve B X f
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ (K ≃ₐ[k] K))) :=
  letI := connectedSpace_of_isCurve B X f
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ ⋙
    Stacks.DerivedIndexing.singlePlusFunctor _ 0 ⋙
    (Stacks.EtaleCohomology.etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus ⋙
    DerivedCategory.Plus.Q ⋙
    Stacks.EtaleCohomology.galoisDerivedGlobalSections Λ (Over.mk j.toBase) K ⋙
    DerivedCategory.Plus.ι ⋙
    (discreteToCompletedGroupAlgebra.{0, u, u + 1} Λ (K ≃ₐ[k] K)).mapDerivedCategory

/-- The left-hand side at `ρ` is `RΓ^{Gal}_c(X_k̄, ℱ_ρ)`, by definition. -/
theorem geometricGaloisCompactSupportDerived_obj
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    (geometricGaloisCompactSupportDerived B X f K y Λ j).obj M =
      (discreteToCompletedGroupAlgebra.{0, u, u + 1} Λ (K ≃ₐ[k] K)).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj (Stacks.EtaleCohomology.galoisDerivedCompactSupport Λ f j K
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj M)))) :=
  rfl

end Sides

/-- **`M ↦ (RΓ^{Gal}(X_k̄, ℋom(ℱ_M, μ_n)))^∨`** in `D(Λ[[Aut(k̄/k)]])`, `n = #Λ`: the target of
the derived Poincaré duality, and the right-hand side of
`AlgebraicGeometry.geometricDerivedHomologyTwistGaloisIso`. -/
def geometricGaloisDualCohomology :
    letI := connectedSpace_of_isCurve B X f
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (CompletedGroupAlgebra Λ (K ≃ₐ[k] K))) :=
  letI := connectedSpace_of_isCurve B X f
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  letI := zmodNatCardAlgebra Λ
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{u, u, u + 1}
    (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))
  (etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ (Nat.card Λ)
      (cyclotomicContinuousModule B X f K y (Nat.card Λ)) ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
    Stacks.EtaleCohomology.galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) K ⋙
    DerivedCategory.Plus.ι).rightOp ⋙
    derivedContragredient.{0, u, u + 1} Λᵐᵒᵖ (K ≃ₐ[k] K) ⋙
    (ModuleCat.restrictScalars.{u + 1}
      (completedGroupAlgebraOpOp Λ (Q := K ≃ₐ[k] K))).mapDerivedCategory

end AlgebraicGeometry

end
