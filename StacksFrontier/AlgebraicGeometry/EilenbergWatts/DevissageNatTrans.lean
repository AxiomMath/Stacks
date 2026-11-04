module

public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Devissage
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Natural transformations out of modules are determined at the unit

Declarations supplementing `StacksFrontier.AlgebraicGeometry.EilenbergWatts.Devissage`
(`natTrans_ext_of_app_unit`, `isIso_app_of_isIso_app_unit`), kept in their own module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace Stacks.EilenbergWatts

variable {R : Type u} [CommRing R] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
  [F.Additive] [F.Linear R]

section Devissage

variable {D : Type*} [Category D]

/-- Two natural transformations out of a colimit-preserving functor on `R`-modules agree as soon
as they agree at `R`: every module is a quotient of a direct sum of copies of `R`. -/
theorem natTrans_ext_of_app_unit {G₁ G₂ : ModuleCat.{u} R ⥤ D}
    [PreservesColimitsOfSize.{u, u} G₁] {α β : G₁ ⟶ G₂}
    (h : α.app (ModuleCat.of R R) = β.app (ModuleCat.of R R)) : α = β := by
  ext M
  have hc := isColimitOfPreserves G₁
    (colimit.isColimit (Discrete.functor fun _ : M => ModuleCat.of R R))
  have hsum : α.app (∐ fun _ : M => ModuleCat.of R R) =
      β.app (∐ fun _ : M => ModuleCat.of R R) := by
    refine hc.hom_ext fun j => ?_
    obtain ⟨m⟩ := j
    exact (α.naturality _).trans ((congrArg (· ≫ _) h).trans (β.naturality _).symm)
  have := PreservesColimitsOfSize.preservesFiniteColimits G₁
  rw [← cancel_epi (G₁.map (freeCover M)), α.naturality, β.naturality, hsum]

/-- **Dévissage for a natural transformation between colimit-preserving functors on modules.**
A natural transformation between two colimit-preserving functors out of `R`-modules which is
invertible at `R` is invertible at every module: first at direct sums of copies of `R`, then at
their cokernels. -/
theorem isIso_app_of_isIso_app_unit {G₁ G₂ : ModuleCat.{u} R ⥤ D}
    [PreservesColimitsOfSize.{u, u} G₁] [PreservesColimitsOfSize.{u, u} G₂] (α : G₁ ⟶ G₂)
    [IsIso (α.app (ModuleCat.of R R))]
    (M : ModuleCat.{u} R) : IsIso (α.app M) := by
  have hsum : ∀ ι : Type u, IsIso (α.app (∐ fun _ : ι => ModuleCat.of R R)) := fun ι =>
    isIso_app_of_isColimit α (colimit.isColimit (Discrete.functor fun _ : ι => ModuleCat.of R R))
      (fun j => by
        obtain ⟨i⟩ := j
        exact (inferInstance : IsIso (α.app (ModuleCat.of R R))))
  have := PreservesColimitsOfSize.preservesFiniteColimits G₁
  have := PreservesColimitsOfSize.preservesFiniteColimits G₂
  have : Epi (freeCover (kernel (freeCover M))) := epi_freeCover _
  have hker : freeCover (kernel (freeCover M)) ≫ kernel.ι (freeCover M) =
      freeCover (kernel (freeCover M)) ≫ kernel.ι (freeCover M) := rfl
  have h0 : IsColimit (CokernelCofork.ofπ (freeCover M)
      (KernelFork.condition (KernelFork.ofι (kernel.ι (freeCover M))
        (kernel.condition (freeCover M))))) :=
    Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (freeCover M))
  have h1 := isCokernelEpiComp h0 (freeCover (kernel (freeCover M))) hker
  exact isIso_app_of_isColimit α h1 (fun j => by
    cases j with
    | zero => exact hsum _
    | one => exact hsum _)

end Devissage

variable [PreservesColimits F]

example (M : ModuleCat.{u} R) : IsIso (wattsMap (𝟭 (ModuleCat.{u} R)) M) := inferInstance

end Stacks.EilenbergWatts

end
