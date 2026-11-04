module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Extension by zero injects into the direct image

For an open immersion `j : U ⟶ X` and a sheaf `F` of `Λ`-modules on `U_étale`, the canonical map
`j_! F ⟶ j_* F` (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroToDirectImage`) is a
monomorphism. Its kernel `K` vanishes after restriction to `U`, where the map is a split
monomorphism followed by an isomorphism, and after inverse image to the closed complement `Z`
of `U`, since there `j_! F` itself vanishes; inverse images to `Z` and to `U` jointly reflect
isomorphisms (`Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleInverseImage`), so `K = 0`.

The cokernel of this monomorphism is the sheaf of local terms of `F` at the boundary, the first
of the two local terms of `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`.

## Main results

* `Stacks.EtaleCohomology.mono_etaleModuleExtensionByZeroToDirectImage_app`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **`j_! F ⟶ j_* F` is a monomorphism** for an open immersion `j`. -/
theorem mono_etaleModuleExtensionByZeroToDirectImage_app (F : EtaleModules.{u, 0} Λ U) :
    Mono ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app F) := by
  let Zc : TopologicalSpace.Closeds X :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact (compl_compl _).symm
  let u := (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app F
  let adj := etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j
  let Rj := etaleModuleRestriction.{u, 0} Λ j
  have hRu : Mono (Rj.map u) := by
    rw [show u = adj.unit.app ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ j).map
          (inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app F)) from
      etaleModuleExtensionByZeroToDirectImage_app Λ j F, Functor.map_comp]
    have : IsSplitMono (Rj.map (adj.unit.app ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F))) :=
      ⟨⟨⟨adj.counit.app _, adj.left_triangle_components _⟩⟩⟩
    exact mono_comp _ _
  have : HasKernels (EtaleModules.{u, 0} Λ X) := Abelian.has_kernels
  let K := kernel u
  have hKj : IsZero (Rj.obj K) := by
    refine IsZero.of_mono_eq_zero (Rj.map (kernel.ι u)) ?_
    rw [← cancel_mono (Rj.map u), zero_comp, ← Rj.map_comp, kernel.condition, Rj.map_zero]
  have : PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} Λ i) :=
    etaleModuleInverseImage_preservesFiniteLimits _ _
  have hKi : IsZero ((etaleModuleInverseImage.{u, 0} Λ i).obj K) :=
    IsZero.of_mono_eq_zero ((etaleModuleInverseImage.{u, 0} Λ i).map (kernel.ι u))
      ((isZero_etaleModuleInverseImage_extensionByZero Λ i j hij F).eq_of_tgt _ _)
  have : IsIso ((etaleModuleInverseImage.{u, 0} Λ i).map (0 : K ⟶ K)) :=
    hKi.isIso hKi _
  have hKj' := hKj.of_iso ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app K)
  have : IsIso ((etaleModuleInverseImage.{u, 0} Λ j).map (0 : K ⟶ K)) :=
    hKj'.isIso hKj' _
  have := isIso_of_isIso_etaleModuleInverseImage Λ i j hij (0 : K ⟶ K)
  exact Preadditive.mono_of_kernel_zero ((IsZero.of_mono_zero K K).eq_of_src _ _)

end Stacks.EtaleCohomology

end
