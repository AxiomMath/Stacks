module

public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.SheafMapIsIso
public import StacksFrontier.RingTheory.GradedAlgebra.ModuleTruncation

/-!
# Truncating a graded module does not change its sheaf on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, let `M = ⨁_{i ∈ ℤ} 𝒨 i` be a `ℤ`-graded
`S`-module in the same universe as `S`, and let `N₀ : ℤ` be a cut. The truncation
`M_{≥ N₀} = ⨁_{i ≥ N₀} 𝒨 i`, `Stacks.GradedModule.truncationAbove`, is again a graded `S`-module,
and the inclusion `M_{≥ N₀} ⊆ M` is degree-preserving. The induced morphism of associated sheaves
on `Proj(S)` is an **isomorphism**,

`(M_{≥ N₀})~ ≅ M~`.

## Main results

* `Stacks.GradedModule.isIso_associatedModuleSheafMap_truncationAbove`: the inclusion of the
  truncation induces an isomorphism of associated sheaves on `Proj(S)`.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
  (isIso_associatedModuleSheafMap_of_eventually_bijective)
open scoped Stacks.GradedLocalization

namespace Stacks.GradedModule

universe u w t

variable {S M : Type u} {σ : Type w}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {τ : Type t} [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨] (N₀ : ℤ)

/-- **Truncating above a cut does not change the sheaf on `Proj`.** The inclusion
`M_{≥ N₀} ⊆ M` is degree-preserving, injective, and surjective onto every homogeneous piece of
degree `≥ N₀`, so the morphism it induces on associated sheaves is an isomorphism.

For `N₀ = 0` this is the step of Stacks 0BXD which identifies the sheaf of
`⨁_{n ≥ 0} Γ(X, ℱ(n))` with that of `⨁_{n ∈ ℤ} Γ(X, ℱ(n))`. -/
theorem isIso_associatedModuleSheafMap_truncationAbove :
    IsIso (associatedModuleSheafMap 𝒮 (truncationAboveGrading 𝒮 𝒨 N₀) 𝒨
      (truncationAbove 𝒮 𝒨 N₀).subtype (truncationAbove_subtype_mem 𝒮 𝒨 N₀)) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective 𝒮
    (truncationAboveGrading 𝒮 𝒨 N₀) 𝒨 (truncationAbove 𝒮 𝒨 N₀).subtype
    (truncationAbove_subtype_mem 𝒮 𝒨 N₀)
    (N₀ := N₀)
    (fun _ _ _ _ hx => eq_zero_of_truncationAbove_subtype_eq_zero 𝒮 𝒨 N₀ hx)
    (fun _ hj _ hm => exists_mem_truncationAboveGrading 𝒮 𝒨 N₀ hj hm)

end Stacks.GradedModule

end
