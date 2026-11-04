module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceClosedSubspaceIdeal

/-!
# The ideal sheaf of a closed subspace of a represented algebraic space, as a module

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an object of the big fppf category
over `S`, and let `Z ⊆ h_V = yoneda.obj V` be a closed subspace.  Two sheaves of ideals are
attached to `Z`:

* the defining ideal sheaf `𝓘_Z ⊆ 𝒪_{h_V}` of Stacks 083B, a submodule of the structure sheaf on
  the **small étale site** of `h_V` (`definingIdealSheaf`), and
* the Zariski sheaf of ideals `I ⊆ 𝒪_V` of the **scheme** `V` that `schemeSpaceIdeal` cuts out,
  whose reading as a submodule of the structure sheaf is
  `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`.

At every étale chart `A` of `h_V` the ideal sheaf that `𝓘_Z` induces on the chart scheme is the
inverse image of `I` along the chart (`comap_schemeSpaceIdeal_eq_idealSheafDataOfChart`).  The
comparison **as sheaves of modules** asserts that `𝓘_Z` is the inverse image `ε^*I` of `I` along
the comparison `ε = id_{small, étale, Zar}` of Stacks 070R, read on the represented space by
`representedAssociatedModule`.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `SchemeSpaceIdealModuleComparison`: the comparison, for every `V` and every closed subspace `Z`.
* `schemeSpaceIdealModuleComparisonIso`: the comparison read at one closed subspace, as a chosen
  isomorphism.

## Main results

* `preservesMonomorphisms_representedAssociatedModule`: `ε^*` preserves monomorphisms, `ε^*` being
  left exact by Stacks 08H8.  Applied to the inclusion `I ⊆ 𝒪_V`, this says that `ε^*I` is a sheaf
  of ideals of `𝒪_{h_V}`.
* `mono_representedAssociatedModule_map`: the same, read at one monomorphism.

## References

* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B), the ideal sheaf of a
  closed subspace.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the correspondence on the
  small étale site.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the comparison `ε`.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the associated
  module.
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), part (2), quasi-coherent
  modules on the sites of a scheme.
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8), exactness of `ε^*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison as a named statement -/

/-- **The defining ideal sheaf of a closed subspace of a represented algebraic space is the inverse
image along `ε` of a Zariski sheaf of ideals of the representing scheme.**

For every object `V` of the big fppf category over `S` and every closed subspace `Z ⊆ h_V`, the
defining ideal sheaf `𝓘_Z ⊆ 𝒪_{h_V}` of Stacks 083B is the image under
`AlgebraicGeometry.Space.representedAssociatedModule` — the associated-module functor of
Stacks 03DU (4), read on the represented space — of the submodule of `𝒪_V` attached to
`AlgebraicGeometry.Space.schemeSpaceIdeal`. -/
abbrev SchemeSpaceIdealModuleComparison : Prop :=
  ∀ (V : BigFppfOver B S hS) (Z : ClosedSubspaces B S hS (yoneda.obj V)),
    Nonempty ((definingIdealSheaf B S hS (schemeSpace V) Z).toSheafOfModules ≅
      (representedAssociatedModule B S hS V (schemeSpace V).property).obj
        (schemeSpaceIdeal B S hS V Z).unitSubmodule.toSheafOfModules)

/-- The comparison of `AlgebraicGeometry.Space.SchemeSpaceIdealModuleComparison` read at one closed
subspace, as a chosen isomorphism. -/
noncomputable def schemeSpaceIdealModuleComparisonIso
    (h : SchemeSpaceIdealModuleComparison B S hS) (V : BigFppfOver B S hS)
    (Z : ClosedSubspaces B S hS (yoneda.obj V)) :
    (definingIdealSheaf B S hS (schemeSpace V) Z).toSheafOfModules ≅
      (representedAssociatedModule B S hS V (schemeSpace V).property).obj
        (schemeSpaceIdeal B S hS V Z).unitSubmodule.toSheafOfModules :=
  (h V Z).some

/-! ### The injectivity half -/

/-- **`ε^*` preserves monomorphisms**, being left exact (Stacks 08H8). -/
theorem preservesMonomorphisms_representedAssociatedModule (V : BigFppfOver B S hS) :
    (representedAssociatedModule B S hS V (schemeSpace V).property).PreservesMonomorphisms :=
  have hfl : PreservesFiniteLimits
      (representedAssociatedModule B S hS V (schemeSpace V).property) :=
    preservesFiniteLimits_representedAssociatedModule B S hS V (schemeSpace V).property
  have : PreservesLimitsOfShape WalkingCospan
      (representedAssociatedModule B S hS V (schemeSpace V).property) :=
    hfl.preservesFiniteLimits _
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **The inverse image along `ε` of a monomorphism of `𝒪_V`-modules is a monomorphism.** -/
theorem mono_representedAssociatedModule_map (V : BigFppfOver B S hS)
    {M N : ((BigFppfOver.toScheme B S hS).obj V).Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((representedAssociatedModule B S hS V (schemeSpace V).property).map φ) :=
  have := preservesMonomorphisms_representedAssociatedModule B S hS V
  inferInstance

end AlgebraicGeometry.Space

end
