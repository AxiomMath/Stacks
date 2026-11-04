module

public import StacksFrontier.AlgebraicGeometry.GenericStalkBaseChange.SheafBasis
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic

/-!
# Restricted to the complement of `V(I)`, the inclusion `I ^ n • G ⟶ G` is an isomorphism

This upgrades the pointwise statement
`Stacks.AlgebraicGeometry.IdealPowerComparison.bijective_idealPowerMultiple_ι_app` to an
isomorphism in `U.toScheme.Modules` for `U = X \ V(I)`, which is the form in which the step
`F'|_U = F|_U` of the proofs of [Stacks, Tag 01PQ] and [Stacks, Tag 01YB] is consumed: it is
what inverts the left-hand map of the equation that [Stacks, Tag 01YB]'s
`homsOverOpen_restrict` asserts.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerComparison.isIso_restrictFunctor_map_ι`.

## Implementation notes

The comparison of scalar actions along the open immersion is avoided rather than confronted. The
component of `(Scheme.Modules.restrictFunctor U.ι).map h` over an open `V` of `U` is, as a
*function*,
literally the component of `h` over `U.ι ''ᵁ V`
(`Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictFunctor_map_val_app`, proved by `rfl`),
so bijectivity transfers with no comparison of the two scalar actions; and in `ModuleCat` a
bijective morphism is an isomorphism. The two module structures are therefore never asked to
agree, which is the step that otherwise needs a compiler escape.

`Stacks.AlgebraicGeometry.GenericStalkBaseChange.isIso_of_isIso_val_app_basis` then assembles
the components, applied to the basis consisting of *all* opens — the hypothesis is about a basis
only because its usual callers compute sections over affine opens alone.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerHomColimit
open Stacks.LocalCohomology

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerComparison

/-- The set of all open sets is a basis of the topology, in the indexed form that
`Stacks.AlgebraicGeometry.GenericStalkBaseChange.isIso_of_isIso_val_app_basis` wants. -/
theorem isBasis_range_id (α : Type*) [TopologicalSpace α] :
    Opens.IsBasis (Set.range (id : Opens α → Opens α)) :=
  Opens.isBasis_iff_nbhd.mpr fun {U _} hx ↦ ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩

variable {X : Scheme.{u}}

/-- **Restricted to the complement of `V(I)`, the inclusion `I ^ n • G ⟶ G` is an
isomorphism.** -/
theorem isIso_restrictFunctor_map_ι (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    [G.IsQuasicoherent] :
    IsIso ((Scheme.Modules.restrictFunctor (idealComplement I).ι).map
      (idealPowerMultiple I n G).ι) := by
  refine GenericStalkBaseChange.isIso_of_isIso_val_app_basis
    (B := (id : Opens _ → Opens _)) (isBasis_range_id _) _ fun V ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_idealPowerMultiple_ι_app I n G ((idealComplement I).ι_image_le V)

/-- `isIso_restrictFunctor_map_ι` as an instance. `AlgebraicGeometry.Scheme.Modules` is a `def`,
so instance search does not reach an `IsIso` fact stated about a morphism in it through the
underlying `SheafOfModules`; the fact has to be registered at this spelling for `inv` to
elaborate. -/
instance instIsIsoRestrictFunctorMapIdealPowerMultipleι (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) [G.IsQuasicoherent] :
    IsIso ((Scheme.Modules.restrictFunctor (idealComplement I).ι).map
      (idealPowerMultiple I n G).ι) :=
  isIso_restrictFunctor_map_ι I n G

end Stacks.AlgebraicGeometry.IdealPowerComparison

end
