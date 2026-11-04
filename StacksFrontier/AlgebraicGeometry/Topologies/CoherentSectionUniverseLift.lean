module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Coherence under the universe lift of the sections

`SheafOfModules.uliftForPresentation` raises the universe of the sections of a sheaf of modules
by an arbitrary amount while keeping its coefficient ring sheaf.  This file proves that coherence
on the site, Stacks 03DL(8), is unchanged by that operation, in the direction that raises the
universe.

## Main results

* `SheafOfModules.isCoherentOnSite_uliftForPresentation`: **the universe lift of the sections of
  a module coherent on a site is coherent on that site.**

## Implementation notes

Both clauses of `SheafOfModules.IsCoherentOnSite` transport along a sectionwise additive
equivalence which is semilinear over a sectionwise ring equivalence and compatible with
restriction — the first by
`Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv`, the second by
`Stacks.SheafOfModules.CoherentLift.relations_isFiniteType_of_sectionwiseEquiv` — and neither
needs the two module universes to agree.  For `SheafOfModules.uliftForPresentation` the ring sheaf
does not move, so the ring equivalence is the identity and the module equivalence is
`AddEquiv.ulift.symm`; all four compatibility conditions are `rfl`, the sections of the lift being
`ULift` of the sections on the nose.

This is `Stacks.SheafOfModules.CoherentLift.isCoherentOnSite_liftModule_iff` with the ring
equivalence specialized from `ULift.ringEquiv` to the identity: that statement lifts the
structure sheaf along with the sections, which changes the ringed site, whereas
`SheafOfModules.uliftForPresentation` keeps it.  The quasi-coherent counterpart is
`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}}

/-- **The universe lift of the sections of a module coherent on a site is coherent on that
site.**

Finite type transports by `Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv` and the
finite-type condition on the sheaves of relations by
`Stacks.SheafOfModules.CoherentLift.relations_isFiniteType_of_sectionwiseEquiv`, along the
sectionwise equivalence `AddEquiv.ulift.symm` over the identity of the coefficient rings; the
sections of the lift are the `ULift` of the sections, so every compatibility is `rfl`. -/
theorem isCoherentOnSite_uliftForPresentation (M : SheafOfModules.{m} R)
    (h : IsCoherentOnSite M) :
    IsCoherentOnSite (uliftForPresentation.{u, v, r, m, t} M) where
  isFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv
      (fun _ ↦ RingEquiv.refl _) (fun _ ↦ AddEquiv.ulift.symm) (fun _ _ _ ↦ rfl)
      (fun _ _ ↦ rfl) h.isFiniteType
  kernel_isFiniteType U n s :=
    Stacks.SheafOfModules.CoherentLift.relations_isFiniteType_of_sectionwiseEquiv
      (fun _ ↦ RingEquiv.refl _) (fun _ _ ↦ rfl) (fun _ ↦ AddEquiv.ulift.symm)
      (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) s (h.kernel_isFiniteType U n _)

end SheafOfModules

end
