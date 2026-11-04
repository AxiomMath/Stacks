module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# Coherence of a module on an algebraic space needs no quasi-coherence hypothesis

`AlgebraicGeometry.Space.IsCoherent`, which is Stacks 07UA, asks two things of a module on an
algebraic space: quasi-coherence on the small étale ringed site, which is Stacks 03DL(6), and
coherence on that site, which is Stacks 03DL(8).  The second implies the first on an arbitrary
site, by `SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite`, so the first clause is
redundant and coherence on the site alone suffices.

## Main results

* `AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite`: a module on an algebraic space whose
  restriction to the small étale ringed site is coherent in the sense of Stacks 03DL(8) is
  coherent in the sense of Stacks 07UA.
* `AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite`: the two notions agree.

## Implementation notes

The statements are at the module universe `u` of the schemes, the universe of the structure
sheaf of the small étale ringed site, because
`SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite` builds the presentations out of global
sections of the structure sheaf and so needs the module universe to agree with the ring universe.
That is also the universe in which the ambient category of modules is abelian and in which
`AlgebraicGeometry.Space.coherentModules_abelian_of_closure` is stated.

Neither result is registered as an instance: `AlgebraicGeometry.Space.IsCoherent` extends
`SheafOfModules.IsCoherentOnSite`, so an instance in this direction would close a cycle with
that parent projection.

## References

* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The quasi-coherence clause of Stacks 07UA is redundant.**  A module on an algebraic space
which is coherent on its small étale ringed site, in the sense of Stacks 03DL(8), is coherent in
the sense of Stacks 07UA: coherence on a site implies quasi-coherence on it. -/
theorem isCoherent_of_isCoherentOnSite (M : Modules.{u, u} B S hS F hF)
    [SheafOfModules.IsCoherentOnSite M] : IsCoherent B S hS F hF M where

/-- **Coherence of a module on an algebraic space is coherence on its small étale ringed
site.**  `AlgebraicGeometry.Space.IsCoherent` is quasi-coherence on that site together with
coherence on it, and the first clause follows from the second: a coherent sheaf of modules on an
arbitrary site is quasi-coherent, which is Stacks 03DL(8) ⟹ 03DL(6), proved as
`SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite`.  The module universe is the universe
of the structure rings, which that implication pins. -/
theorem isCoherent_iff_isCoherentOnSite (M : Modules.{u, u} B S hS F hF) :
    IsCoherent B S hS F hF M ↔ SheafOfModules.IsCoherentOnSite M :=
  ⟨fun h => h.toIsCoherentOnSite, fun h =>
    have : SheafOfModules.IsCoherentOnSite M := h
    isCoherent_of_isCoherentOnSite B S hS F hF M⟩

end AlgebraicGeometry.Space

end
