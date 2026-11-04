module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement

/-!
# Full faithfulness of `𝓕 ↦ 𝓕^a` on the big fppf site, with no hypothesis

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful` proves full faithfulness
of `𝓕 ↦ 𝓕^a` over the hypothesis
`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` — the unit of the associated-module
adjunction is an isomorphism at every quasi-coherent `𝒪_S`-module — and
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent` reduces that
hypothesis to `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the descent of morphisms of
quasi-coherent modules along fpqc covering families.  That last hypothesis is now a theorem:
`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`, proved in
`StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement` by refining an fpqc covering to
a standard one.  This file composes the two steps, so that the fppf form of Stacks 0GN7 and of
Stacks 06VE (1) carries no hypothesis at all.

## Main results

* `AlgebraicGeometry.BigFppfOver.unitIsoOnQuasicoherent`:
  `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` with its hypothesis discharged.
* `AlgebraicGeometry.BigFppfOver.full_associatedModuleQcoh'` and
  `AlgebraicGeometry.BigFppfOver.faithful_associatedModuleQcoh'`: the two halves of
  **Stacks 0GN7 for `τ = fppf`**, unconditionally, and as instances — this is the form the
  colimit transfer of
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize`
  consumes.
* `AlgebraicGeometry.BigFppfOver.fullyFaithfulAssociatedModuleQcoh'`: the two together, as a
  `CategoryTheory.Functor.FullyFaithful`.

## Implementation notes

Nothing here carries a `stacks` attribute, and the reason is no longer a hypothesis.  Stacks
0GN7 quantifies over `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` and over both the big site
`QCoh((Sch/S)_τ, 𝒪)` and the small site `QCoh(S_τ, 𝒪)`; every statement below is the big fppf
site alone, which is a strictly smaller claim, so a tag would be an over-claim.  What is
missing is exactly the `τ`-generalisation, and nothing mathematical about the fppf case.

That generalisation is not blocked on the functor: a structure sheaf exists for every
`AlgebraicGeometry.SiteKind` (`AlgebraicGeometry.FibredSite.baseStructureSheaf`), and so does
the associated-module functor, `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`, the
pullback along `AlgebraicGeometry.BigFppfOver.baseStructureMap`, with
`baseAssociatedModule .fppf = associatedModule` by `rfl`.  What is missing is the `τ`-form of
the statements downstream of it — a `τ`-indexed `baseAssociatedModuleQcoh`, and then the
`τ`-forms of `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` and of the two results
below.  (An earlier phrasing of this paragraph, still present in some files of this chain, said
that no analogue of `AlgebraicGeometry.BigFppfOver.structureMap` is constructed at a coarser
topology.  That was true when written and is false now.)

## References

* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The unit of the associated-module adjunction is an isomorphism at every quasi-coherent
`𝒪_S`-module, with no hypothesis.**  `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`
discharged, by feeding `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms` to
`AlgebraicGeometry.BigFppfOver.unitIsoOnQuasicoherent_of_fpqcDescent`. -/
public theorem unitIsoOnQuasicoherent : UnitIsoOnQuasicoherent B S hS :=
  unitIsoOnQuasicoherent_of_fpqcDescent B S hS fpqcDescentOfQuasicoherentHoms

/-- **Stacks 0GN7 for `τ = fppf`, the fullness half, with no hypothesis.** -/
public instance full_associatedModuleQcoh' : (associatedModuleQcoh B S hS).Full :=
  full_associatedModuleQcoh B S hS (unitIsoOnQuasicoherent B S hS)

/-- **Stacks 0GN7 for `τ = fppf`, the faithfulness half, with no hypothesis.** -/
public instance faithful_associatedModuleQcoh' : (associatedModuleQcoh B S hS).Faithful :=
  faithful_associatedModuleQcoh B S hS (unitIsoOnQuasicoherent B S hS)

/-- **Stacks 0GN7 for `τ = fppf`, with no hypothesis**: the functor `𝓕 ↦ 𝓕^a` from the
quasi-coherent `𝒪_S`-modules to the modules on the big fppf site of `S` is fully faithful. -/
public noncomputable def fullyFaithfulAssociatedModuleQcoh' :
    (associatedModuleQcoh B S hS).FullyFaithful :=
  fullyFaithfulAssociatedModuleQcoh B S hS (unitIsoOnQuasicoherent B S hS)

end BigFppfOver

end AlgebraicGeometry

end
