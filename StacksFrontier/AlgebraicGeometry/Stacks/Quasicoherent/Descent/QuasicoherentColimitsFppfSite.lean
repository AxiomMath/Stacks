module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssSurjectivityFpqcRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsBigSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsUnconditional

/-!
# Stacks 0GNC (1), (2), (3) for `τ = fppf`, with no hypothesis

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsUnconditional`
states the first three clauses of Stacks 0GNC for the big fppf site of a scheme `S` over one
hypothesis, `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` — the
essential surjectivity half of Stacks 03DX (1), that every quasi-coherent `𝒪`-module on
`(Sch/S)_fppf` is an `𝓕^a`.  That hypothesis is now a theorem,
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`, so
the clauses are stated here with it discharged and carry the tag.

## Main results

* `AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_isQuasicoherentOnSite_unconditional`:
  **Stacks 0GNC (2)** for `τ = fppf` — quasi-coherence of `𝒪`-modules on `(Sch/S)_fppf` is
  closed under colimits of every shape indexed at the size of the site.
* `AlgebraicGeometry.BigFppfOver`
  `.isClosedUnderColimitsOfShape_discrete_isQuasicoherentOnSite_unconditional`: **Stacks
  0GNC (1)** for `τ = fppf` — a direct sum of quasi-coherent modules is quasi-coherent.
* `AlgebraicGeometry.BigFppfOver`
  `.isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite_unconditional`:
  **Stacks 0GNC (3)** for `τ = fppf` — the cokernel of a morphism of quasi-coherent modules is
  quasi-coherent.

## Implementation notes

The clause strings say `τ = fppf`, which is the scope of the *statements* below: they are about
the fppf structure sheaf `structureSheaf B S hS` itself rather than about
`FibredSite.baseRingStructureSheaf _ .fppf`.  The three proofs are the `τ`-indexed statements of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsBigSites` at
`τ = .fppf`, which hold at every `τ` with no hypothesis — the essential surjectivity half of
Stacks 03DX (1) at `(Sch/S)_τ`,
`AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule τ`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/QuasiCoherentSmallEtaleBigSite.lean:127`), that
they once carried as a hypothesis is now the theorem
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`, and the clauses
at the four coarser topologies are registered there.
Clause (4) of the source is not here; it is proved at every `τ` on
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`).

The index shapes are `K : Type u` with `Category.{u} K`, `u` being the universe of the morphisms
of the site and of its structure sheaf; this is the convention of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer`, whose
implementation notes explain why a bare `HasColimits` would say something else.  The two
colimit-existence instance arguments that
`AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite` carries —
colimits of shape `K` in `ModuleCat.{u} R` and in the `𝒪_S`-modules of the small Zariski site —
are found by instance search at these shapes, so nothing below has a hypothesis.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GNC (2)** for `τ = fppf`: a colimit of quasi-coherent `𝒪`-modules on the big fppf
site of a scheme `S` is quasi-coherent.

`AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite`, the
`τ`-indexed form of the clause, at `τ = .fppf`; the statement here is the one about the fppf
structure sheaf itself, and the two agree because
`FibredSite.baseRingStructureSheaf B S hS .fppf = structureSheaf B S hS` holds by `rfl`.
This is the transfer the source performs with Lemma 06VE: the colimit is formed in `QCoh(𝒪_S)`,
where it exists and is quasi-coherent, and carried up by `𝓕 ↦ 𝓕^a`, which preserves colimits
and whose essential image is exactly the quasi-coherent modules of the site. -/
@[stacks 0GNC "part (2), big site at τ = fppf"]
public theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite_unconditional
    (K : Type u) [Category.{u} K] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape K :=
  isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite B S hS .fppf K

/-- **Stacks 0GNC (1)** for `τ = fppf`: a direct sum of quasi-coherent `𝒪`-modules on the big
fppf site of a scheme `S` is quasi-coherent.  A direct sum is a colimit over a discrete index
category, which is how the source argues it. -/
@[stacks 0GNC "part (1), big site at τ = fppf"]
public theorem isClosedUnderColimitsOfShape_discrete_isQuasicoherentOnSite_unconditional
    (I : Type u) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape (Discrete I) :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite_unconditional B S hS (Discrete I)

/-- **Stacks 0GNC (3)** for `τ = fppf`: the cokernel of a morphism of quasi-coherent
`𝒪`-modules on the big fppf site of a scheme `S` is quasi-coherent.  A cokernel is a colimit
over `CategoryTheory.Limits.WalkingParallelPair`, and the source obtains clause (3) from
clause (2) in exactly this way. -/
@[stacks 0GNC "part (3), big site at τ = fppf"]
public theorem
    isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite_unconditional :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape WalkingParallelPair :=
  isClosedUnderColimitsOfShape_walkingParallelPair_baseIsQuasicoherentOnSite B S hS .fppf

end BigFppfOver

end AlgebraicGeometry

end
