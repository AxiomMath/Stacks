module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Algebraic spaces whose quasi-coherent first cohomology vanishes

Several statements about an algebraic space `X` over a scheme `S` hold under the single
hypothesis that `H¹(X, 𝓕) = 0` for every quasi-coherent `𝒪_X`-module `𝓕`, together with
quasi-compactness and quasi-separatedness of `X`.  Stacks 07UY fixes that data, and writes `A`
for the ring `Γ(X, 𝒪_X)` of global regular functions.  Over such a space the comparison between
quasi-coherent modules and `A`-modules becomes an equivalence, and `X` turns out to be the
spectrum of `A`.

## Main definitions

* `AlgebraicGeometry.Space.CohomologyVanishingSituation` is the data of Stacks 07UY.
* `AlgebraicGeometry.Space.CohomologyVanishingSituation.globalFunctions` is the ring
  `A = Γ(X, 𝒪_X)` of the source.

## Main results

* `AlgebraicGeometry.Space.CohomologyVanishingSituation.instCommRingGlobalFunctions`: the ring
  of global functions is commutative, the multiplication being that of the structure sheaf.

## Implementation notes

Cohomology of `𝒪_X`-modules is `Stacks.Cohomology.SiteModules.globalModuleCohomology` on the
small étale ringed site of `X`, the right derived functor of global sections constructed for an
arbitrary ringed site in Stacks 071H, and the quasi-coherent modules are the objects of
`AlgebraicGeometry.Space.QuasicoherentSheaves` of Stacks 03G9.  The universe of the module
sections is independent of the universe of the schemes, which is why the vanishing hypothesis
quantifies over `QuasicoherentSheaves.{u, max (u + 1) m}`: the derived functors of global
sections are defined on module universes containing both the site and the structure rings, so
`max (u + 1) m` is the general module universe at which the hypothesis can be imposed.

Quasi-separatedness is the absolute notion
`AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of Stacks 03BS(3), quasi-separatedness
over the terminal scheme, which is why the ambient big fppf site is required to contain the
terminal scheme as well as the base.

The ring `A` is `Stacks.Cohomology.SiteModules.GlobalSectionRing`, that is, Mathlib's subring
`RingCat.sectionsSubring` of compatible families of sections of the structure sheaf.  The small
étale site need not have a terminal chart, so this limit over all charts is what global
sections on a site means.  Its elements are families of *commutative* ring elements, so the
subring is commutative; that is the content of `instCommRingGlobalFunctions`, which is needed
because `RingCat.sectionsSubring` is formed in `RingCat` and therefore only supplies a `Ring`
instance.  That instance adds `mul_comm` to `Subring.toRing` and nothing else, so it agrees at
instance transparency with the `Ring` structure `ModuleCat` uses and with
`AlgebraicGeometry.Space.structureGlobalSectionCommRing`.

## References

* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u m

/-- **Stacks 07UY.** A quasi-compact, quasi-separated algebraic space `X` over a scheme `S`
every one of whose quasi-coherent modules has vanishing first cohomology. -/
@[stacks 07UY]
structure CohomologyVanishingSituation where
  /-- The ambient big fppf site. -/
  site : BigFppfSite.{u}
  /-- The base scheme. -/
  base : Scheme.{u}
  /-- The base scheme belongs to the ambient big fppf site. -/
  containsBase : site.Contains base
  /-- The terminal scheme belongs to the ambient big fppf site, so that absolute
  quasi-separatedness can be expressed. -/
  containsTerminal : site.Contains (⊤_ Scheme.{u})
  /-- The algebraic space over the base. -/
  space : AlgebraicSpaces site base containsBase
  /-- The space is quasi-compact. -/
  quasiCompact : IsQuasiCompactSpace site base containsBase space.1
  /-- The space is quasi-separated. -/
  quasiSeparated :
    IsAbsolutelyQuasiSeparated site base containsBase containsTerminal space.1
  /-- Every quasi-coherent module has vanishing first cohomology. -/
  firstCohomologyVanishing :
    ∀ M : QuasicoherentSheaves.{u, max (u + 1) m} site base containsBase space.1 space.2,
      IsZero ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, m}
        (structureRingSheaf site base containsBase space) 1).obj M.obj)

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m})

/-- The ring `A = Γ(X, 𝒪_X)` of global regular functions on the space of a vanishing
situation. -/
abbrev globalFunctions :=
  Stacks.Cohomology.SiteModules.GlobalSectionRing
    (structureRingSheaf T.site T.base T.containsBase T.space)

/-- Global regular functions on an algebraic space form a commutative ring.

Only `mul_comm` is added to the subring's `Ring` instance `Subring.toRing`, so the ring
operations remain syntactically those over which `ModuleCat` and the `𝒪_X`-modules are
linear. -/
instance instCommRingGlobalFunctions : CommRing T.globalFunctions :=
  letI r : Ring T.globalFunctions := inferInstance
  { r with
    mul_comm := fun a b => Subtype.ext (funext fun U =>
      mul_comm (G := (structurePresheaf T.site T.base T.containsBase T.space.1).obj U)
        (a.1 U) (b.1 U)) }

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end
