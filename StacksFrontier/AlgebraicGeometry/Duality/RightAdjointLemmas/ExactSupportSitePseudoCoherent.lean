module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison

/-!
# Site-level pseudo-coherence of `Ri_* 𝒪_Z`

For a pseudo-coherent closed immersion of schemes `i : Z ⟶ X`, the derived pushforward
`Ri_* 𝒪_Z` is a pseudo-coherent object of `D(𝒪_X)`. That is [Stacks, Tag 0AVX], proved as
`AlgebraicGeometry.Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf` at
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, the ringed-space notion of
[Stacks, Tag 08CB]. The tensor–Hom theory of [Stacks, Tag 0ATN] is stated on an arbitrary
ringed site and asks for `AlgebraicGeometry.RingedSite.IsPseudoCoherent`, the notion of
[Stacks, Tag 08FT]. This file supplies the conclusion at the site notion, by the comparison of
`StacksFrontier/Topology/Sheaves/Cohomology/PseudoCoherence/RingedSiteComparison.lean`.

## Main results

* `AlgebraicGeometry.Scheme.isPseudoCoherentSite_pushforward_derivedStructureSheaf`:
  `Ri_* 𝒪_Z` is pseudo-coherent at the ringed site of opens of `X`.

## Implementation notes

The two pseudo-coherence predicates localise differently: [Stacks, Tag 08CB] on open subspaces
and [Stacks, Tag 08FT] on covering sieves of the site of opens. The site used here is
`Stacks.SheafOfModules.ringedSite X.sheaf`.

## References

* [Stacks Project, Tag 0AVX](https://stacks.math.columbia.edu/tag/0AVX)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- If a closed immersion of schemes `i : Z ⟶ X` is pseudo-coherent, then `Ri_* 𝒪_Z` is a
pseudo-coherent object of `D(𝒪_X)` at the ringed site of opens of `X`, in the sense of
[Stacks, Tag 08FT]. -/
@[stacks 0AVX "for a closed immersion, at the site notion of pseudo-coherence"]
theorem isPseudoCoherentSite_pushforward_derivedStructureSheaf (hi : PseudoCoherent i) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherent
      ((modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Z.sheaf))) :=
  RingedSpace.PseudoCoherence.isPseudoCoherent_ringedSite' X.toRingedSpace _
    (isPseudoCoherent_pushforward_derivedStructureSheaf i hi)

end AlgebraicGeometry.Scheme

end
