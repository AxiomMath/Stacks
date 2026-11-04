module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# Monomorphisms of modules on a representable algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf site
over `S`, with underlying scheme `T`.  The small étale site of the algebraic space `yoneda.obj U`
is equivalent to the small étale site of `T`, taken in the big étale site carried by the same
category of schemes, and that equivalence matches the two structure sheaves on the nose:
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and
`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`.  The induced equivalence
of module categories is `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff` transports
quasi-coherence along it.

This file shows that the comparison functors preserve and reflect monomorphisms.

## Main results

* `AlgebraicGeometry.Space.mono_representedSmallEtaleModule_map_iff`: a morphism of modules on the
  small étale site of the scheme underlying `U` is a monomorphism exactly when the morphism it
  becomes on the small étale site of `yoneda.obj U` is.
* `AlgebraicGeometry.Space.mono_representedQuasicoherentSchemeEquivalence_map_iff`: the same for
  the equivalence between the quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the scheme
  underlying `U` and `QCoh(𝒪_{yoneda.obj U})`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)

/-! ### Monomorphisms -/

/-- **A monomorphism of modules on the small étale site of the scheme underlying `U` is a
monomorphism of the `𝒪`-modules they become on the small étale site of `yoneda.obj U`, and
conversely.** -/
theorem mono_representedSmallEtaleModule_map_iff
    {M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)} (f : M ⟶ N) :
    Mono ((representedSmallEtaleModuleEquivalence B S hS U).functor.map f) ↔ Mono f :=
  Stacks.mono_map_iff_of_isEquivalence
    (representedSmallEtaleModuleEquivalence B S hS U).functor f

/-- **A monomorphism of quasi-coherent modules on the scheme underlying `U` is a monomorphism of
the quasi-coherent `𝒪`-modules they become on the small étale site of `yoneda.obj U`, and
conversely.** -/
theorem mono_representedQuasicoherentSchemeEquivalence_map_iff
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (f : M ⟶ N) :
    Mono ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map f) ↔ Mono f :=
  Stacks.mono_map_iff_of_isEquivalence
    (representedQuasicoherentSchemeEquivalence B S hS U).functor f

end AlgebraicGeometry.Space

end
