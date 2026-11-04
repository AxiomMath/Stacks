module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# The associated module of a globally presented module is quasi-coherent on the site

`AlgebraicGeometry.BigFppfOver.isQuasicoherent_associatedModule` proves that the associated
module `𝓕^a` of a globally presented `𝒪_S`-module is quasi-coherent in Mathlib's sense,
`SheafOfModules.IsQuasicoherent`.  Stacks 03DV is stated about
`SheafOfModules.IsQuasicoherentOnSite`, the predicate of Stacks 03DL(6), and the passage from
the first to the second was recorded as unavailable: it goes through
`SheafOfModules.HasGlobalPresentation.of_presentation_of_preservesColimits`, whose
colimit-preservation hypothesis had no supply at the universe it asks for.

That hypothesis is discharged on every site by
`SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'`, so the passage is now
`SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent` and this file is its instantiation at
the big fppf site of `S` and at every localization of that site at an object.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_associatedModule`: if an `𝒪_S`-module `𝓕`
  admits a presentation on all of `S`, then `𝓕^a` is quasi-coherent on `(Sch/S)_fppf` in the
  sense of Stacks 03DL(6).
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_associatedModule_over`: and so is its
  restriction to every localization of that site at an object.

## Implementation notes

Nothing here carries a `stacks` attribute, and 03DV is not yet available.  Clause (1) of 03DV
asserts quasi-coherence of `𝓕^a` on `(Sch/S)_τ` for each of the five topologies `τ` and for an
*arbitrary* quasi-coherent `𝓕`, and clause (2) is about the small Zariski and small étale sites
of `S`.  Two gaps remain against clause (1).

The first is that `AlgebraicGeometry.BigFppfOver.associatedModule` is defined only for the fppf
topology: it is the pullback along `AlgebraicGeometry.BigFppfOver.structureMap`, which exists for
no coarser `SiteKind`, so this covers `τ = fppf` alone.  (The structure sheaf itself is not the
obstruction — `AlgebraicGeometry.FibredSite.baseStructureSheaf` supplies one for every
`SiteKind`; what is missing for the coarser `τ` is the comparison morphism.)

The second is the restriction to a global presentation.  For an arbitrary quasi-coherent `𝓕` the
source's proof chooses a Zariski covering `{S_i → S}` of `S` on which `𝓕` is presented and uses
`AlgebraicGeometry.BigFppfOver.associatedModuleOverObjIso`, `(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)}`, to
transport each presentation.  Transporting a presentation along that isomorphism needs the
localized comparison `AlgebraicGeometry.BigFppfOver.sliceStructureMap` to carry the unit object
to the unit object, which is `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal` for the
localized functor `CategoryTheory.Over.post (AlgebraicGeometry.BigFppfOver.opensToBig B S hS)`
and so needs that functor to be final.  What is proved here is therefore the case in which the
covering chosen by the source may be taken to be `{S}` itself.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DV for a globally presented module, in the predicate 03DV is stated in.**  If an
`𝒪_S`-module `𝓕` is a cokernel of a map between free modules on all of `S`, then the associated
module `𝓕^a` is quasi-coherent on the big fppf site of `S` in the sense of Stacks 03DL(6). -/
public theorem isQuasicoherentOnSite_associatedModule {𝓕 : S.Modules} (P : 𝓕.Presentation) :
    ((associatedModule B S hS).obj 𝓕).IsQuasicoherentOnSite :=
  have := isQuasicoherent_associatedModule B S hS P
  SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent _

/-- The restriction of `𝓕^a` to the big fppf site localized at any object is again
quasi-coherent in the sense of Stacks 03DL(6), for `𝓕` globally presented. -/
public theorem isQuasicoherentOnSite_associatedModule_over {𝓕 : S.Modules} (P : 𝓕.Presentation)
    (X : BigFppfOver B S hS) :
    (((associatedModule B S hS).obj 𝓕).over X).IsQuasicoherentOnSite :=
  have := isQuasicoherent_associatedModule_over B S hS P X
  SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent _

end BigFppfOver

end AlgebraicGeometry

end
