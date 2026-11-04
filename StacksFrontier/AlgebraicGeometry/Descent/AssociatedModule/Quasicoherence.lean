module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalPresentationObstruction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor

/-!
# The associated module of a globally presented module

Stacks 03DV says that the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕` is a
quasi-coherent module on `(Sch/S)_τ`.  The source proves it by choosing a Zariski covering
`{S_i → S}` on which `𝓕` is the cokernel of a map of free modules — which is possible by the
very definition of quasi-coherence — observing that `𝓕^a` then sits in the corresponding
sequence on each `(Sch/S_i)_τ`, and appealing to Stacks 03DN, quasi-coherence being local on a
covering.

This file proves the middle step, for `τ = fppf` and over all of `S`: if `𝓕` is a cokernel of a
map of free `𝒪_S`-modules, then `𝓕^a` is a cokernel of a map of free `𝒪`-modules on
`(Sch/S)_fppf`.  Nothing is needed beyond the two properties of the associated-module functor
that the source uses implicitly: it preserves colimits, being a left adjoint
(`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModule`), and it carries the
structure sheaf of `S` to the structure sheaf of the big fppf site
(`AlgebraicGeometry.BigFppfOver.associatedModuleUnitIso`), hence free modules to free modules on
the same index set.

## Main results

* `AlgebraicGeometry.BigFppfOver.presentationAssociatedModule`: a presentation of `𝓕` gives a
  presentation of `𝓕^a`, with the same generators and relations.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherent_associatedModule`: hence `𝓕^a` is
  quasi-coherent on the big fppf site of `S` as soon as `𝓕` admits a *global* presentation.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherent_associatedModule_over`: and so is its
  restriction to every slice of that site, which is the form in which Stacks 03DN consumes it.

## Implementation notes

`SheafOfModules.Presentation.map` asks for sheafification on the target site in the strong form
`CategoryTheory.HasSheafify`, whereas the big fppf site carries only the weak form as an
instance, `AlgebraicGeometry.BigFppfOver.hasWeakSheafify_topology`.  The strong form holds for
the same reason — the big fppf category over `S` is essentially small — and is installed here as
`AlgebraicGeometry.BigFppfOver.hasSheafify_topology`, together with the instances for the
localizations of the site at one and at two objects, which is what
`SheafOfModules.IsQuasicoherent` and `SheafOfModules.isQuasicoherent_over` ask for.

The associated-module functor is stated with source `AlgebraicGeometry.Scheme.Modules`, which is
a `def` carrying its own `CategoryTheory.Category` instance rather than a reducible abbreviation
of `SheafOfModules.{u} S.ringCatSheaf`.  The two categories are definitionally equal but not at
the transparency instance search uses, so the colimit-preservation instance found for the
functor at the first spelling is not found at the second, which is the one
`SheafOfModules.Presentation.map` unifies against.  The proof below therefore names the functor
at the `SheafOfModules` spelling and transports the instance to it by hand.

Quasi-coherence here is Mathlib's `SheafOfModules.IsQuasicoherent`, equivalently
`AlgebraicGeometry.BigFppfOver.HasLocalFreePresentations` with its covering index type left
free, and *not* the predicate `SheafOfModules.IsQuasicoherentOnSite` of Stacks 03DL(6) in which
Stacks 03DV is stated in this library.  The two differ by the universe of the presentations they
quantify over, and the passage from the first to the second is
`SheafOfModules.HasGlobalPresentation.of_presentation_of_preservesColimits`.  **Its hypothesis
— that the universe lift of sheaves of modules preserves colimits — is available**, on every
site and with no size
assumption: `SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'`, whence
`SheafOfModules.Presentation.hasGlobalPresentation`.

That hypothesis needs `PreservesColimitsOfShape K (SheafOfModules.toSheaf _)` at `K : Type u`
with `Category.{u} K`, while `toSheaf_preservesColimits` supplies `Category.{u + 1} K`.  This is
a **unification** issue, not a mathematical one: `preservesColimitsOfSize_shrink` closes the gap
once its universes are written out explicitly, and left to unification it reports
`stuck at solving universe constraint`.

So nothing here carries a `stacks` attribute.  Stacks 03DV asserts
`SheafOfModules.IsQuasicoherentOnSite` for an arbitrary quasi-coherent `𝓕`; what is proved here
is the globally presented case of the middle step of its proof.  **Both steps it needs are
proved** — the universe bridge above, and the compatibility of `𝓕 ↦ 𝓕^a` with restriction to an
open of `S`, which is `AlgebraicGeometry.BigFppfOver.associatedModuleOverIso`
(`…/AssociatedModule/OpenRestriction.lean:259`) — and the arbitrary case is
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`
(`…/AssociatedModule/OpenCoverQuasicoherence.lean:154`).  It is still untagged, because clause (1)
of 03DV is asserted for all five `τ` and `structureMap` is fppf-only, and clause (2) is untouched.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on the big fppf site of `S` have a left exact sheafification, the big
fppf category over `S` being essentially small. -/
public instance hasSheafify_topology : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Abelian presheaves on a localization of the big fppf site of `S` at an object have a left
exact sheafification. -/
public instance hasSheafify_over_topology (X : BigFppfOver B S hS) :
    HasSheafify ((topology B S hS).over X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Abelian presheaves on a localization of the big fppf site of `S` at two successive objects
have a left exact sheafification. -/
public instance hasSheafify_over_over_topology (X : BigFppfOver B S hS)
    (Y : Over X) : HasSheafify (((topology B S hS).over X).over Y) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on a localization of the big fppf site of `S` at two
successive objects are the locally bijective maps. -/
public instance wEqualsLocallyBijective_over_over_topology (X : BigFppfOver B S hS) (Y : Over X) :
    (((topology B S hS).over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The big fppf category over `S` admits binary products, being a slice of a category with
fibre products. -/
public instance hasBinaryProducts : HasBinaryProducts (BigFppfOver B S hS) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- **Stacks 03DV, the step the source calls clear, over all of `S`.**  A presentation of an
`𝒪_S`-module `𝓕` — an exhibition of `𝓕` as a cokernel of a map between free modules — gives a
presentation of the associated module `𝓕^a` on the big fppf site of `S`, with the same
generators and relations.

The associated-module functor preserves colimits, being a left adjoint, and carries the
structure sheaf of `S` to the structure sheaf of the big fppf site, hence carries free modules
to free modules on the same index set. -/
public noncomputable def presentationAssociatedModule {𝓕 : S.Modules} (P : 𝓕.Presentation) :
    ((associatedModule B S hS).obj 𝓕).Presentation := by
  letI F : SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u} (structureSheaf B S hS) :=
    associatedModule B S hS
  letI : PreservesColimitsOfSize.{u, u} F := preservesColimitsOfSize_associatedModule B S hS
  exact P.map F (associatedModuleUnitIso B S hS).symm

/-- **Stacks 03DV for a globally presented module.**  If an `𝒪_S`-module `𝓕` is a cokernel of a
map between free modules on all of `S`, then the associated module `𝓕^a` is quasi-coherent on
the big fppf site of `S`.

This is Stacks 03DV in the case where the Zariski covering chosen by its proof may be taken to
be `{S}` itself. -/
public theorem isQuasicoherent_associatedModule {𝓕 : S.Modules} (P : 𝓕.Presentation) :
    ((associatedModule B S hS).obj 𝓕).IsQuasicoherent :=
  (presentationAssociatedModule B S hS P).isQuasicoherent

/-- The restriction of `𝓕^a` to the big fppf site localized at any object is again
quasi-coherent, for `𝓕` globally presented.  This is the form in which the covering argument of
Stacks 03DN consumes the previous result. -/
public theorem isQuasicoherent_associatedModule_over {𝓕 : S.Modules} (P : 𝓕.Presentation)
    (X : BigFppfOver B S hS) :
    (((associatedModule B S hS).obj 𝓕).over X).IsQuasicoherent :=
  have := isQuasicoherent_associatedModule B S hS P
  SheafOfModules.isQuasicoherent_over _ X

end BigFppfOver

end AlgebraicGeometry

end
