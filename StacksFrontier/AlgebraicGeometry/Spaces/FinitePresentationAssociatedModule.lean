module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationSiteEquivalence

/-!
# Finite presentation of the associated module on a small étale site

Let `S` be a scheme and let `𝓕` be an `𝒪_S`-module of finite presentation on the small Zariski
site of `S`.  This file proves that the small-étale module `𝓕^a` attached to `𝓕` by Stacks
03DU (4) is of finite presentation, and transports that along the equivalence of Stacks 04M0
between the small étale site of a scheme of the big fppf site and the small étale site of the
algebraic space the scheme represents.

This is the finite-presentation analogue of
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`,
Stacks 03DV (2) at `τ = étale`, and of its transported form
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAssociatedModule`; it is also the
finite-presentation companion of
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`, whose file this one
follows.  All three run over the same localized pullback datum
`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`, and the only thing added here is that
the transported presentation is again *finite*: `SheafOfModules.Presentation.map` changes neither
of the two index types, and `SheafOfModules.Presentation.ofIsIso` changes neither either.

## Main results

* `AlgebraicGeometry.SmallEtale.presentationAssociatedModuleOver_isFinite`: the presentation of
  the restriction of `𝓕^a` to an open of `S` transported from a finite presentation of the
  restriction of `𝓕` is finite.
* **The associated module of a module of finite presentation on the small Zariski site of `S` is
  of finite presentation on the small étale site of `S`**, in the rendering of Stacks 03DL(7) by
  universal properties: this is the base's
  `AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_associatedModule` of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallSiteSheafHomComparison.lean`,
  whose hypothesis is finite presentation on the small Zariski site; Mathlib's rendering of the
  hypothesis is converted to it by
  `SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation`.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_representedAssociatedModule`: **the
  small-étale module on a represented algebraic space attached to a module of finite presentation
  on its scheme is of finite presentation.**

## Implementation notes

The finiteness of the transported presentation is supplied through
`Stacks.SheafOfModules.presentation_isFinite_map` rather than through Mathlib's instance
`SheafOfModules.Presentation.IsFinite.map`, for the reason that restatement exists: instance
search does not find the latter here, and the former takes the finiteness of the given
presentation as a named binder.  The colimit preservation it asks for is that of the *localized*
pullback along `AlgebraicGeometry.SmallEtale.sliceStructureMap`, which is a left adjoint by
`AlgebraicGeometry.SmallEtale.sheafPushforward_sliceStructureMap_isRightAdjoint`.

The index universe of the quasi-coherent datum is the universe of the objects of the site on each
side — `Type u` for the small Zariski site of `S` and `Type (u + 1)` for the small étale site —
and `AlgebraicGeometry.SmallEtale.quasicoherentDataAssociatedModule` already performs that raise,
reusing the given presentations index for index; so no `SheafOfModules.QuasicoherentData.shrink`
is needed and the finiteness transfers one presentation at a time.

The transport to the represented algebraic space is
`Stacks.SheafOfModules.isFinitePresentationOnSite_reindex_iff`, the clause of Stacks 03DM for
Stacks 03DL(7); its dense-subsite instance is
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse`, which is why
`StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent` is imported, exactly as
the quasi-coherent and finite-locally-free companions do.

No `@[stacks]` attribute is placed.  Stacks 03DV (2) is carried by the quasi-coherence statement
and Stacks 03DL(7) by the two renderings of finite presentation; what is proved here is that one
clause of Stacks 03DO survives the associated-module functor, which is not a covering set for
either tag.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module.
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV), its quasi-coherence.
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL), part (7), finite
  presentation of a module on a site.
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM), the local conditions of
  Stacks 03DL are intrinsic.
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO), the local conditions
  under a morphism of ringed sites.
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0), the small étale site of
  a scheme and of the algebraic space it represents.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The transported presentation of the associated module over an open is finite.**  The
localized pullback carries a finite presentation of `𝓕|_V` to one of `(𝓕^a)|_{V_étale}`:
`SheafOfModules.Presentation.map` changes neither of the two index types, and the identification
`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso` is an isomorphism, along which
`SheafOfModules.Presentation.ofIsIso` changes neither either. -/
theorem presentationAssociatedModuleOver_isFinite (V : S.Opens) {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) [P.IsFinite] :
    (presentationAssociatedModuleOver B S hS V P).IsFinite := by
  let : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)) :=
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (sliceStructureMap B S hS V)).leftAdjoint_preservesColimits
  let := Stacks.SheafOfModules.presentation_isFinite_map P
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
    (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))).symm
  exact inferInstanceAs (SheafOfModules.Presentation.IsFinite
    ((P.map (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
        (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
          (sliceStructureMap B S hS V))).symm).ofIsIso
      (associatedModuleOverObjIso B S hS V 𝓕).hom))

/-- **The quasi-coherent datum of the associated module built from a finitely presented one is
finitely presented.**  Every one of its presentations is a transported one, and
`AlgebraicGeometry.SmallEtale.presentationAssociatedModuleOver_isFinite` says those are
finite. -/
theorem quasicoherentDataAssociatedModule_isFinitePresentation {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕)
    [hq : q.IsFinitePresentation] :
    (quasicoherentDataAssociatedModule B S hS q).IsFinitePresentation where
  isFinite_presentation i := by
    let := hq.isFinite_presentation i.down
    exact presentationAssociatedModuleOver_isFinite B S hS (q.X i.down) (q.presentation i.down)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small-étale module attached to a module of finite presentation on a scheme of the big
fppf site is of finite presentation on the small étale site of the algebraic space the scheme
represents.**

The associated module of the scheme's own small étale site is of finite presentation there by
`AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_associatedModule` (its hypothesis read
off `SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation`), and finite
presentation is invariant under the equivalence of that site with the small étale site of the
represented algebraic space, the two structure sheaves being equal; the invariance is
`Stacks.SheafOfModules.isFinitePresentationOnSite_reindex_iff`, the clause of Stacks 03DM for
Stacks 03DL(7).

This is the finite-presentation analogue of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAssociatedModule`. -/
theorem isFinitePresentationOnSite_representedAssociatedModule
    (U : BigFppfOver B S hS) (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hM : SheafOfModules.IsFinitePresentation M) :
    ((representedAssociatedModule B S hS U hU).obj M).IsFinitePresentationOnSite :=
  (Stacks.SheafOfModules.isFinitePresentationOnSite_reindex_iff
    (J' := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M)).2
    (_root_.AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M
      (SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation M (h := hM)))

end AlgebraicGeometry.Space

end
