module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFreeAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of the associated module on a small étale site

Let `S` be a scheme and let `𝓕` be an `𝒪_S`-module which is finite locally free on the small
Zariski site of `S`, in the covering-family form of Stacks 03DL (2). The small-étale module `𝓕^a`
attached to `𝓕` by Stacks 03DU (4) is finite locally free on the small étale site of `S`, and so is
its transport along the equivalence of Stacks 04M0 between the small étale site of a scheme of the
big fppf site and the small étale site of the algebraic space it represents.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteFree_associatedModule_over_opens`: on an open `V` of `S`
  on which `𝓕` is finite free, the restriction of `𝓕^a` to `V` read in the small étale site is
  finite free.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedAssociatedModule`: the
  small-étale module on a represented algebraic space attached to a module finite locally free on
  its scheme is finite locally free.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL), the local conditions on
  a module on a site; clause (2) is finite local freeness.
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM), they are intrinsic to
  the ringed topos.
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO), they are preserved by
  pullback.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module on
  a small site.
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0), the equivalence of small
  étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If an `𝒪_S`-module `𝓕` is finite free on an open `V` of `S`, then its associated module `𝓕^a`
is finite free on `V` read as an object of the small étale site of `S`. -/
public theorem isFiniteFree_associatedModule_over_opens (V : S.Opens) (𝓕 : S.Modules)
    (h : _root_.SheafOfModules.IsFiniteFree (S.ringCatSheaf.over V)
      (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V)) :
    _root_.SheafOfModules.IsFiniteFree
      ((structureSheaf B S hS).over ((opensToSmallEtale B S hS).obj V))
      (((associatedModule B S hS).obj 𝓕).over ((opensToSmallEtale B S hS).obj V)) :=
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)) :=
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (sliceStructureMap B S hS V)).leftAdjoint_preservesColimits
  Stacks.Sheaves.LocalizedPullback.isFiniteFree_map
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
    (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V)))
    (associatedModuleOverObjIso B S hS V 𝓕) h

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small-étale module attached to a finite locally free module on a scheme of the big fppf
site is finite locally free on the small étale site of the algebraic space the scheme
represents. -/
public theorem isFiniteLocallyFreeOnSite_representedAssociatedModule
    (U : BigFppfOver B S hS) (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite
      ((representedAssociatedModule B S hS U hU).obj M) :=
  (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff
    (J' := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M)).2
    (SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M hM)

end AlgebraicGeometry.Space

end
