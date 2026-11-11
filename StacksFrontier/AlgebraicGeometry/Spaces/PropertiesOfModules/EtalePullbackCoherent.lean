module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence is preserved by pullback along an étale morphism of algebraic spaces

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Pullback of `𝒪_Y`-modules along `f` is restriction along postcomposition of
étale charts with `f` (Stacks 03LP, 03LW).  On the slice at an étale chart `V` of `X` that
restriction is the reindexing of the restriction of the module to the slice at the composite
chart, along the slice equivalence of Stacks 04M0, and coherence (Stacks 03DL (8)) is invariant
under that equivalence of sites (the special cocontinuous case of Stacks 03DM) and inherited by
slices.  Since coherence is local on the site (Stacks 03DN), the pullback of a coherent module
along an étale morphism is coherent.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_etaleModulePullback`: the étale restriction of a
  coherent module is coherent.
* `AlgebraicGeometry.Space.isCoherentOnSite_modulePullback_of_isEtale`: the inverse image of
  Stacks 03LU of a coherent module along an étale morphism is coherent.

## References

* [Stacks Project, Tag 05VR](https://stacks.math.columbia.edu/tag/05VR)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The étale restriction of a coherent module is coherent.**  For an étale morphism
`f : X ⟶ Y` of algebraic spaces and a coherent `𝒪_Y`-module `M`, the restriction of `M` along
postcomposition of étale charts with `f` is a coherent `𝒪_X`-module.

On the slice at each étale chart `V` of `X` the restriction is the reindexing of `M` restricted
to the slice at the composite chart, which is coherent by
`Stacks.SheafOfModules.isCoherentOnSite_over`; coherence travels along the slice equivalence by
`Stacks.Sheaves.SpecialCocontinuous.isCoherentOnSite_iff`, and is glued back from all slices by
`AlgebraicGeometry.Space.isCoherentOnSite_of_forall_over`. -/
theorem isCoherentOnSite_etaleModulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsCoherentOnSite) :
    ((etaleModulePullback B S hS f hf).obj M).IsCoherentOnSite := by
  refine isCoherentOnSite_of_forall_over B S hS X.1 X.2 _ fun V ↦ ?_
  have := SmallEtale.isCocontinuous_overPostcomp B S hS f hf V
  have := SmallEtale.isCocontinuous_postcompOverInverse B S hS f hf V
  have := Equivalence.isDenseSubsite_functor_of_isCocontinuous
    ((smallEtaleRingedSite B S hS X.1 X.2).J.over V)
    ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V)
  exact (Stacks.Sheaves.SpecialCocontinuous.isCoherentOnSite_iff
    ((smallEtaleRingedSite B S hS X.1 X.2).J.over V)
    ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).functor
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
    (M.over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))).1
    (Stacks.SheafOfModules.isCoherentOnSite_over M hM _)

/-- **The pullback of a coherent module along an étale morphism is coherent.**  For an étale
morphism `f : X ⟶ Y` of algebraic spaces, the inverse image `f^*M` of Stacks 03LU of a coherent
`𝒪_Y`-module is coherent: it is isomorphic to the étale restriction of `M` (Stacks 03LW), which
is coherent by `AlgebraicGeometry.Space.isCoherentOnSite_etaleModulePullback`. -/
@[stacks 05VR "consequence (2), property 'coherent': for an étale morphism f of algebraic \
spaces, the pullback f^*𝓕 of a coherent module 𝓕 is coherent"]
theorem isCoherentOnSite_modulePullback_of_isEtale (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsCoherentOnSite) :
    ((modulePullback B S hS f).obj M).IsCoherentOnSite :=
  Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).app M).symm
    (isCoherentOnSite_etaleModulePullback B S hS f hf M hM)

end AlgebraicGeometry.Space

end
