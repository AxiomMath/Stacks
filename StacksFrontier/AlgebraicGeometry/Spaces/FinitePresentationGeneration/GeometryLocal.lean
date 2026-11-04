module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartLocalRestrictionIdentification

/-!
# Finite presentation on a slice under étale restriction

For an étale morphism `f : Y ⟶ X` of algebraic spaces and an étale chart `V` of `Y`, the slice of
the small étale site of `Y` at `V` is equivalent to the slice of the small étale site of `X` at
the composite chart (Stacks 04M0, slice form), and this equivalence carries the restriction of
an `𝒪_X`-module `G` to the slice at the composite chart to the restriction of the étale
pullback of `G` to the slice at `V`, on the nose.  Finite presentation is invariant under such a
reindexing (Stacks 03DM for clause 03DL (7)), so the two restrictions are of finite presentation
together.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_over_etaleModulePullback_iff`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Finite presentation on a slice is unchanged by étale restriction.**  For an étale
`f : Y ⟶ X` and an étale chart `V` of `Y`, the restriction of the étale pullback of an
`𝒪_X`-module to the slice at `V` is of finite presentation exactly when the restriction of the
module itself to the slice at the composite chart is. -/
theorem isFinitePresentation_over_etaleModulePullback_iff (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) :
    (G.over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)).IsFinitePresentation ↔
      (((etaleModulePullback B S hS f hf).obj G).over V).IsFinitePresentation := by
  let (U : Over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) :
      HasSheafify (((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)).over U) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let (U : Over V) :
      HasSheafify (((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V).over U) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hF := smallEtaleRingedSite_isContinuous_postcompOverEquivalence_functor B S hS f hf V
  have hG := smallEtaleRingedSite_isContinuous_postcompOverEquivalence_inverse B S hS f hf V
  have := isDenseSubsite_inverse_of_isContinuous _ _
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V) hF hG
  have := isDenseSubsite_inverse_of_isContinuous _ _
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).symm hG hF
  exact Stacks.SheafOfModules.isFinitePresentation_reindex_iff
    (J' := (smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V)
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
    (G.over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))

end AlgebraicGeometry.Space

end
