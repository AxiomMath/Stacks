module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartLocalRestrictionIdentification
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationSiteEquivalence

/-!
# Finite presentation across the chart-scheme identification

The slice at an étale chart `W` of the small étale site of an algebraic space `U` is the small
étale site of the scheme underlying `W`, by
`AlgebraicGeometry.Space.chartSchemeEquivalence` — Stacks 04M0 after Stacks 03ED — and the two
structure sheaves agree on the nose, by
`AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf`.  This file transports finite
presentation of modules across that identification, so that a statement about a module on the
slice at a chart can be read as a statement about a module on a *scheme*, where the results of
Descent, Chapter 35 apply.

The transport itself is `Stacks.SheafOfModules.isFinitePresentation_reindex_iff`, the
finite-presentation clause 03DL (7) of Modules on Sites, Lemma 03DM.  What this file supplies is
the sheafification data that lemma consumes on both sides of the identification:

* on the small étale site of a *scheme*, the slices were not previously known to admit
  sheafification; they do, because a slice of an essentially small category is essentially
  small and `AlgebraicGeometry.SmallEtale.essentiallySmall` makes the site essentially small;
* on the slice at a chart the data is already available, but at the spelling
  `(𝒪_U-site).J.over W` rather than at `((𝒪_U-site).over W).J`, which is the spelling a module
  on the slice carries.  The two topologies are equal by `rfl`, but instance search does not
  unfold `AlgebraicGeometry.Space.smallEtaleRingedSite`, so each datum is restated.

## Main results

* `AlgebraicGeometry.Space.chartSchemeSiteModule`: a module on the slice at a chart, read as a
  module on the small étale site of the scheme underlying the chart.
* `AlgebraicGeometry.Space.isFinitePresentation_chartSchemeModule_iff`: that reading preserves
  and reflects finite presentation.

## Implementation notes

The chart is taken at the spelling `(smallEtaleRingedSite B S hS U.1 U.2).C` rather than at
`AlgebraicGeometry.Space.SmallEtale`, because that is the spelling under which the slice
sheafification instances of
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart` and the module-level
predicates are found.  `AlgebraicGeometry.Space.chartSchemeIdentification` names the
chart-scheme equivalence with its codomain written out at that spelling, which fixes the
category instance on `Over W`
once; writing `AlgebraicGeometry.Space.chartSchemeEquivalence` directly leaves the instance to
be synthesized from a metavariable and it is not found.  For the same reason the instances
restated here are handed to
`Stacks.SheafOfModules.isFinitePresentation_reindex_iff` from the local context rather than left
to instance search, which resolves that lemma's binders before its site arguments are assigned.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T)

/-- A slice of the small étale site of a scheme is essentially small, because a slice of an
essentially small category is. -/
instance schemeSmallEtale_essentiallySmall_over (X : AlgebraicGeometry.SmallEtale E T hT) :
    EssentiallySmall.{u} (Over X) :=
  inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 _) X))

/-- Abelian presheaves on a slice of the small étale site of a scheme have a sheafification. -/
instance schemeSmallEtale_hasSheafify_over (X : AlgebraicGeometry.SmallEtale E T hT) :
    HasSheafify ((AlgebraicGeometry.SmallEtale.topology E T hT).over X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On a slice of the small étale site of a scheme the local equivalences of abelian presheaves
are exactly the locally bijective morphisms. -/
instance schemeSmallEtale_wEqualsLocallyBijective_over (X : AlgebraicGeometry.SmallEtale E T hT) :
    ((AlgebraicGeometry.SmallEtale.topology E T hT).over X).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  .ofEssentiallySmall _

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : AlgebraicSpaces B S hS) (W : (smallEtaleRingedSite B S hS U.1 U.2).C)

/-- **Stacks 04M0 after Stacks 03ED**, `AlgebraicGeometry.Space.chartSchemeEquivalence` with its
codomain written at the spelling the slice of the small étale ringed site carries.  Naming the
codomain fixes the category instance on the slice once, which is what lets the reindexing
results below be applied to it at all. -/
abbrev chartSchemeIdentification : chartSchemeSite B S hS U W ≌ Over W :=
  chartSchemeEquivalence B S hS U W

/-- The functor of the chart-scheme identification is continuous. -/
instance isContinuous_chartSchemeIdentification_functor :
    (chartSchemeIdentification B S hS U W).functor.IsContinuous (chartSchemeTopology B S hS U W)
      ((smallEtaleRingedSite B S hS U.1 U.2).over W).J :=
  isContinuous_chartSchemeEquivalence_functor B S hS U W

/-- The inverse of the chart-scheme identification is continuous. -/
instance isContinuous_chartSchemeIdentification_inverse :
    (chartSchemeIdentification B S hS U W).inverse.IsContinuous
      ((smallEtaleRingedSite B S hS U.1 U.2).over W).J (chartSchemeTopology B S hS U W) :=
  isContinuous_chartSchemeEquivalence_inverse B S hS U W

/-- The inverse of the chart-scheme identification is a dense subsite inclusion: it is an
equivalence of categories continuous in both directions. -/
instance isDenseSubsite_chartSchemeIdentification_inverse :
    (chartSchemeIdentification B S hS U W).inverse.IsDenseSubsite
      ((smallEtaleRingedSite B S hS U.1 U.2).over W).J (chartSchemeTopology B S hS U W) :=
  isDenseSubsite_inverse_of_isContinuous _ _ (chartSchemeIdentification B S hS U W)
    (isContinuous_chartSchemeIdentification_functor B S hS U W)
    (isContinuous_chartSchemeIdentification_inverse B S hS U W)

/-- The functor of the chart-scheme identification is a dense subsite inclusion, being the
inverse of the opposite equivalence. -/
instance isDenseSubsite_chartSchemeIdentification_functor :
    (chartSchemeIdentification B S hS U W).functor.IsDenseSubsite
      (chartSchemeTopology B S hS U W) ((smallEtaleRingedSite B S hS U.1 U.2).over W).J :=
  isDenseSubsite_inverse_of_isContinuous _ _ (chartSchemeIdentification B S hS U W).symm
    (isContinuous_chartSchemeIdentification_inverse B S hS U W)
    (isContinuous_chartSchemeIdentification_functor B S hS U W)

/-- Sheafification on the slice at a chart, at the spelling that reads the slice of the small
étale ringed site as a ringed site in its own right. -/
instance hasWeakSheafify_chartSlice :
    HasWeakSheafify ((smallEtaleRingedSite B S hS U.1 U.2).over W).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify ((smallEtaleRingedSite B S hS U.1 U.2).J.over W)
    AddCommGrpCat.{u})

/-- The agreement of local equivalences with locally bijective morphisms on the slice at a
chart, in the same slice-as-a-ringed-site spelling. -/
instance wEqualsLocallyBijective_chartSlice :
    ((smallEtaleRingedSite B S hS U.1 U.2).over W).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  inferInstanceAs (((smallEtaleRingedSite B S hS U.1 U.2).J.over W).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- The structure sheaf of the small étale site of the scheme underlying an étale chart.  By
`AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf` this is, on the nose, the structure
sheaf of the slice at the chart transported along the chart-scheme identification. -/
abbrev chartSchemeSiteStructureSheaf :=
  _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
    (chartOverObject B S hS U W).left.property

/-- **A module on the slice at an étale chart, read as a module on the small étale site of the
scheme underlying the chart.**  The comparison of coefficients is the identity, because the two
structure sheaves are equal by `AlgebraicGeometry.Space.chartSchemeEquivalence_ringSheaf`. -/
abbrev chartSchemeSiteModule
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS U.1 U.2).over W).O)) :
    SheafOfModules.{u} (chartSchemeSiteStructureSheaf B S hS U W) :=
  (SheafOfModules.pushforward.{u}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS U.1 U.2).over W).O))
    (F := (chartSchemeIdentification B S hS U W).functor) (𝟙 _)).obj M

/-- **Finite presentation transports across the chart-scheme identification.**  A module on the
slice at an étale chart is of finite presentation if and only if the module it becomes on the
small étale site of the scheme underlying that chart is.

This is `Stacks.SheafOfModules.isFinitePresentation_reindex_iff`, the finite-presentation
clause 03DL (7) of Modules on Sites, Lemma 03DM, applied to
`AlgebraicGeometry.Space.chartSchemeIdentification`. -/
theorem isFinitePresentation_chartSchemeModule_iff
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS U.1 U.2).over W).O)) :
    M.IsFinitePresentation ↔ (chartSchemeSiteModule B S hS U W M).IsFinitePresentation := by
  have := hasWeakSheafify_chartSlice B S hS U W
  have := wEqualsLocallyBijective_chartSlice B S hS U W
  have : ∀ X : Over W,
      HasSheafify (((smallEtaleRingedSite B S hS U.1 U.2).over W).J.over X)
        AddCommGrpCat.{u} :=
    inferInstanceAs (∀ X : Over W,
      HasSheafify (((smallEtaleRingedSite B S hS U.1 U.2).J.over W).over X) AddCommGrpCat.{u})
  have : ∀ X : Over W,
      (((smallEtaleRingedSite B S hS U.1 U.2).over W).J.over X).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    inferInstanceAs (∀ X : Over W,
      (((smallEtaleRingedSite B S hS U.1 U.2).J.over W).over X).WEqualsLocallyBijective
        AddCommGrpCat.{u})
  have := isDenseSubsite_chartSchemeIdentification_inverse B S hS U W
  have := isDenseSubsite_chartSchemeIdentification_functor B S hS U W
  have := isContinuous_chartSchemeIdentification_functor B S hS U W
  have := isContinuous_chartSchemeIdentification_inverse B S hS U W
  exact Stacks.SheafOfModules.isFinitePresentation_reindex_iff
    (chartSchemeIdentification B S hS U W) _ M

end AlgebraicGeometry.Space

end
