module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRankOneFreeLocusRank
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreStalkFreeness
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.InvertibleCoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOneEssentiallySmall

/-!
# The Picard stack inside the stack of coherent sheaves with proper support

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
flat, of finite presentation and proper.  Stacks 0D03 says that the natural map
`Pic_{X/B} ⟶ Coh_{X/B}` is representable by open immersions.  The source's proof has two parts.

The first is that the map is well defined: a triple `(T, g, L)` of the Picard stack of Section
0372 is sent to the same triple viewed in Situation 08KB, which works because an invertible
`𝒪_{X_T}`-module is finitely presented, is flat over `T` because `X_T ⟶ T` is flat (Stacks
03MO), and has support proper over `T` because `X_T ⟶ T` is proper (Stacks 04WP).

The second is the content: for an object `(T, g, F)` of `Coh_{X/B}` there is an open
`U ⊆ T` such that a morphism `T' ⟶ T` factors through `U` exactly when the pullback `F_{T'}`
is invertible.  The locus is `U = T ∖ f_T(|X_T| ∖ W₁)` with `W₁ ⊆ |X_T|` the set of points at
which `F` is free of rank one in an étale neighbourhood — the locus of Stacks 0CZT with the rank
pinned to one, which performs the source's two reductions at once.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.toPicardSituation`: the Picard situation of
  Stacks 0D25 underlying a coherent situation of Stacks 08KB.
* `AlgebraicGeometry.Space.picardObjectToCoherent`: **Stacks 0D03, the natural map on
  objects** — the first part of the source's proof.
* `AlgebraicGeometry.Space.fibrewiseLocus`: the shape `T ∖ f_T(|X_T| ∖ W)` of the locus `U` of
  the second part of the source's proof, with the subset `W ⊆ |X_T|` left free.
* `AlgebraicGeometry.Space.fibrewiseEtaleRankOneFreeLocus`: **Stacks 0D03, the locus `U`** of the
  second part of the source's proof — that shape at the *rank-one* étale free locus, which is
  the source's own `U`.
* `AlgebraicGeometry.Space.fibrewiseEtaleFreeLocus`: the same shape at the locus of Stacks 0CZT,
  that is, the first of the source's two reductions only.
* `AlgebraicGeometry.Space.chartSmallEtaleRestrictionFunctor`: restriction of `𝒪_Z`-modules to
  the slice of the small étale site at an étale scheme chart, read on the small étale site of
  the algebraic space the chart represents, as a functor — which is the form in which a
  trivialization of a module transports.

## Main results

* `AlgebraicGeometry.Space.isFlat_projection` and
  `AlgebraicGeometry.Space.isProper_projection`: the projection `X_T ⟶ T` of a base change is
  flat, respectively proper, when `f` is.  These are Stacks 03MO and Stacks 04WP applied to the
  cartesian square defining `X_T`, and they are the two citations the source's first part makes.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_projection`: the projection is a closed map on
  points when `f` is proper.
* `AlgebraicGeometry.Space.picardObjectToCoherent`: **Stacks 0D03, part one.**
* `AlgebraicGeometry.Space.mem_fibrewiseLocus_iff` and
  `AlgebraicGeometry.Space.isOpen_fibrewiseLocus`: the description of `T ∖ f_T(|X_T| ∖ W)` by
  fibres, and its openness for an open `W`, both for an arbitrary subset `W ⊆ |X_T|`.
* `AlgebraicGeometry.Space.isOpen_fibrewiseEtaleRankOneFreeLocus`: **Stacks 0D03, the
  construction of the source's `U` and its openness** — unconditionally, and with no
  decomposition of `X_T` by rank.
* `AlgebraicGeometry.Space.mem_fibrewiseEtaleFreeLocus_iff` and
  `AlgebraicGeometry.Space.isOpen_fibrewiseEtaleFreeLocus`: the same for the locus of
  Stacks 0CZT, the first of the source's two reductions.
* `AlgebraicGeometry.Space.range_pointsMap_relativeMap_subset_etaleRankOneFreeLocus` and
  `AlgebraicGeometry.Space.range_pointsMap_relativeMap_subset_etaleFreeLocus`: **Stacks 0D03,
  the implication (a) ⟹ (b) on points** — unconditional, at the source's `U` and at the locus of
  Stacks 0CZT respectively.
* `AlgebraicGeometry.Space.mem_etaleRankOneFreeLocus_of_isInvertibleModule`: an invertible
  `𝒪_Z`-module is free of **rank one** in an étale neighbourhood of every point of `|Z|` —
  unconditional.
* `AlgebraicGeometry.Space.range_pointsMap_relativeMap_subset_etaleFreeLocus_of_forall_mem`:
  **Stacks 0D03, the implication (b) ⟹ (a) on points** — unconditional, from the base-change
  clause of Stacks 0CZT.
* `AlgebraicGeometry.Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`: **Stacks 0B8Q
  at the small étale ringed site of an algebraic space** — an `𝒪_Z`-module is invertible exactly
  when it is finite locally free of rank one.  Both directions, unconditionally.
* `AlgebraicGeometry.Space.mem_etaleFreeLocus_of_isInvertibleModule`: an invertible
  `𝒪_Z`-module is free in an étale neighbourhood of every point of `|Z|` — unconditional.
* `Space.range_pointsMap_relativeMap_subset_etaleFreeLocus_of_isInvertibleModule`:
  **Stacks 0D03, the implication (b) ⟹ (a) on points with (b) at the source's own condition**,
  that `F_{T'}` be invertible — unconditional.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_projection`: the projection `X_T ⟶ T` is
  locally of finite presentation, which is the hypothesis the base-change clause of Stacks 0CZT
  takes at the instance of that tag which applies here.
* `Space.isInvertibleModule_modulePullback_relativeMap_of_subset_fibrewiseEtaleRankOneFreeLocus`:
  **Stacks 0D03, the implication (a) ⟹ (b) complete** — at the source's own `U` and the source's
  own condition (b), that `F_{T'}` be invertible, unconditionally.

## Implementation notes

**The projections of base changes are the unconditional geometric content here.**  The square
defining `X_T = X ×_Y T` is cartesian with `f` opposite the projection `X_T ⟶ T`
(`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_fiberProduct`), so Stacks 03MO
(`AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`, carried whole) and Stacks 04WP
(`AlgebraicGeometry.Space.isProper_isStableUnderBaseChange`, carried whole) apply to it
directly.  Properness of the projection gives both the locally-finite-type hypothesis which
Stacks 0CZD asks for and the closedness on points which makes the locus `U` open.

**All three conditions of Situation 08KB are proved for an invertible module.**
`Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible` supplies finite presentation,
and quasi-coherence follows from
`SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`.  Flatness over the base is
`AlgebraicGeometry.Space.isFlatOver_of_isInvertibleModule`: flatness over the base is read at
geometric points, and there it factors through the source itself, the geometric stalk of an
invertible module being free of rank one by
`AlgebraicGeometry.Space.nonempty_linearEquiv_geometricModuleStalk_of_isInvertibleModule`.
Properness of the support is
`AlgebraicGeometry.Space.isProperOver_supportOfSheaf_of_isInvertibleModule`: the support is
closed by Stacks 07TZ and *any* closed subset is proper over the base along a proper morphism, by
`AlgebraicGeometry.Space.isProperOver_of_isProper` of
`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/DerivedExistenceHypotheses.lean`.  Each is
applied to the projection `X_T ⟶ T`, which Stacks 03MO and Stacks 04WP make flat, respectively
proper, so the base-change citations the source makes are performed too.

**The base-change clause of Stacks 0CZT is proved, and both implications below are therefore
unconditional.**  The clause is
`AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusBaseChange.lean`, registered on Stacks 0CZT
with a which-part note; together with
`AlgebraicGeometry.Space.isOpen_etaleFreeLocus` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocus.lean`, attributed to openness, the two
cover the whole tag.  The two implications below bind no hypothesis standing in for the
clause.

Of the two inclusions making up the base-change equality, the one needed for the step of
(a) ⟹ (b) that is proved here is not needed at all: a point of `|X_{T'}|` maps to a point of
`|X_T|` lying over a point of `U`, and membership of that image point in the locus is what
`AlgebraicGeometry.Space.mem_fibrewiseLocus_iff` already says.  The implication (b) ⟹ (a) needs
the hard inclusion `W(F_{T'}) ⊆ |X_g|⁻¹(W(F))`, which is the half of the clause that clause (4)
of Stacks 0CZS is for.  The *opposite*, easy inclusion is what the last step of (a) ⟹ (b) needs;
it holds for an arbitrary morphism with no hypothesis
(`AlgebraicGeometry.Space.preimage_etaleRankOneFreeLocus_subset` at rank one and
`AlgebraicGeometry.Space.preimage_etaleFreeLocus_subset` at an arbitrary rank).

**What the hard inclusion needs, and what it does not.**  The source transports
clause (1) of Stacks 0CZS, flatness of the geometric fibre stalk, across the base change.  Three
inputs are needed, and all three are available:

* the base-change invariance of clause (1) —
  `AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_modulePullback_iff` of
  `StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkBaseChange.lean`.  **It does not need
  condition (2) of Stacks 05WY**:
  it follows at the étale local rings from the cartesian input of Stacks 05VW, because dividing
  by the maximal ideal of the base turns that comparison into a base change along a homomorphism
  out of a field, so the fibre local ring upstairs is *faithfully flat* over the one downstairs
  even though the étale local rings themselves are not.  Condition (2) of Stacks 05WY is still
  neither stated nor proved, and Stacks 05WY is still registered on `(1) ⟺ (3)` only; that is
  now a gap in the registration of Stacks 05WY alone;
* clause (1) `⟺` clause (4) of Stacks 0CZS —
  `AlgebraicGeometry.Space.exists_chartOpen_over_iso_free_iff_flat_geometricFibreModuleStalk`
  of `StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkFreeness.lean`, attributed
  `0CZS "(1) iff (4)"`;
* the comparison of clause (4)'s Zariski reading of freeness with the locus's small-étale
  reading.  At the *image* point this is what the last hop of the assembly performs, through
  `AlgebraicGeometry.Space.chartOpenNeighborhood` and Stacks 03DX (2) for outright freeness; at
  the point of `|X_{T'}|` the comparison is **not used at all**, and that is what made the
  assembly possible.  Instead the geometric stalk is read directly:
  `AlgebraicGeometry.Space.free_geometricModuleStalk_of_isFreeModule` of
  `StacksFrontier/AlgebraicGeometry/Spaces/GeometricModuleStalkFree.lean` makes the geometric stalk
  of a module free on the small étale site free over the étale local ring at an *arbitrary* index
  type, and
  `AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_comp_modulePullback_iff` of
  `StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkEtaleLocal.lean` moves clause (1) from
  the étale neighbourhood down to `X_{T'}`.  So the refinement of an arbitrary small étale
  neighbourhood of algebraic spaces by a Zariski open of a scheme chart, which the attribute on
  clause (4) records as not claimed, is still unlanded and is not needed here.

## References

* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The Picard situation of a coherent situation -/

/-- The Picard situation of Stacks 0D25 underlying a coherent situation of Stacks 08KB: the same
morphism `f : X ⟶ Y` of algebraic spaces, with the finite-presentation hypothesis forgotten.

The test schemes and the base changes of the two situations are the same, so an object of the
Picard stack of Section 0372 for this situation carries a test scheme over `Y` and an invertible
module on the base change `X_T` of the coherent situation. -/
def CoherentSituation.toPicardSituation (D : CoherentSituation B S hS) :
    PicardSituation B S hS where
  X := D.X
  base := D.Y
  f := D.f

/-! ### The projection of a base change -/

/-- **The projection `X_T ⟶ T` of a base change is flat when `f` is.**  This is Stacks 03MO
applied to the cartesian square defining `X_T = X ×_Y T`, in which `f` is the morphism opposite
the projection; it is the flatness citation of the first part of the proof of Stacks 0D03. -/
theorem isFlat_projection (D : CoherentSituation B S hS) (hf : IsFlat B S hS D.f.hom)
    (T : SchemesOver D.Y) : IsFlat B S hS (D.projection T).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) hf

/-- **The projection `X_T ⟶ T` of a base change is proper when `f` is.**  This is Stacks 04WP
applied to the same cartesian square; it is the properness citation of the first part of the
proof of Stacks 0D03. -/
theorem isProper_projection (D : CoherentSituation B S hS) (hf : IsProper B S hS D.f.hom)
    (T : SchemesOver D.Y) : IsProper B S hS (D.projection T).hom :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) hf

/-- **The projection `X_T ⟶ T` of a base change is locally of finite type.**  This needs no
hypothesis beyond the situation: `f` is of finite presentation by the standing data of
Stacks 08KB, hence locally of finite type, and being locally of finite type is stable under the
base change that defines `X_T` (Stacks 03XH).  This is the hypothesis that properness over the
test scheme in the sense of Stacks 0CZD takes. -/
theorem isLocallyOfFiniteType_projection (D : CoherentSituation B S hS) (T : SchemesOver D.Y) :
    IsLocallyOfFiniteType B S hS (D.projection T).hom :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom)
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS D.finitePresentation.1)

/-- **The projection `X_T ⟶ T` of a base change is locally of finite presentation.**  This needs
no hypothesis beyond the situation: `f` is of finite presentation by the standing data of
Stacks 08KB, hence locally of finite presentation, and that is stable under the base change which
defines `X_T` (Stacks 03XR).  It is the hypothesis the base-change clause of Stacks 0CZT takes at
the instance of that tag which applies here, namely the tag at the projection `X_T ⟶ T`. -/
theorem isLocallyOfFinitePresentation_projection (D : CoherentSituation B S hS)
    (T : SchemesOver D.Y) :
    IsLocallyOfFinitePresentation B S hS (D.projection T).hom :=
  (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.finitePresentation.1

/-- **The projection `X_T ⟶ T` of a base change is a closed map on points when `f` is proper.**
Properness of the projection, which Stacks 04WP supplies, contains universal closedness; its
instance at the identity of the target identifies the base change with the projection itself. -/
theorem isClosedMap_pointsMap_projection (D : CoherentSituation B S hS)
    (hf : IsProper B S hS D.f.hom) (T : SchemesOver D.Y) :
    IsClosedMap (pointsMap B S hS (D.space T).1 (D.projection T).hom) :=
  isClosedMap_pointsMap_of_pullback_fst_id B S hS _
    ((isProper_projection D hf T).2.2 _ ((schemeSpaceFunctor B S hS).obj T.left).2 (𝟙 _))

/-! ### Invertible modules are finitely presented -/

/-- **An invertible module on an algebraic space is of finite presentation on its small étale
site.**  This is the first of the three conditions Situation 08KB imposes, and it is the
assertion "an invertible `𝒪_{X_T}`-module `L` is finitely presented" of the first part of the
proof of Stacks 0D03.  It is
`Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible`, Stacks 0B8N (b) read on an
arbitrary site, at the structure sheaf of the algebraic space. -/
theorem isFinitePresentationOnSite_of_isInvertibleModule {Z : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L) :
    L.IsFinitePresentationOnSite :=
  Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L hL

/-! ### Invertible modules are étale-locally free of rank one -/

/-- **Stacks 0B8Q at the small étale ringed site of an algebraic space.**  An `𝒪_Z`-module on an
algebraic space `Z` is invertible exactly when it is finite locally free of rank one in the
sense of the rank clause of Stacks 0409: over a covering family of every object of the small
étale site of `Z` it is a coproduct of one copy of the structure sheaf.

Local ringedness of the site, which the converse clause of Stacks 0B8Q asks for, is Stacks 04KH
(`AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`).

Neither carrier of Stacks 0B8Q stated for a bare ringed site applies here:
`AlgebraicGeometry.RingedSite.isInvertible_iff_isFiniteLocallyFreeOfRank_one` is stated at
`RingedSite.{u, max u v, max u v}` and
`AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one` at
`RingedSite.{u, v, max u v w}`, so both put the universe of the module sections at or above the
universe of the objects of the site, whereas the small étale site of an algebraic space has its
objects in `Type (u + 1)` and the sections of its structure sheaf in `Type u`.  The two
universe-flexible forms of the same two clauses do apply:
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'`, whose only
hypotheses beyond local ringedness are sheafification and the characterization of local
equivalences, and
`AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall`,
which asks in addition for a small model of the site.  All three instances are available for the
small étale site of an algebraic space. -/
theorem isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one {Z : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS Z.1 Z.2) :
    IsInvertibleModule Z L ↔
      RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) L 1 := by
  constructor
  · intro hL
    have : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS Z.1 Z.2).O.obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Z.1 Z.2).O)).property L := hL
    exact RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'
      (smallEtaleRingedSite B S hS Z.1 Z.2) L
      (smallEtaleRingedSite_isLocallyRinged B S hS Z.1 Z.2)
  · have := Space.smallEtaleRingedSite_essentiallySmall B S hS Z.1 Z.2
    exact RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall
      (smallEtaleRingedSite B S hS Z.1 Z.2) L

/-! ### From rank one on the site to the étale free locus -/

/-- Restriction of `𝒪_Z`-modules to the slice of the small étale site at an étale scheme chart
`W`, read as modules on the small étale site of the algebraic space represented by `W`, as a
*functor*.

Its action on objects is `AlgebraicGeometry.Space.chartSmallEtaleRestriction`, which is defined
as this pushforward applied to `L.over W`; the functor itself is needed because a trivialization
of `L` on the slice has to be transported, and only a functor transports an isomorphism.  The
map of sheaves of rings it pushes forward along is the identity, the two structure sheaves of
Stacks 04M0 being equal by
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`. -/
def chartSmallEtaleRestrictionFunctor (Z : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS Z.1) :
    SheafOfModules.{u} ((structureRingSheaf B S hS Z).over W) ⥤
      SheafOfModules.{u} (chartStructureRingSheaf B S hS Z W) :=
  @SheafOfModules.pushforward _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS Z W).1)
    ((SmallEtale.topology B S hS Z.1).over W)
    (SmallEtale.chartLocalizationEquivalence B S hS Z.1 W).functor
    (chartStructureRingSheaf B S hS Z W)
    ((structureRingSheaf B S hS Z).over W)
    (isContinuous_chartLocalization_chartSpace B S hS Z W)
    (𝟙 _)

/-- **Restriction to the slice at a chart is pullback to the chart space.**  The restriction of
an `𝒪_Z`-module to the slice of the small étale site at an étale scheme chart `W`, read through
the comparison equivalence of Stacks 04M0, is the étale restriction of Equation 03LW along the
structure morphism of `W`.

The identification is definitional, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSpaceGlobalPresentation.lean` record: the comparison
functor followed by the slice projection is postcomposition with the structure morphism of the
chart, and no change of scalars occurs on either leg. -/
def chartSmallEtaleRestrictionFunctorObjIso (Z : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (W : SmallEtale B S hS Z.1) :
    (chartSmallEtaleRestrictionFunctor Z W).obj (L.over W) ≅
      (etaleModulePullback B S hS (chartToSpace B S hS Z W)
        (isEtale_chartToSpace B S hS Z W)).obj L :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))

/-- The structure sheaf of the slice at an étale scheme chart restricts to the structure sheaf
of the chart space.  This is the unit module of
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionFunctorObjIso`, and it holds for the same
reason: the two structure sheaves of Stacks 04M0 agree, so the restriction changes no
sections. -/
def chartSmallEtaleRestrictionFunctorUnitIso (Z : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS Z.1) :
    (chartSmallEtaleRestrictionFunctor Z W).obj
        (SheafOfModules.unit ((structureRingSheaf B S hS Z).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (chartSpace B S hS Z W).1 (chartSpace B S hS Z W).2).O)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext; rfl))

/-- A presentation of a sheaf of modules as a coproduct of *one* copy of the unit module is an
isomorphism with the unit module: the cofan of a single identity of the unit module is a
colimit, and two colimits of the same shape agree.

This is the local form of `locallyFreeRankOneIso`, which
`StacksFrontier/CategoryTheory/Sites/Modules/InvertibleRankOne.lean` keeps private.

The colimit datum is taken as an argument rather than as a `Nonempty`, so that this
definition has a real body: extracting the colimit from a bare existence statement would
make the isomorphism depend on an arbitrary choice of witness.  A caller holding only
`Nonempty (IsColimit _)` is inside a proof, where destructing it is harmless. -/
def unitCofanIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R)
    (ι : ∀ _ : Fin 1, SheafOfModules.unit R ⟶ M)
    (hι : IsColimit (Cofan.mk M ι)) : M ≅ SheafOfModules.unit R := by
  have hc : IsColimit (Cofan.mk (SheafOfModules.unit R)
      (fun _ : Fin 1 => 𝟙 (SheafOfModules.unit R))) := by
    refine Cofan.IsColimit.mk _ (fun s => s.inj 0) ?_ ?_
    · intro s j
      fin_cases j
      simp
    · intro s m hm
      simpa using hm 0
  exact hι.coconePointUniqueUpToIso hc

/-- A module isomorphic to the structure sheaf is free: a one-element cofan whose single leg is
an isomorphism is a coproduct diagram.  Freeness here is
`AlgebraicGeometry.Space.IsFreeModule`, the universal-property reading of Stacks 0CZT's
"free". -/
theorem isFreeModule_of_iso_unit (V : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS V.1 V.2)
    (e : M ≅ SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O))) :
    IsFreeModule B S hS V M := by
  refine ⟨PUnit.{u + 1}, fun _ => e.inv, ⟨Cofan.IsColimit.mk _
    (fun s => e.hom ≫ s.inj PUnit.unit) ?_ ?_⟩⟩
  · intro s j
    obtain ⟨⟩ := j
    exact e.inv_hom_id_assoc _
  · intro s m hm
    have h0 : e.inv ≫ m = s.inj PUnit.unit := hm PUnit.unit
    rw [← h0, Iso.hom_inv_id_assoc]

/-- The rank-one free locus is contained in the free locus: a module isomorphic to the structure
sheaf is free. -/
theorem etaleRankOneFreeLocus_subset_etaleFreeLocus {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) :
    etaleRankOneFreeLocus B S hS F ⊆ etaleFreeLocus B S hS F := by
  rintro x ⟨V, a, hae, hxr, ⟨e⟩⟩
  exact ⟨V, a, hae, hxr, isFreeModule_of_iso_unit V _ e⟩

/-- **A trivialization on an étale chart puts the points of that chart in the rank-one étale
free locus.**  If an `𝒪_Z`-module `L` becomes isomorphic to the structure sheaf on the slice of
the small étale site at an étale scheme chart `W`, then every point of `|Z|` in the image of
`|W|` is a point at which `L` is free of rank one in an étale neighbourhood.

The étale neighbourhood is the algebraic space represented by `W` together with its structure
morphism, which is étale by Stacks 03G1
(`AlgebraicGeometry.Space.isEtale_chartToSpace`); the pullback of `L` along it is the
restriction to the slice by Stacks 04M0 and Equation 03LW
(`AlgebraicGeometry.Space.chartSmallEtaleRestrictionFunctorObjIso` and
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`), so the trivialization
transports to an isomorphism of that pullback with the structure sheaf of the chart space. -/
theorem mem_etaleRankOneFreeLocus_of_over_iso_unit (Z : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (W : SmallEtale B S hS Z.1)
    (e : L.over W ≅ SheafOfModules.unit ((structureRingSheaf B S hS Z).over W))
    (x : points B S hS Z.1)
    (hx : x ∈ Set.range (pointsMap B S hS (chartSpace B S hS Z W).1
      (chartToSpace B S hS Z W).hom)) :
    x ∈ etaleRankOneFreeLocus B S hS L :=
  ⟨chartSpace B S hS Z W, chartToSpace B S hS Z W, isEtale_chartToSpace B S hS Z W, hx,
    ⟨(modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Z W)
          (isEtale_chartToSpace B S hS Z W)).app L ≪≫
        (chartSmallEtaleRestrictionFunctorObjIso Z L W).symm ≪≫
        (chartSmallEtaleRestrictionFunctor Z W).mapIso e ≪≫
        chartSmallEtaleRestrictionFunctorUnitIso Z W⟩⟩

/-- **A trivialization on an étale chart puts the points of that chart in the étale free
locus.**  This is
`AlgebraicGeometry.Space.mem_etaleRankOneFreeLocus_of_over_iso_unit` followed by the inclusion
of the rank-one locus in the locus of Stacks 0CZT. -/
theorem mem_etaleFreeLocus_of_over_iso_unit (Z : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (W : SmallEtale B S hS Z.1)
    (e : L.over W ≅ SheafOfModules.unit ((structureRingSheaf B S hS Z).over W))
    (x : points B S hS Z.1)
    (hx : x ∈ Set.range (pointsMap B S hS (chartSpace B S hS Z W).1
      (chartToSpace B S hS Z W).hom)) :
    x ∈ etaleFreeLocus B S hS L :=
  etaleRankOneFreeLocus_subset_etaleFreeLocus L
    (mem_etaleRankOneFreeLocus_of_over_iso_unit Z L W e x hx)

/-- **An invertible module on an algebraic space is free of rank one in an étale neighbourhood
of every point**, that is, its rank-one étale free locus is all of `|Z|`.

This is the step the source's condition (b) is used through, and it is unconditional.  An
invertible module is finite locally free of rank one by Stacks 0B8Q
(`AlgebraicGeometry.Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`), so over an
étale chart containing the given point — one exists by Stacks 03H5
(`AlgebraicGeometry.Space.exists_chart_point`) — there is a covering family trivializing it.
That family is jointly surjective on points
(`AlgebraicGeometry.Space.SmallEtale.exists_mem_arrows_pointsMap_eq`), so the point lifts into a
member of the sieve it generates, hence into one of the trivializing charts, and
`AlgebraicGeometry.Space.mem_etaleRankOneFreeLocus_of_over_iso_unit` applies to that chart.

The rank is one throughout, which is what the second part of the proof of Stacks 0D03 needs: the
locus of Stacks 0CZT records freeness of some rank, and the condition to be recognized there is
invertibility. -/
theorem mem_etaleRankOneFreeLocus_of_isInvertibleModule (Z : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L)
    (x : points B S hS Z.1) :
    x ∈ etaleRankOneFreeLocus B S hS L := by
  obtain ⟨U, p, hp⟩ := exists_chart_point B S hS Z.1 Z.2 x
  obtain ⟨I, V, f, hcov, hfree⟩ :=
    (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L).1 hL U
  obtain ⟨W, g, hg, q, hq⟩ := SmallEtale.exists_mem_arrows_pointsMap_eq B S hS Z.1 hcov p
  obtain ⟨i, h, -⟩ := Sieve.ofArrows.exists hg
  obtain ⟨ι, ⟨hιc⟩⟩ := hfree i
  refine mem_etaleRankOneFreeLocus_of_over_iso_unit Z L (V i) (unitCofanIso _ ι hιc) x
    ⟨pointsMap B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS Z.1).obj W)) (yoneda.map h.hom.left) q, ?_⟩
  have hW : yoneda.map ((SmallEtale.toOver B S hS Z.1).map g) ≫ U.obj.hom = W.obj.hom :=
    CostructuredArrow.w g.hom
  have hVi : yoneda.map h.hom.left ≫ (V i).obj.hom = W.obj.hom :=
    CostructuredArrow.w h.hom
  have hres := pointsMap_apply_comm B S hS (hW.trans hVi.symm) q
  rw [hq] at hres
  exact hres.symm.trans hp

/-- **An invertible module on an algebraic space is free in an étale neighbourhood of every
point**, that is, its étale free locus of Stacks 0CZT is all of `|Z|`.  This is
`AlgebraicGeometry.Space.mem_etaleRankOneFreeLocus_of_isInvertibleModule` followed by the
inclusion of the rank-one locus in the locus of Stacks 0CZT. -/
theorem mem_etaleFreeLocus_of_isInvertibleModule (Z : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L)
    (x : points B S hS Z.1) :
    x ∈ etaleFreeLocus B S hS L :=
  etaleRankOneFreeLocus_subset_etaleFreeLocus L
    (mem_etaleRankOneFreeLocus_of_isInvertibleModule Z L hL x)

/-! ### Invertible modules are flat over the base, with proper support -/

/-- **An invertible module is flat over the base along a flat morphism.**  For a flat morphism
`p : Z ⟶ W` of algebraic spaces and an invertible `𝒪_Z`-module `L`, the module `L` is flat over
`W` in the sense of Stacks 05VV.

This is the flatness half of the first part of the proof of Stacks 0D03.  Flatness over the base
is read at geometric points, which needs the quasi-coherence that invertibility supplies, and
there it factors through `Z` itself by Stacks 05VX (1): the geometric stalk of an invertible
module is free of rank one over the étale local ring, hence flat, and the étale local ring of
`W` is flat under it because `p` is flat. -/
theorem isFlatOver_of_isInvertibleModule {Z W : AlgebraicSpaces B S hS} (p : Z ⟶ W)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hp : IsFlat B S hS p.hom)
    (hL : IsInvertibleModule Z L) :
    IsFlatOver B S hS Z.2 p.hom L := by
  have : L.IsFinitePresentationOnSite := isFinitePresentationOnSite_of_isInvertibleModule L hL
  have : L.IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite L
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS p L]
  intro xbar
  have hid : IsFlatOverAtGeometricPoint B S hS (𝟙 Z) L xbar := by
    rw [isFlatOverAtGeometricPoint_id_iff B S hS L xbar]
    obtain ⟨e⟩ :=
      nonempty_linearEquiv_geometricModuleStalk_of_isInvertibleModule B S hS Z xbar L hL
    exact Module.Flat.of_linearEquiv e
  have h := isFlatOverAtGeometricPoint_comp B S hS (𝟙 Z) p L xbar hid
    (isFlatAt_of_isFlat B S hS p.hom hp _)
  rwa [Category.id_comp] at h

/-- **The support of an invertible module is closed.**  An invertible `𝒪_Z`-module is of finite
presentation on the small étale site, hence of finite type, and the support of a module of
finite type is closed (Stacks 07TZ). -/
theorem isClosed_supportOfSheaf_of_isInvertibleModule {Z : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L) :
    IsClosed (supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj L)) :=
  have : L.IsFinitePresentationOnSite := isFinitePresentationOnSite_of_isInvertibleModule L hL
  isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS Z.1 Z.2 L

/-- **The support of an invertible module is proper over the base along a proper morphism.**
For a proper morphism `p : Z ⟶ W` of algebraic spaces and an invertible `𝒪_Z`-module `L`, the
support of `L` is a closed subset of `|Z|` proper over `W` in the sense of Stacks 0CZD.

This is the proper-support half of the first part of the proof of Stacks 0D03.  The source
argues that the support is all of `|Z|`, which is proper over `W` when `p` is; that detour is
unnecessary, because properness over the base of *any* closed subset follows from properness of
the morphism — the inclusion of the reduced induced closed subspace is proper, and a composite
of proper morphisms is proper (Stacks 04XY). -/
theorem isProperOver_supportOfSheaf_of_isInvertibleModule {Z W : AlgebraicSpaces B S hS}
    (p : Z ⟶ W) (hp : IsLocallyOfFiniteType B S hS p.hom)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hproper : IsProper B S hS p.hom)
    (hL : IsInvertibleModule Z L) :
    ∃ hU : IsClosed (supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj L)),
      IsProperOver B S hS Z.2 W.2 p.hom hp
        (supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj L)) hU :=
  ⟨isClosed_supportOfSheaf_of_isInvertibleModule L hL,
    isProperOver_of_isProper B S hS Z.2 W.2 p.hom hp hproper _ _⟩

/-! ### The superseded declared hypotheses

The three `Prop`s below stood for inputs that are now theorems, and nothing in this file uses
them any more: the flatness and proper-support halves of the first part of the proof are
`AlgebraicGeometry.Space.isFlatOver_of_isInvertibleModule` and
`AlgebraicGeometry.Space.isProperOver_supportOfSheaf_of_isInvertibleModule`, and the base-change
clause of Stacks 0CZT is `AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq`.  They are
kept, with their original statements, only because other code may name them; their notes below
describe the state of the library when they were written. -/

/-- **The flatness half of the first part of the proof of Stacks 0D03**, as a declared
hypothesis: an invertible module on an algebraic space `Z` is flat over `W` along a flat
morphism `p : Z ⟶ W`, flatness of a module over a base being Stacks 05VV.

The source obtains this from flatness of `p` together with the local freeness of an invertible
module, which is the converse clause of Stacks 0B8Q.  Nothing in this development relates
`AlgebraicGeometry.Space.IsFlatOver` of a module to `AlgebraicGeometry.Space.IsFlat` of the
morphism: the former is a condition on the restrictions of the module to étale scheme charts and
the latter a condition on the induced morphisms of charts, and no comparison of the two is
proved anywhere.  The flat morphism this hypothesis is applied to below is the one Stacks 03MO
produces, so what is assumed is only the module-theoretic half of the source's step. -/
def InvertibleIsFlatOver (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {Z W : AlgebraicSpaces B S hS} (p : Z ⟶ W) (L : Modules.{u, u} B S hS Z.1 Z.2),
    IsFlat B S hS p.hom → IsInvertibleModule Z L → IsFlatOver B S hS Z.2 p.hom L

/-- **The proper-support half of the first part of the proof of Stacks 0D03**, as a declared
hypothesis: the support of an invertible module on an algebraic space `Z` is a closed subset of
`|Z|` which is proper over `W` in the sense of Stacks 0CZD, along a proper morphism
`p : Z ⟶ W`.

The source's argument is that the support of an invertible module is all of `|Z|`, which is
closed, and that all of `|Z|` is proper over `W` when `p` is.  Neither step is available: no
result computes `AlgebraicGeometry.Space.supportOfSheaf` of an invertible module, and no result
produces `AlgebraicGeometry.Space.IsProperOver` of a closed subset from
`AlgebraicGeometry.Space.IsProper` of the morphism — properness over the base is properness of
the reduced induced closed subspace, and the identification of that subspace at the whole of
`|Z|` with `Z` is not proved.  The proper morphism this hypothesis is applied to below is the one
Stacks 04WP produces, and the locally-finite-type hypothesis is the one that properness supplies,
so again only the module-theoretic half of the source's step is assumed. -/
def InvertibleHasProperSupport (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ {Z W : AlgebraicSpaces B S hS} (p : Z ⟶ W) (hp : IsLocallyOfFiniteType B S hS p.hom)
    (L : Modules.{u, u} B S hS Z.1 Z.2), IsProper B S hS p.hom → IsInvertibleModule Z L →
      ∃ hU : IsClosed (supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj L)),
        IsProperOver B S hS Z.2 W.2 p.hom hp
          (supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj L)) hU

/-- **The base-change clause of Stacks 0CZT**, as a declared hypothesis, in the one inclusion
that is not reachable: for a morphism `g : T' ⟶ T` of test schemes over `Y`, a point of
`|X_{T'}|` at which the pullback of `F` along `X_g : X_{T'} ⟶ X_T` is free in an étale
neighbourhood lies above a point of `|X_T|` at which `F` is free in an étale neighbourhood.

Stacks 0CZT asserts that formation of the étale free locus commutes with arbitrary base change,
that is, `W(F_{T'}) = |X_g|⁻¹(W(F))`; this is the inclusion from left to right.  It is not proved
in this development.  The carrier of Stacks 0CZT is
`AlgebraicGeometry.Space.isOpen_etaleFreeLocus`, attributed `0CZT "openness"`, and the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocus.lean` record why the
base-change clause is not: the source derives it from clause (4) of Stacks 0CZS, which identifies
membership in the locus with flatness of the geometric fibre stalk, transported across a base
change by Stacks 05WY, and
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkFreeness.lean` states clauses (1) and
(2) of Stacks 0CZS only, recording in its own notes the five further inputs the implication
(1) ⟹ (4) needs.  Only the opposite inclusion is reachable without clause (4). -/
def EtaleFreeLocusBaseChange (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T' T : SchemesOver Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2),
    etaleFreeLocus B S hS ((modulePullback B S hS (baseChangeMap f g)).obj F) ⊆
      pointsMap B S hS (baseChangeSpace f T').1 (baseChangeMap f g).hom ⁻¹'
        etaleFreeLocus B S hS F

/-! ### Part one: the natural map is well defined -/

/-- **Stacks 0D03, the first part of the proof: the natural map `Pic_{X/B} ⟶ Coh_{X/B}` on
objects.**  A triple `(T, g, L)` of the Picard stack of Section 0372 is sent to the same triple
`(T, g, L)` viewed in Situation 08KB.

The three conditions of Situation 08KB hold for an invertible `L` for the reasons the source
gives, and all three are proved.  Finite presentation is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_of_isInvertibleModule` and quasi-coherence
follows from it.  Flatness over `T` is
`AlgebraicGeometry.Space.isFlatOver_of_isInvertibleModule` applied to the projection `X_T ⟶ T`,
which is flat by Stacks 03MO.  Properness of the support over `T` is
`AlgebraicGeometry.Space.isProperOver_supportOfSheaf_of_isInvertibleModule` applied to the same
projection, which is proper by Stacks 04WP and therefore locally of finite type. -/
@[stacks 0D03 "part one of the proof, the well-definedness of the natural map, on objects: the \
triple (T, g, L) of Section 0372 goes to the same triple in Situation 08KB. All three \
conditions 08KB imposes are proved, with no hypothesis beyond the tag's own flatness and \
properness of f. Finite presentation of an invertible module -- and with it quasi-coherence -- \
is Tag 0B8N(b) on the small etale site. The two citations the source makes are performed: the \
projection X_T -> T is flat by Tag 03MO and proper by Tag 04WP (isFlat_projection, \
isProper_projection). Their module-theoretic halves are isFlatOver_of_isInvertibleModule (Tag \
05VV, through the geometric-stalk criterion and Tag 05VX(1), the geometric stalk of an \
invertible module being free of rank one) and isProperOver_supportOfSheaf_of_isInvertibleModule \
(Tag 0CZD, the support being closed by Tag 07TZ and proper over the base by Tag 04XY). What \
remains of the tag is the second part of its proof, the open locus in T."]
def picardObjectToCoherent (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom)
    (A : PicardObject D.toPicardSituation) : CoherentObject D where
  T := A.T
  F := A.lineBundle
  quasicoherent :=
    haveI : A.lineBundle.IsFinitePresentationOnSite :=
      isFinitePresentationOnSite_of_isInvertibleModule A.lineBundle A.invertible
    SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite A.lineBundle
  finitePresentation := isFinitePresentationOnSite_of_isInvertibleModule A.lineBundle A.invertible
  flat :=
    isFlatOver_of_isInvertibleModule (D.projection A.T) A.lineBundle
      (isFlat_projection D hflat A.T) A.invertible
  properSupport :=
    ⟨isLocallyOfFiniteType_projection D A.T,
      isProperOver_supportOfSheaf_of_isInvertibleModule (D.projection A.T)
        (isLocallyOfFiniteType_projection D A.T) A.lineBundle
        (isProper_projection D hproper A.T) A.invertible⟩

/-- The natural map keeps the test scheme of the triple, which is the pair `(T, g)` of the
source. -/
@[simp]
theorem picardObjectToCoherent_T (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (A : PicardObject D.toPicardSituation) :
    (picardObjectToCoherent D hflat hproper A).T = A.T :=
  rfl

/-- The natural map keeps the module of the triple: the coherent sheaf it produces is the
invertible module it started from. -/
@[simp]
theorem picardObjectToCoherent_F (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (A : PicardObject D.toPicardSituation) :
    (picardObjectToCoherent D hflat hproper A).F = A.lineBundle :=
  rfl

/-- **Stacks 0D03, the first part of the proof: the natural map `Pic_{X/B} ⟶ Coh_{X/B}` on
objects.**  A triple `(T, g, L)` of the Picard stack of Section 0372 is sent to the same triple
`(T, g, L)` viewed in Situation 08KB.

The three conditions of Situation 08KB hold for an invertible `L` for the reasons the source
gives.  Finite presentation is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_of_isInvertibleModule` and quasi-coherence
follows from it.  Flatness over `T` is the declared hypothesis
`AlgebraicGeometry.Space.InvertibleIsFlatOver` applied to the projection `X_T ⟶ T`, which is
flat by Stacks 03MO.  Properness of the support over `T` is the declared hypothesis
`AlgebraicGeometry.Space.InvertibleHasProperSupport` applied to the same projection, which is
proper by Stacks 04WP and therefore locally of finite type. -/
def picardToCoherentObject (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (hfl : InvertibleIsFlatOver B S hS)
    (hsupp : InvertibleHasProperSupport B S hS)
    (A : PicardObject D.toPicardSituation) : CoherentObject D where
  T := A.T
  F := A.lineBundle
  quasicoherent :=
    haveI : A.lineBundle.IsFinitePresentationOnSite :=
      isFinitePresentationOnSite_of_isInvertibleModule A.lineBundle A.invertible
    SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite A.lineBundle
  finitePresentation := isFinitePresentationOnSite_of_isInvertibleModule A.lineBundle A.invertible
  flat := hfl (D.projection A.T) A.lineBundle (isFlat_projection D hflat A.T) A.invertible
  properSupport :=
    ⟨isLocallyOfFiniteType_projection D A.T,
      hsupp (D.projection A.T) (isLocallyOfFiniteType_projection D A.T) A.lineBundle
        (isProper_projection D hproper A.T) A.invertible⟩

/-- The natural map keeps the test scheme of the triple, which is the pair `(T, g)` of the
source. -/
@[simp]
theorem picardToCoherentObject_T (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (hfl : InvertibleIsFlatOver B S hS)
    (hsupp : InvertibleHasProperSupport B S hS) (A : PicardObject D.toPicardSituation) :
    (picardToCoherentObject D hflat hproper hfl hsupp A).T = A.T :=
  rfl

/-- The natural map keeps the module of the triple: the coherent sheaf it produces is the
invertible module it started from. -/
@[simp]
theorem picardToCoherentObject_F (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (hfl : InvertibleIsFlatOver B S hS)
    (hsupp : InvertibleHasProperSupport B S hS) (A : PicardObject D.toPicardSituation) :
    (picardToCoherentObject D hflat hproper hfl hsupp A).F = A.lineBundle :=
  rfl

/-! ### Part two: the locus in the test scheme -/

/-- The étale free locus of a module on an algebraic space is open, with none of the hypotheses
the openness clause of Stacks 0CZT carries.

This is `AlgebraicGeometry.Space.isOpen_of_etale_witness`, the mechanism behind that clause: if
`a : V ⟶ X` is an étale neighbourhood on which the module becomes free then every point in the
image of `|a|` has `a` for such a neighbourhood, so the locus contains the image of `|a|`, which
is open by Stacks 03IR.  The clause itself states the same conclusion under the hypotheses of the
source, which it does not use. -/
theorem isOpen_etaleFreeLocus_of_module {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) : IsOpen (etaleFreeLocus B S hS F) :=
  isOpen_of_etale_witness B S hS _ (by
    rintro x ⟨V, a, hae, hxr, hfree⟩
    exact ⟨V, a, hae, hxr, fun _ hy => ⟨V, a, hae, hy, hfree⟩⟩)

/-- The set of points of the test scheme `T` whose entire fibre in `X_T` lies in a given subset
`W` of `|X_T|`, written as the complement of the image under the projection `|X_T| ⟶ |T|` of the
complement of `W`.

This is the shape of the source's `U = T ∖ f_T(|X_T| ∖ W)` of the second part of the proof of
Stacks 0D03, with the subset left free: the source's own `U` is this at the *rank-one* locus
(`AlgebraicGeometry.Space.fibrewiseEtaleRankOneFreeLocus`), and
`AlgebraicGeometry.Space.fibrewiseEtaleFreeLocus` is this at the locus of Stacks 0CZT. -/
def fibrewiseLocus (D : CoherentSituation B S hS) (T : SchemesOver D.Y)
    (W : Set (points B S hS (D.space T).1)) :
    Set (points B S hS ((schemeSpaceFunctor B S hS).obj T.left).1) :=
  (pointsMap B S hS (D.space T).1 (D.projection T).hom '' Wᶜ)ᶜ

/-- A point of the test scheme lies in `AlgebraicGeometry.Space.fibrewiseLocus` exactly when
every point of `X_T` above it lies in the given subset.  This is what writing the locus as the
complement of the image of a complement says. -/
theorem mem_fibrewiseLocus_iff (D : CoherentSituation B S hS) (T : SchemesOver D.Y)
    (W : Set (points B S hS (D.space T).1))
    (t : points B S hS ((schemeSpaceFunctor B S hS).obj T.left).1) :
    t ∈ fibrewiseLocus D T W ↔
      ∀ x : points B S hS (D.space T).1,
        pointsMap B S hS (D.space T).1 (D.projection T).hom x = t → x ∈ W := by
  simp only [fibrewiseLocus, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  exact ⟨fun h x hx => by_contra fun hxw => h x hxw hx, fun h x hxw hx => hxw (h x hx)⟩

/-- `AlgebraicGeometry.Space.fibrewiseLocus` is open in `|T|` for an open subset of `|X_T|` when
`f` is proper: the projection `|X_T| ⟶ |T|` is a closed map because `X_T ⟶ T` is proper by
Stacks 04WP, so the image of the closed complement is closed and the locus, its complement, is
open. -/
theorem isOpen_fibrewiseLocus (D : CoherentSituation B S hS) (hf : IsProper B S hS D.f.hom)
    (T : SchemesOver D.Y) (W : Set (points B S hS (D.space T).1)) (hW : IsOpen W) :
    IsOpen (fibrewiseLocus D T W) :=
  (isClosedMap_pointsMap_projection D hf T _ hW.isClosed_compl).isOpen_compl

/-- **Stacks 0D03, the locus `U` of the second part of the proof.**  The set of points of the
test scheme `T` whose entire fibre in `X_T` lies in the étale free locus of `F`, written as the
complement of the image under the projection `|X_T| ⟶ |T|` of the complement of that locus.

This is `T ∖ f_T(|X_T| ∖ W)` with `W ⊆ |X_T|` the set of points at which `F` is free in an étale
neighbourhood, that is, the first of the source's two reductions.  The source's own `U` is
`AlgebraicGeometry.Space.fibrewiseEtaleRankOneFreeLocus`, which performs both at once. -/
def fibrewiseEtaleFreeLocus (D : CoherentSituation B S hS) (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    Set (points B S hS ((schemeSpaceFunctor B S hS).obj T.left).1) :=
  fibrewiseLocus D T (etaleFreeLocus B S hS F)

/-- A point of the test scheme lies in the locus exactly when every point of `X_T` above it is
one at which `F` is free in an étale neighbourhood.  This is what writing the locus as the
complement of the image of a complement says. -/
theorem mem_fibrewiseEtaleFreeLocus_iff (D : CoherentSituation B S hS) (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (t : points B S hS ((schemeSpaceFunctor B S hS).obj T.left).1) :
    t ∈ fibrewiseEtaleFreeLocus D T F ↔
      ∀ x : points B S hS (D.space T).1,
        pointsMap B S hS (D.space T).1 (D.projection T).hom x = t →
          x ∈ etaleFreeLocus B S hS F :=
  mem_fibrewiseLocus_iff D T (etaleFreeLocus B S hS F) t

/-- **Stacks 0D03, the locus `U` of the second part of the proof, at the rank-one locus — the
source's own `U`.**  The set of points of the test scheme `T` whose entire fibre in `X_T` lies in
the *rank-one* étale free locus of `F`.

This is the composite of the source's two reductions.  The source sets
`U = T ∖ f_T(|X_T| ∖ W)` with `W` the locus of Stacks 0CZT and then, having decomposed a finite
locally free module by rank as `X_T = X_0 ⨿ X_1 ⨿ X_2 ⨿ ⋯`, removes `f_T(|X_0| ∪ |X_2| ∪ ⋯)` as
well.  Since `|X_T| ∖ W₁ = (|X_T| ∖ W) ∪ |X_0| ∪ |X_2| ∪ ⋯`, the single locus `W₁` of rank-one
freeness delivers both removals at once, and no decomposition by rank is needed — which is what
makes this reachable here, the decomposition for algebraic spaces not being available
(`Stacks.SheafOfModules.rankDecomposition`, Stacks 0B37, is for ringed *spaces*). -/
def fibrewiseEtaleRankOneFreeLocus (D : CoherentSituation B S hS) (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    Set (points B S hS ((schemeSpaceFunctor B S hS).obj T.left).1) :=
  fibrewiseLocus D T (etaleRankOneFreeLocus B S hS F)

/-- A point of the test scheme lies in the rank-one locus exactly when every point of `X_T`
above it is one at which `F` is free of rank one in an étale neighbourhood. -/
theorem mem_fibrewiseEtaleRankOneFreeLocus_iff (D : CoherentSituation B S hS)
    (T : SchemesOver D.Y) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (t : points B S hS ((schemeSpaceFunctor B S hS).obj T.left).1) :
    t ∈ fibrewiseEtaleRankOneFreeLocus D T F ↔
      ∀ x : points B S hS (D.space T).1,
        pointsMap B S hS (D.space T).1 (D.projection T).hom x = t →
          x ∈ etaleRankOneFreeLocus B S hS F :=
  mem_fibrewiseLocus_iff D T (etaleRankOneFreeLocus B S hS F) t

/-- **Stacks 0D03, the construction of the open `U` of the second part of the proof.**  The locus
is open in `|T|` when `f` is proper.

The étale free locus is open, so its complement is closed, and the projection `|X_T| ⟶ |T|` is a
closed map because `X_T ⟶ T` is proper by Stacks 04WP; the image of that complement is therefore
closed and the locus, its complement, is open. -/
@[stacks 0D03 "part two of the proof, the construction of the open T \\ f_T(|X_T| \\ W) and its \
openness, unconditionally, as an open SUBSET of |T| for the point topology -- realizing it as an \
open subscheme of T is done in hasOpenLocus_picardToCoherent of \
Quot/PicardStackOpenImmersion.lean. W is the etale \
free locus of Tag 0CZT, open by the mechanism of that tag's openness clause \
(isOpen_of_etale_witness); the projection X_T -> T is proper by Tag 04WP, hence closed on \
points. This is the FIRST of the source's two reductions only; the source's own U is the same \
construction at the RANK-ONE locus, isOpen_fibrewiseEtaleRankOneFreeLocus, which performs both \
reductions at once. The source's parenthetical quasi-compactness assumption on T is not needed \
for either: it belongs to the decomposition X_T = X_0 + X_1 + ... by rank, which the rank-one \
locus makes unnecessary."]
theorem isOpen_fibrewiseEtaleFreeLocus (D : CoherentSituation B S hS)
    (hf : IsProper B S hS D.f.hom) (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    IsOpen (fibrewiseEtaleFreeLocus D T F) :=
  isOpen_fibrewiseLocus D hf T _ (isOpen_etaleFreeLocus_of_module F)

/-- **Stacks 0D03, the construction of the open `U` of the second part of the proof, at the
source's own `U`.**  The rank-one locus is open in `|T|` when `f` is proper.

The rank-one étale free locus `W₁` is open with no hypothesis
(`AlgebraicGeometry.Space.isOpen_etaleRankOneFreeLocus`, the mechanism of the openness clause of
Stacks 0CZT), and the projection `|X_T| ⟶ |T|` is a closed map because `X_T ⟶ T` is proper by
Stacks 04WP; so the image of the closed complement is closed and the locus is open.  No
decomposition of `X_T` by rank is used, and so no quasi-compactness of `T`. -/
@[stacks 0D03 "part two of the proof, the construction of the open U = T \\ f_T(|X_T| \\ W_1) \
and its openness, unconditionally, as an open SUBSET of |T| for the point topology -- realizing \
it as an open subscheme of T is done in hasOpenLocus_picardToCoherent of \
Quot/PicardStackOpenImmersion.lean. W_1 is \
the locus of Tag 0CZT with the rank pinned to ONE, and this U is the source's own U: it is the \
composite of the source's two reductions, since |X_T| \\ W_1 = (|X_T| \\ W) + X_0 + X_2 + ..., \
so the source's decomposition of a finite locally free module by rank is not needed and neither \
is its parenthetical quasi-compactness assumption on T. Openness of W_1 is the mechanism of the \
openness clause of 0CZT (isOpen_of_etale_witness) and the projection X_T -> T is proper by Tag \
04WP, hence closed on points."]
theorem isOpen_fibrewiseEtaleRankOneFreeLocus (D : CoherentSituation B S hS)
    (hf : IsProper B S hS D.f.hom) (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    IsOpen (fibrewiseEtaleRankOneFreeLocus D T F) :=
  isOpen_fibrewiseLocus D hf T _ (isOpen_etaleRankOneFreeLocus B S hS F)

/-! ### Part two: the two implications -/

/-- The implication (a) ⟹ (b) of the second part of the proof of Stacks 0D03, on points, with
the subset of `|X_T|` left free: if `g : T' ⟶ T` maps `|T'|` into
`AlgebraicGeometry.Space.fibrewiseLocus` at `W`, then `X_g : X_{T'} ⟶ X_T` maps `|X_{T'}|` into
`W`.

A point `x'` of `|X_{T'}|` goes to a point `x` of `|X_T|` lying over the image in `|T|` of the
point of `|T'|` below `x'`, because `X_g` commutes with the two projections to the test schemes;
that image lies in the locus, so `x` lies in `W`.  Nothing about `W` is used. -/
theorem range_pointsMap_relativeMap_subset_of_subset_fibrewiseLocus
    (D : CoherentSituation B S hS) {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (W : Set (points B S hS (D.space T).1))
    (hg : Set.range (pointsMap B S hS ((schemeSpaceFunctor B S hS).obj T'.left).1
        ((schemeSpaceFunctor B S hS).map g.left).hom) ⊆ fibrewiseLocus D T W) :
    Set.range (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom) ⊆ W := by
  rintro x ⟨x', rfl⟩
  have hsq : (D.relativeMap g).hom ≫ (D.projection T).hom =
      (D.projection T').hom ≫ ((schemeSpaceFunctor B S hS).map g.left).hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      baseChangeMap_comp_inclusion D.f g]
  have hx : pointsMap B S hS (D.space T).1 (D.projection T).hom
      (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom x') =
      pointsMap B S hS ((schemeSpaceFunctor B S hS).obj T'.left).1
        ((schemeSpaceFunctor B S hS).map g.left).hom
        (pointsMap B S hS (D.space T').1 (D.projection T').hom x') := by
    exact pointsMap_apply_comm B S hS hsq x'
  exact (mem_fibrewiseLocus_iff D T W _).1 (hg ⟨_, rfl⟩) _ hx

/-- **Stacks 0D03, the implication (a) ⟹ (b) of the second part of the proof, on points.**  If a
morphism `g : T' ⟶ T` of test schemes over `Y` maps `|T'|` into the locus, then the induced
morphism `X_g : X_{T'} ⟶ X_T` maps `|X_{T'}|` into the étale free locus of `F`.

A point `x'` of `|X_{T'}|` goes to a point `x` of `|X_T|` lying over the image in `|T|` of the
point of `|T'|` below `x'`, because `X_g` commutes with the two projections to the test schemes;
that image lies in the locus, so `x` lies in the étale free locus.  No base-change property of
the locus is used. -/
@[stacks 0D03 "part two of the proof, the implication (a) => (b) on points, unconditionally: if \
|T'| maps into U -- which is how condition (a), that T' -> T factors through U, is read here, U \
being produced as an open subset of |T| -- then |X_T'| maps into the etale free locus W of F. \
This is the \
direction that needs no base-change property of W, as the source's own argument shows; it is \
the commutation of X_g with the projections to the test schemes together with the description \
of U as the points whose whole fibre lies in W. The remaining step needs \
neither the rank decomposition nor a conditional \
clause of Tag 0B8Q: the rank decomposition is not needed at all -- pinning the rank to one at \
the level of the locus replaces it, see \
range_pointsMap_relativeMap_subset_etaleRankOneFreeLocus -- and the clause of Tag 0B8Q the step \
would use is the UNCONDITIONAL one, which holds at this site. What the step does need is \
recorded on that rank-one statement."]
theorem range_pointsMap_relativeMap_subset_etaleFreeLocus (D : CoherentSituation B S hS)
    {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hg : Set.range (pointsMap B S hS ((schemeSpaceFunctor B S hS).obj T'.left).1
        ((schemeSpaceFunctor B S hS).map g.left).hom) ⊆ fibrewiseEtaleFreeLocus D T F) :
    Set.range (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom) ⊆
      etaleFreeLocus B S hS F :=
  range_pointsMap_relativeMap_subset_of_subset_fibrewiseLocus D g _ hg

/-- **Stacks 0D03, the implication (a) ⟹ (b) of the second part of the proof, on points, at the
source's own `U`.**  If a morphism `g : T' ⟶ T` of test schemes over `Y` maps `|T'|` into the
rank-one locus, then `X_g : X_{T'} ⟶ X_T` maps `|X_{T'}|` into the rank-one étale free locus
of `F`.

This is `AlgebraicGeometry.Space.range_pointsMap_relativeMap_subset_of_subset_fibrewiseLocus` at
`W₁`, and it is the implication the source proves — its `U` is the rank-one locus, so what (a)
yields is rank-one freeness at every point of `|X_{T'}|` rather than freeness of some rank.  No
decomposition by rank and no base-change property of the locus is used. -/
@[stacks 0D03 "part two of the proof, the implication (a) => (b) on points at the source's own \
U, unconditionally: if |T'| maps into U = T \\ f_T(|X_T| \\ W_1) -- which is how condition (a), \
that T' -> T factors through U, is read here, U being produced as an open subset of |T| -- then \
|X_T'| maps into the RANK-ONE etale free locus W_1 of F. This is the direction that needs no \
base-change property of the locus, as the source's own argument shows; it is the commutation of \
X_g with the projections to the test schemes together with the description of U as the points \
whose whole fibre lies in W_1. Pinning the rank to one at the level of the locus is what \
replaces the source's decomposition X_T = X_0 + X_1 + ... by rank, which is not available for \
algebraic spaces. The passage from rank-one freeness in an etale neighbourhood of every \
point of |X_T'| to invertibility of F_T' takes two steps \
-- the easy inclusion of the base-change \
clause of Tag 0CZT and the local-to-global refinement for the unconditional clause of Tag 0B8Q; \
both steps are proved \
(preimage_etaleRankOneFreeLocus_subset and \
isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus), and the complete implication \
-- |T'| into U gives F_T' INVERTIBLE, unconditionally -- is \
isInvertibleModule_modulePullback_relativeMap_of_subset_fibrewiseEtaleRankOneFreeLocus below."]
theorem range_pointsMap_relativeMap_subset_etaleRankOneFreeLocus (D : CoherentSituation B S hS)
    {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hg : Set.range (pointsMap B S hS ((schemeSpaceFunctor B S hS).obj T'.left).1
        ((schemeSpaceFunctor B S hS).map g.left).hom) ⊆
      fibrewiseEtaleRankOneFreeLocus D T F) :
    Set.range (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom) ⊆
      etaleRankOneFreeLocus B S hS F :=
  range_pointsMap_relativeMap_subset_of_subset_fibrewiseLocus D g _ hg

/-- **Stacks 0D03, the implication (b) ⟹ (a) of the second part of the proof, on points.**  If
the pullback of `F` along `X_g : X_{T'} ⟶ X_T` is free in an étale neighbourhood of every point
of `|X_{T'}|` — which is the case when that pullback is invertible — then `X_g` maps `|X_{T'}|`
into the étale free locus of `F`.

This is the source's "if `T' ⟶ T` satisfies (b) then `|X_{T'}| ⟶ |X_T|` maps into `W`", and it
is exactly where the base-change clause of Stacks 0CZT enters; the clause is carried as
`AlgebraicGeometry.Space.EtaleFreeLocusBaseChange`. -/
theorem range_pointsMap_relativeMap_subset_etaleFreeLocus_of_free
    (hbc : EtaleFreeLocusBaseChange B S hS) (D : CoherentSituation B S hS)
    {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hF : ∀ x' : points B S hS (D.space T').1,
      x' ∈ etaleFreeLocus B S hS ((modulePullback B S hS (D.relativeMap g)).obj F)) :
    Set.range (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom) ⊆
      etaleFreeLocus B S hS F := by
  rintro x ⟨x', rfl⟩
  exact hbc D.f g F (hF x')

/-- **Stacks 0D03, the implication (b) ⟹ (a) of the second part of the proof, at the source's
own condition (b).**  If the pullback `F_{T'}` of `F` along `X_g : X_{T'} ⟶ X_T` is *invertible*
— which is condition (b) of the source, and not merely the étale-local freeness that
`AlgebraicGeometry.Space.range_pointsMap_relativeMap_subset_etaleFreeLocus_of_free` asks for —
then `X_g` maps `|X_{T'}|` into the étale free locus of `F`.

The passage from invertibility of `F_{T'}` to its freeness in an étale neighbourhood of every
point of `|X_{T'}|` is `AlgebraicGeometry.Space.mem_etaleFreeLocus_of_isInvertibleModule` and is
unconditional: it is the converse clause of Stacks 0B8Q at the small étale ringed site of an
algebraic space, which is locally ringed by Stacks 04KH, together with the comparison of
Stacks 04M0 between the slices of that site and the small étale sites of the chart spaces.  The
base-change clause of Stacks 0CZT is still needed, for the same reason as in
`AlgebraicGeometry.Space.range_pointsMap_relativeMap_subset_etaleFreeLocus_of_free`, and is
carried as `AlgebraicGeometry.Space.EtaleFreeLocusBaseChange`. -/
theorem range_pointsMap_relativeMap_subset_etaleFreeLocus_of_isInvertible
    (hbc : EtaleFreeLocusBaseChange B S hS) (D : CoherentSituation B S hS)
    {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hF : IsInvertibleModule (D.space T')
      ((modulePullback B S hS (D.relativeMap g)).obj F)) :
    Set.range (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom) ⊆
      etaleFreeLocus B S hS F :=
  range_pointsMap_relativeMap_subset_etaleFreeLocus_of_free hbc D g F
    (mem_etaleFreeLocus_of_isInvertibleModule (D.space T') _ hF)

/-- **Stacks 0D03, the implication (b) ⟹ (a) of the second part of the proof, on points.**  If
the pullback of `F` along `X_g : X_{T'} ⟶ X_T` is free in an étale neighbourhood of every point
of `|X_{T'}|` — which is the case when that pullback is invertible — then `X_g` maps `|X_{T'}|`
into the étale free locus of `F`.

This is the source's "if `T' ⟶ T` satisfies (b) then `|X_{T'}| ⟶ |X_T|` maps into `W`", and it
is exactly where the base-change clause of Stacks 0CZT enters.  That clause is now proved, as
`AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusBaseChange.lean`, so this statement is
unconditional.  `F` carries Stacks 0CZT's own hypotheses — quasi-coherent, of finite presentation
and flat over `T` — which is what an object of `Coh_{X/Y}` is, and local finite presentation of
the projection `X_T ⟶ T` costs nothing
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_projection`).  The square of the
morphism of test schemes is cartesian by
`AlgebraicGeometry.Space.isPullback_baseChangeMap`, which is the form the clause is stated at. -/
@[stacks 0D03 "part two of the proof, the implication (b) => (a) on points: if F_T' is free in \
an etale neighbourhood of every point then |X_T'| maps into the etale free locus W of F. \
UNCONDITIONAL. This is the direction the source derives from the base-change clause of \
Tag 0CZT, and that clause is proved: etaleFreeLocus_modulePullback_eq of \
Spaces/EtaleFreeLocusBaseChange.lean, registered on 0CZT with a which-part note, states the \
EQUALITY W(F_T') = |X_g|^(-1)(W(F)) at an arbitrary cartesian square. This statement \
binds no hypothesis standing in for that equality; its binders \
are D, g, F, 0CZT's own three conditions on F, and the antecedent (b). The source's route \
is what was assembled: clause (4) of Tag 0CZS \
(exists_chartOpen_over_iso_free_iff_flat_geometricFibreModuleStalk) at the image point, the \
base-change invariance of clause (1) \
(flat_geometricFibreModuleStalk_modulePullback_iff of \
Spaces/GeometricFibreStalkBaseChange.lean) for the transport, and the etale-locality of \
clause (1) (flat_geometricFibreModuleStalk_comp_modulePullback_iff of \
Spaces/GeometricFibreStalkEtaleLocal.lean) at the point upstairs. Condition (2) of Tag 05WY is \
NOT needed and is still neither stated nor proved; that is a gap in the registration of \
Tag 05WY alone. F carries 0CZT's own three hypotheses, quasi-coherent, of finite presentation \
and flat over T, which is exactly what an object of Coh_{X/Y} is (CoherentObject), so no \
consumer pays for them."]
theorem range_pointsMap_relativeMap_subset_etaleFreeLocus_of_forall_mem
    (D : CoherentSituation B S hS)
    {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hqc : F.IsQuasicoherentOnSite) (hfp : F.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F)
    (hF : ∀ x' : points B S hS (D.space T').1,
      x' ∈ etaleFreeLocus B S hS ((modulePullback B S hS (D.relativeMap g)).obj F)) :
    Set.range (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom) ⊆
      etaleFreeLocus B S hS F := by
  rintro x ⟨x', rfl⟩
  exact (Set.ext_iff.1 (etaleFreeLocus_modulePullback_eq B S hS
    (isPullback_baseChangeMap D.f g) F hqc
    (isLocallyOfFinitePresentation_projection D T) hfp hflat) x').1 (hF x')

/-- **Stacks 0D03, the implication (b) ⟹ (a) of the second part of the proof, at the source's
own condition (b).**  If the pullback `F_{T'}` of `F` along `X_g : X_{T'} ⟶ X_T` is *invertible*
— which is condition (b) of the source, and not merely the étale-local freeness that
`Space.range_pointsMap_relativeMap_subset_etaleFreeLocus_of_forall_mem` asks for — then `X_g` maps
`|X_{T'}|` into the étale free locus of `F`.

The passage from invertibility of `F_{T'}` to its freeness in an étale neighbourhood of every
point of `|X_{T'}|` is `AlgebraicGeometry.Space.mem_etaleFreeLocus_of_isInvertibleModule` and is
unconditional: it is the converse clause of Stacks 0B8Q at the small étale ringed site of an
algebraic space, which is locally ringed by Stacks 04KH, together with the comparison of
Stacks 04M0 between the slices of that site and the small étale sites of the chart spaces.  The
base-change clause of Stacks 0CZT is still used, for the same reason as in
`Space.range_pointsMap_relativeMap_subset_etaleFreeLocus_of_forall_mem`, and it is now proved
(`AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq`), so this statement is
unconditional as well; `F` carries Stacks 0CZT's own hypotheses here too, which is what an
object of `Coh_{X/Y}` is. -/
@[stacks 0D03 "part two of the proof, the implication (b) => (a) on points, with (b) at the \
source's own condition that F_T' be INVERTIBLE rather than at the etale-local freeness of the \
preceding statement. The step from invertibility to freeness in an etale neighbourhood of every \
point is unconditional here (mem_etaleFreeLocus_of_isInvertibleModule): the converse clause of \
Tag 0B8Q applies to the small etale ringed site of an algebraic space, which is locally ringed \
by Tag 04KH, in its universe-flexible form -- the site has its objects one universe above the \
sections of its structure sheaf, so the two carriers of 0B8Q stated for a bare ringed site do \
not instantiate -- and Tag 04M0 identifies a trivialization on a slice of that site with \
freeness of the pullback to the chart space, which is how the locus W of Tag 0CZT is phrased. \
UNCONDITIONAL. The base-change clause of Tag 0CZT, which this direction needs, is now proved: \
etaleFreeLocus_modulePullback_eq of Spaces/EtaleFreeLocusBaseChange.lean. This statement \
binds no hypothesis standing in for that equality; its binders \
are D, g, F, 0CZT's own three conditions on F, and the antecedent (b). The \
base-change invariance of clause (1) of Tag 0CZS \
(flat_geometricFibreModuleStalk_modulePullback_iff) does NOT need condition (2) of Tag 05WY. \
The converse implication, \
from |T'| mapping into U to invertibility of F_T', does not need the source's rank decomposition of \
X_T. The decomposition is replaced by pinning the rank to one at the level of the \
locus (etaleRankOneFreeLocus), and that converse is complete in \
isInvertibleModule_modulePullback_relativeMap_of_subset_fibrewiseEtaleRankOneFreeLocus. F \
carries 0CZT's own three hypotheses, quasi-coherent, of finite presentation and flat over T, \
which is exactly what an object of Coh_{X/Y} is (CoherentObject)."]
theorem range_pointsMap_relativeMap_subset_etaleFreeLocus_of_isInvertibleModule
    (D : CoherentSituation B S hS)
    {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hqc : F.IsQuasicoherentOnSite) (hfp : F.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F)
    (hF : IsInvertibleModule (D.space T')
      ((modulePullback B S hS (D.relativeMap g)).obj F)) :
    Set.range (pointsMap B S hS (D.space T').1 (D.relativeMap g).hom) ⊆
      etaleFreeLocus B S hS F :=
  range_pointsMap_relativeMap_subset_etaleFreeLocus_of_forall_mem D g F hqc hfp hflat
    (mem_etaleFreeLocus_of_isInvertibleModule (D.space T') _ hF)

/-- **Stacks 0D03, the implication (a) ⟹ (b) of the second part of the proof, complete.**  If a
morphism `g : T' ⟶ T` of test schemes over `Y` maps `|T'|` into the source's own locus
`U = T ∖ f_T(|X_T| ∖ W₁)`, then the pullback `F_{T'}` of `F` along `X_g : X_{T'} ⟶ X_T` is
*invertible* — which is the source's condition (b).  Unconditionally.

The three steps are each unconditional.  Condition (a) puts every point of `|X_{T'}|` over a
point of the rank-one étale free locus of `F`
(`AlgebraicGeometry.Space.range_pointsMap_relativeMap_subset_etaleRankOneFreeLocus`); the easy
inclusion of the base-change clause of Stacks 0CZT carries that locus forward along `X_g`
(`AlgebraicGeometry.Space.preimage_etaleRankOneFreeLocus_subset`, a pullback of a rank-one free
module being rank-one free); and a module whose rank-one étale free locus is all of `|X_{T'}|`
has rank one on the small étale site
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus`,
the local-to-global refinement), hence is invertible by the unconditional clause of Stacks 0B8Q
(`AlgebraicGeometry.Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`).

Neither the base-change clause of Stacks 0CZT nor the source's decomposition of `X_T` by rank is
used: the hard inclusion of that clause is what the *converse* implication needs, and the
decomposition is replaced by pinning the rank to one at the level of the locus. -/
@[stacks 0D03 "part two of the proof, the implication (a) => (b) COMPLETE and unconditional, at \
the source's own U and the source's own condition (b): if |T'| maps into U = T \\ f_T(|X_T| \\ \
W_1) -- which is how condition (a), that T' -> T factors through U, is read here, U being \
produced as an open SUBSET of |T| for the point topology -- then F_T' is INVERTIBLE. This \
completes the direction whose last two steps were recorded as missing on \
range_pointsMap_relativeMap_subset_etaleRankOneFreeLocus: (i) the easy inclusion of the \
base-change clause of Tag 0CZT, |X_g|^{-1}(W_1(F)) subset W_1(F_T'), which is \
preimage_etaleRankOneFreeLocus_subset and holds for an arbitrary morphism of algebraic spaces; \
and (ii) the local-to-global refinement from a trivialization through every POINT of |X_T'| to a \
trivializing covering family of every OBJECT of the small etale site, which is \
isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus -- the chosen neighbourhoods \
form an etale covering, so their charts cover the final object (coversTop_of_isEtaleCovering, \
the slice form of Tag 04M0), and the rank clause of Tag 0409 is local on such a family. The \
unconditional clause of Tag 0B8Q then gives invertibility. The source's decomposition of X_T by \
rank is not used, and neither is the base-change clause of Tag 0CZT: the hard inclusion of that \
clause is what the CONVERSE implication (b) => (a) needs, and it is proved in \
etaleFreeLocus_modulePullback_eq of Spaces/EtaleFreeLocusBaseChange.lean."]
theorem isInvertibleModule_modulePullback_relativeMap_of_subset_fibrewiseEtaleRankOneFreeLocus
    (D : CoherentSituation B S hS) {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hg : Set.range (pointsMap B S hS ((schemeSpaceFunctor B S hS).obj T'.left).1
        ((schemeSpaceFunctor B S hS).map g.left).hom) ⊆
      fibrewiseEtaleRankOneFreeLocus D T F) :
    IsInvertibleModule (D.space T') ((modulePullback B S hS (D.relativeMap g)).obj F) :=
  (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one _).2
    (isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus B S hS _ fun x' =>
      preimage_etaleRankOneFreeLocus_subset B S hS (D.relativeMap g) F
        (range_pointsMap_relativeMap_subset_etaleRankOneFreeLocus D g F hg ⟨x', rfl⟩))

end AlgebraicGeometry.Space

end
