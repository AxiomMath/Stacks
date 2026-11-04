module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankEtaleLocal
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of a module on an algebraic space is étale local on the base

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` which is surjective
on points.  An `𝒪_Y`-module on the small étale ringed site of `Y` is finite locally free exactly
when its étale restriction to `X` is.  This is the clause of Stacks 03DN for finite local
freeness, read along an étale morphism of algebraic spaces rather than along a covering family
of one site, and it is the step which the proof of Stacks 03ZU performs with Modules on Sites,
Lemma 03DN after choosing a surjective étale `V ⟶ Y`.

Applied to the direct image `f_*𝒪_X` of Stacks 03ZV, and combined with the étale base change
Stacks 03LX of that direct image, it says that the module conjunct of Stacks 03ZV may be tested
after an arbitrary base change along a surjective étale morphism; so finite local freeness of a
morphism of algebraic spaces is affineness of the morphism together with finite local freeness
of such a base change.  Both statements are rank free, as Stacks 03ZU is.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_iff_over_of_isSurjective`: finite local
  freeness of a module on the small étale ringed site of an algebraic space may be tested on the
  slice at one étale chart whose structure morphism is surjective on points.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_etaleModulePullback_iff`: **finite local
  freeness is étale local on the base.** A module is finite locally free exactly when its étale
  restriction along a morphism of algebraic spaces surjective on points is.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_pushforwardStructureModule_iff_of_isPullback`:
  the module conjunct of Stacks 03ZV is unchanged by base change along a surjective étale
  morphism.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_iff_isAffineHom_and_baseChange`: finite local
  freeness of a morphism of algebraic spaces in the sense of Stacks 03ZV is its affineness
  together with finite local freeness of its base change along a surjective étale morphism.

## Implementation notes

Finite local freeness of a module is `SheafOfModules.IsFiniteLocallyFreeOnSite`, the
universe-flexible form of Stacks 03DL (2), and the étale restriction is
`AlgebraicGeometry.Space.etaleModulePullback`, restriction along postcomposition of charts; no
change of scalars is involved, so the two structure sheaves on a slice of a small étale site
agree on the nose.  The rank-indexed companions of the first three statements are not recorded:
they would read the same way through
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_reindex_iff`, and Stacks 03ZU states no
rank.

The comparison of a slice with the small étale site of the chart is not used, and neither is any
identification of the two structure sheaves across the site equivalence of Stacks 04M0: the
locality statement is proved by transporting a covering family inside one site.  In the forward
direction the covering family is the family of *all* objects of the small étale site of `X`,
which covers its final object for formal reasons, and the restriction of the pullback to the
slice at a chart `V` is compared with the restriction of the module to the composite chart by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff`.  In the
converse direction the family is a single étale chart of `X` surjective on points, whose
composite with `f` is an étale chart of `Y` surjective on points and therefore covers the final
object of the small étale site of `Y` by
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`.

*What Stacks 03ZU needs beyond this file.*  Both inputs its proof cites are available:
Stacks 03LX, Properties of Spaces, Lemma 66.26.2, is
`AlgebraicGeometry.Space.pushforwardStructureModuleEtaleBaseChangeIso`, and Stacks 03DN, Modules
on Sites, Lemma 18.23.3, for finite local freeness is
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite`,
whose reading along an étale morphism of algebraic spaces is proved below.  What this file does
not supply is a step the source leaves to its conventions: for a *scheme* `V` the source
identifies `Mod(𝒪_V)` with the modules on the small étale site of `V`, whereas
`Stacks.Morphisms.IsFiniteLocallyFree` asks for finite local freeness of
`Stacks.Morphisms.pushforwardStructureSheaf` on the Zariski site of `V` and
`AlgebraicGeometry.Space.IsFiniteLocallyFree` asks it of
`AlgebraicGeometry.Space.pushforwardStructureModule` on the small étale ringed site.  No
statement here mentions `Stacks.Morphisms.IsFiniteLocallyFree`, and the equivalence of
Stacks 03ZU itself is not asserted here; it is asserted, and that step performed, in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`, as
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree`, where the Zariski versus small étale
comparison for a scheme is the clause 03DL (2) of Stacks 05VG,
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff`, carried to the
slice at a chart by `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sliceAssociatedModule_iff`.
Only the rank form of the equivalence is still open, over the rank chart comparison that
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison` carries as a
hypothesis: no statement in the tree transports a rank across `𝓕 ↦ 𝓕ᵃ`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Finite local freeness at one surjective étale chart -/

/-- **Finite local freeness may be tested on one surjective étale chart.** A module on the small
étale ringed site of an algebraic space over `S` is finite locally free exactly when its
restriction to the slice at one étale chart whose structure morphism is surjective on points
is. -/
theorem isFiniteLocallyFreeOnSite_iff_over_of_isSurjective
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (hsurj : IsSurjective B S hS V.1.hom) :
    SheafOfModules.IsFiniteLocallyFreeOnSite M ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V) (M.over V) := by
  refine ⟨fun h => h.over V, fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
    (smallEtaleRingedSite B S hS Y.1 Y.2) M).2
    ⟨PUnit.{u + 2}, fun _ => V,
      SmallEtale.coversTop_of_isSurjective B S hS Y.1 Y.2 V hsurj, fun _ => h⟩

/-! ### Finite local freeness is étale local on the base -/

/-- **Finite local freeness is étale local on the base.** For an étale morphism `f : X ⟶ Y` of
algebraic spaces over `S` which is surjective on points, an `𝒪_Y`-module on the small étale
ringed site of `Y` is finite locally free exactly when its étale restriction to `X` is.

This is an application of the clause of Stacks 03DN for finite local freeness, read along an
étale morphism of algebraic spaces rather than along a covering family of one site; it is the
shape in which the proof of Stacks 03ZU uses Modules on Sites, Lemma 03DN after choosing a
surjective étale `V ⟶ Y`.  The clause itself, for an arbitrary ringed site, is
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite`. -/
theorem isFiniteLocallyFreeOnSite_etaleModulePullback_iff (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    SheafOfModules.IsFiniteLocallyFreeOnSite M ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((etaleModulePullback B S hS f hf).obj M) := by
  constructor
  · intro hM
    refine
      (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
        (smallEtaleRingedSite B S hS X.1 X.2)
        ((etaleModulePullback B S hS f hf).obj M)).2
      ⟨ULift.{u + 1} (smallEtaleRingedSite B S hS X.1 X.2).C, fun i => i.down,
        Stacks.SheafOfModules.coversTop_ulift_self
          (smallEtaleRingedSite B S hS X.1 X.2).J, fun i => ?_⟩
    exact (isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff B S hS f hf M i.down).2
      (hM.over _)
  · intro hN
    obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS X.1 X.2
    refine (isFiniteLocallyFreeOnSite_iff_over_of_isSurjective B S hS M
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)
      (isSurjective_smallEtalePostcomp_obj_hom B S hS f hf hsurj V hV)).2 ?_
    exact (isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff B S hS f hf M V).1 (hN.over V)

/-! ### The module conjunct of Stacks 03ZV along a surjective étale base change -/

section BaseChange

variable {X' Y' : AlgebraicSpaces B S hS}

/-- **The module conjunct of Stacks 03ZV is unchanged by a surjective étale base change.** For a
cartesian square with `g : Y' ⟶ Y` étale and surjective on points, the direct image `f_*𝒪_X` is
finite locally free exactly when `f'_*𝒪_{X'}` is.

This combines the étale base change of the direct image, Stacks 03LX, with étale locality of
finite local freeness on the base. -/
theorem isFiniteLocallyFreeOnSite_pushforwardStructureModule_iff_of_isPullback
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hgsurj : IsSurjective B S hS g.hom) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (pushforwardStructureModule B S hS f) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite (pushforwardStructureModule B S hS f') :=
  Iff.trans
    (isFiniteLocallyFreeOnSite_etaleModulePullback_iff B S hS g hg hgsurj
      (pushforwardStructureModule B S hS f))
    (isFiniteLocallyFreeOnSite_pushforwardStructureModule_baseChange_iff
      B S hS i f' f g sq hg).symm

/-- **Finite local freeness of a morphism of algebraic spaces is affineness together with finite
local freeness of a surjective étale base change.** For a cartesian square with `g : Y' ⟶ Y`
étale and surjective on points, `f` is finite locally free in the sense of Stacks 03ZV exactly
when `f` is affine and `f'` is finite locally free.

Affineness of `f'` follows from affineness of `f` by Stacks 03WI, so the content is the module
conjunct; affineness of `f` is retained on the right because its descent along a surjective
étale morphism of algebraic spaces is a separate statement, Stacks 03WG. -/
theorem isFiniteLocallyFree_iff_isAffineHom_and_baseChange
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hgsurj : IsSurjective B S hS g.hom) :
    IsFiniteLocallyFree B S hS f ↔
      IsAffineHom B S hS f.hom ∧ IsFiniteLocallyFree B S hS f' := by
  have hmod := isFiniteLocallyFreeOnSite_pushforwardStructureModule_iff_of_isPullback
    B S hS i f' f g sq hg hgsurj
  refine ⟨fun h => ⟨h.1, ?_, hmod.1 h.2⟩, fun h => ⟨h.1, hmod.2 h.2.2⟩⟩
  exact IsAffineHom.of_isPullback (sq.map (ObjectProperty.ι (IsAlgebraicSpace B S hS))) h.1

end BaseChange

end AlgebraicGeometry.Space

end
