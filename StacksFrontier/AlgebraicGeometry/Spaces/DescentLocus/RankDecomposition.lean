module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree

/-!
# The rank decomposition of Stacks 0D23

Let `f : X ⟶ Y` be a universally closed morphism of algebraic spaces such that the structure map
`𝒪_{Y'} ⟶ f'_*𝒪_{X'}` of every base change `f' : X' = X ×_Y Y' ⟶ Y'` is an isomorphism, and let
`E` be a finite locally free `𝒪_X`-module.  The proof of Stacks 0D23 begins by decomposing `Y`
according to the rank of `E`: every point of `|Y|` lies in the image of an affine étale chart
`V` of `Y` such that the pullback of `E` to `X ×_Y V` has a single rank.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.mem_rankLocus_iff_of_pointsMap_eq`: the rank of `E`
  is constant on the fibres of `|f|`.
* `AlgebraicGeometry.Space.DescentStratum.exists_affine_chart_isFiniteLocallyFreeOfRank`: **the
  rank decomposition**, in the rank form `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`
  of Stacks 0409, and
  `AlgebraicGeometry.Space.DescentStratum.exists_affine_chart_isFiniteLocallyFreeOfIntRank`, the
  same with `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank`.

## Implementation notes

Everything happens on points.  The rank loci of `E` (`AlgebraicGeometry.Space.rankLocus`) are
open, pairwise disjoint and cover `|X|`, hence clopen.  Over an étale chart `V` of `Y` the
structure map of `X ×_Y V ⟶ V` is an isomorphism, so the clopen preimage in `|X ×_Y V|` of a rank
locus is the preimage of a set of points of `V`
(`AlgebraicGeometry.Space.exists_preimage_eq_of_isClopen_of_isIso_fSharp`); since two points of
`|X|` over the same point of `|Y|` lift to points of `|X ×_Y V|` over one point of `V`
(`AlgebraicGeometry.Space.exists_point_of_isPullback`), the rank is constant on the fibres of
`|f|`.  As `|f|` is closed, the points of `|Y|` all of whose preimages have the rank `r` of the
fibre over `y` form an open neighbourhood of `y`, and an affine open of a chart through `y` inside
it is the chart sought.  The pullback of `E` to `X ×_Y V` then has rank `r` by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_iff`.  When the fibre over `y`
is empty every rank will do, and `r = 0` is taken.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.DescentStratum

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure map of the ringed-topos morphism of `f` is an isomorphism when the structure map
of sheaves of rings is: the two agree after forgetting commutativity. -/
theorem isIso_fSharp_of_isIso_structureSharp {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (h : IsIso (structureSharp B S hS f)) : IsIso (smallEtaleRingedToposHom B S hS f).fSharp := by
  have h' : IsIso ((sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (smallEtaleRingedToposHom B S hS f).fSharp) := by
    rwa [forgetCommRingSheaf_map_fSharp]
  exact isIso_of_reflects_iso _
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The rank loci of a finite locally free module are open and closed. -/
private theorem isClopen_rankLocus {Y : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (n : ℕ) : IsClopen (rankLocus M n) := by
  refine ⟨?_, isOpen_rankLocus M n⟩
  have hc : (rankLocus M n)ᶜ = ⋃ m ∈ {m : ℕ | m ≠ n}, rankLocus M m := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hy
      obtain ⟨m, hm⟩ := exists_mem_rankLocus hM y
      exact ⟨m, fun h => hy (h ▸ hm), hm⟩
    · rintro ⟨m, hmn, hm⟩ hy
      exact hmn (eq_of_mem_rankLocus_of_mem_rankLocus hm hy)
  rw [← isOpen_compl_iff, hc]
  exact isOpen_biUnion fun m _ => isOpen_rankLocus M m

/-- **The rank of `E` is constant on the fibres of `|f|`** when the structure map of the base
change of `f` along every étale chart of `Y` is an isomorphism. -/
theorem mem_rankLocus_iff_of_pointsMap_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    {E : Modules.{u, u} B S hS X.1 X.2} (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (n : ℕ) {x₁ x₂ : points B S hS X.1}
    (h : pointsMap B S hS X.1 f.hom x₁ = pointsMap B S hS X.1 f.hom x₂) :
    x₁ ∈ rankLocus E n ↔ x₂ ∈ rankLocus E n := by
  obtain ⟨V, p, hp⟩ := exists_chart_point B S hS Y.1 Y.2 (pointsMap B S hS X.1 f.hom x₁)
  let T := (SmallEtale.toOver B S hS Y.1).obj V
  let c : schemeSpace T ⟶ Y := chartToSpace B S hS Y V
  let g : pullback f c ⟶ schemeSpace T := pullback.snd f c
  let j : pullback f c ⟶ X := pullback.fst f c
  have : IsIso (smallEtaleRingedToposHom B S hS g).fSharp :=
    isIso_fSharp_of_isIso_structureSharp g (hiso c)
  let C : Set (points B S hS (pullback f c).obj) :=
    pointsMap B S hS _ j.hom ⁻¹' rankLocus E n
  obtain ⟨D, hD⟩ := exists_preimage_eq_of_isClopen_of_isIso_fSharp g C
    ((isClopen_rankLocus hE n).preimage (continuous_pointsMap B S hS _))
  have hlift : ∀ x : points B S hS X.1,
      pointsMap B S hS X.1 f.hom x = pointsMap B S hS X.1 f.hom x₁ →
      ∃ w, pointsMap B S hS _ j.hom w = x ∧ pointsMap B S hS _ g.hom w = p := fun x hx =>
    exists_point_of_isPullback B S hS (IsPullback.of_hasPullback f c) x p (hx.trans hp.symm)
  obtain ⟨w₁, hw₁, hw₁'⟩ := hlift x₁ rfl
  obtain ⟨w₂, hw₂, hw₂'⟩ := hlift x₂ h.symm
  rw [← hw₁, ← hw₂]
  change w₁ ∈ C ↔ w₂ ∈ C
  rw [hD w₁, hD w₂]
  exact Iff.of_eq (congrArg (fun q => pointsToScheme B S hS T q ∈ D) (hw₁'.trans hw₂'.symm))

/-- **The rank decomposition of Stacks 0D23.**  Let `f : X ⟶ Y` be universally closed, such that
the structure map of every base change of `f` is an isomorphism, and let `E` be a finite locally
free `𝒪_X`-module.  Every point `y` of `|Y|` lies in the image of an étale chart `V` of `Y` whose
scheme is affine and over which the pullback of `E` to `X ×_Y V` is finite locally free of a
single rank `r`. -/
theorem exists_affine_chart_isFiniteLocallyFreeOfRank {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : UniversallyClosed B S hS f.hom)
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E)
    (y : points B S hS Y.1) :
    ∃ (V : SmallEtale B S hS Y.1) (r : ℕ), IsAffine (chartScheme V) ∧
      y ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS Y V).hom) ∧
      RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS (pullback f (chartToSpace B S hS Y V)).1
          (pullback f (chartToSpace B S hS Y V)).2)
        ((modulePullback B S hS (pullback.fst f (chartToSpace B S hS Y V))).obj E) r := by
  have hE' : SheafOfModules.IsFiniteLocallyFreeOnSite E :=
    Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree E hE
  -- the rank of `E` on the fibre over `y`
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ∀ x, pointsMap B S hS X.1 f.hom x = y → x ∈ rankLocus E r := by
    by_cases hy : ∃ x, pointsMap B S hS X.1 f.hom x = y
    · obtain ⟨x₀, hx₀⟩ := hy
      obtain ⟨r, hr⟩ := exists_mem_rankLocus hE' x₀
      exact ⟨r, fun x hx =>
        (mem_rankLocus_iff_of_pointsMap_eq f hiso hE' r (hx₀.trans hx.symm)).1 hr⟩
    · exact ⟨0, fun x hx => (hy ⟨x, hx⟩).elim⟩
  -- the points of `|Y|` over which every point has rank `r` form an open neighbourhood of `y`
  let O : Set (points B S hS Y.1) := (pointsMap B S hS X.1 f.hom '' (rankLocus E r)ᶜ)ᶜ
  have hO : IsOpen O := (isClosedMap_pointsMap_of_pullback_fst_id B S hS f.hom
    (hf Y.1 Y.2 (𝟙 Y.1)) _ (isOpen_rankLocus E r).isClosed_compl).isOpen_compl
  have hyO : y ∈ O := fun ⟨x, hx, hxy⟩ => hx (hr x hxy)
  -- an affine open of a chart through `y` inside that neighbourhood
  obtain ⟨V₀, v, hv⟩ := exists_chartSchemeToPoints_eq B S hS Y y
  have hvO : v ∈ chartSchemeToPoints B S hS Y.1 V₀ ⁻¹' O := by
    rwa [Set.mem_preimage, hv]
  obtain ⟨_, ⟨W, hW, rfl⟩, hvW, hWO⟩ :=
    (chartScheme V₀).isBasis_affineOpens.exists_subset_of_mem_open hvO
      (hO.preimage (continuous_chartSchemeToPoints B S hS V₀))
  let V := openChart B S hS Y.1 V₀ W
  have hpt : ∀ z : chartScheme V,
      chartSchemeToPoints B S hS Y.1 V z = chartSchemeToPoints B S hS Y.1 V₀ z.1 := by
    intro z
    rw [← chartSchemeToPoints_map B S hS Y.1 (openChartInclusion B S hS Y.1 V₀ W) z,
      toScheme_map_toOver_map_openChartInclusion]
    rfl
  refine ⟨V, r, hW, ?_, ?_⟩
  · exact (hpt ⟨v, hvW⟩).trans hv ▸ chartSchemeToPoints_mem_range B S hS V ⟨v, hvW⟩
  · refine (isFiniteLocallyFreeOfRank_modulePullback_iff _ hE' r).2 ?_
    rintro _ ⟨w, rfl⟩
    by_contra hx
    have hw : (pullback.fst f (chartToSpace B S hS Y V)).hom ≫ f.hom =
        (pullback.snd f (chartToSpace B S hS Y V)).hom ≫ (chartToSpace B S hS Y V).hom :=
      congrArg (fun m => m.hom) (pullback.condition (f := f) (g := chartToSpace B S hS Y V))
    have himg : pointsMap B S hS X.1 f.hom
        (pointsMap B S hS _ (pullback.fst f (chartToSpace B S hS Y V)).hom w) ∈
          Set.range (pointsMap B S hS _ (chartToSpace B S hS Y V).hom) := by
      refine ⟨pointsMap B S hS _ (pullback.snd f (chartToSpace B S hS Y V)).hom w, ?_⟩
      have e₁ := congrFun (pointsMap_comp B S hS _
        (pullback.fst f (chartToSpace B S hS Y V)).hom f.hom) w
      have e₂ := congrFun (pointsMap_comp B S hS _
        (pullback.snd f (chartToSpace B S hS Y V)).hom (chartToSpace B S hS Y V).hom) w
      exact e₂.symm.trans ((congrArg (fun m => pointsMap B S hS _ m w) hw).symm.trans e₁)
    obtain ⟨z, hz⟩ := exists_chartSchemeToPoints_eq_of_mem_range B S hS V himg
    have hzO : chartSchemeToPoints B S hS Y.1 V z ∈ O := by
      rw [hpt]
      exact hWO z.2
    rw [hz] at hzO
    exact hzO ⟨_, hx, rfl⟩

/-- **The rank decomposition of Stacks 0D23, with an integer rank**: the same statement as
`AlgebraicGeometry.Space.DescentStratum.exists_affine_chart_isFiniteLocallyFreeOfRank`, read with
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank`. -/
theorem exists_affine_chart_isFiniteLocallyFreeOfIntRank {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : UniversallyClosed B S hS f.hom)
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E)
    (y : points B S hS Y.1) :
    ∃ (V : SmallEtale B S hS Y.1) (r : ℕ), IsAffine (chartScheme V) ∧
      y ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS Y V).hom) ∧
      SheafOfModules.IsFiniteLocallyFreeOfIntRank
        ((modulePullback B S hS (pullback.fst f (chartToSpace B S hS Y V))).obj E) (r : ℤ) := by
  obtain ⟨V, r, hV, hy, hr⟩ := exists_affine_chart_isFiniteLocallyFreeOfRank f hf hiso E hE y
  exact ⟨V, r, hV, hy, (SheafOfModules.isFiniteLocallyFreeOfIntRank_natCast_iff _ r).2
    ((RingedSite.isFiniteLocallyFreeOfRank_iff_sheafOfModules _ _ r).1 hr)⟩

end AlgebraicGeometry.Space.DescentStratum

end
