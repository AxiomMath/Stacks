module

public import Mathlib.Topology.Spectral.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableImpliesFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Topology.Spectral.PrespectralOpenSurjection

/-!
# The point space of a quasi-compact quasi-separated algebraic space is spectral

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site. Its point space
is always prespectral, because an étale chart from a scheme is continuous, open and surjective
on points and the point space of a scheme is prespectral. If `X` is quasi-separated then its
point space is quasi-separated as well, and `X` is decent, hence its point space is Kolmogorov
and quasi-sober. Adding quasi-compactness, which is compactness of the point space, gives all
five conditions in the definition of a spectral space.

## Main results

* `AlgebraicGeometry.Space.prespectralSpace_points`: the point space of an algebraic space
  over `S` is prespectral.
* `AlgebraicGeometry.Space.isDecentSpace_of_isAbsolutelyQuasiSeparated`: a quasi-separated
  algebraic space over `S` is decent.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isCompact_range`: an open subspace with
  compact set of points is quasi-compact.
* `AlgebraicGeometry.Space.quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated`: the
  point space of a quasi-separated algebraic space over `S` is quasi-separated.
* `AlgebraicGeometry.Space.spectralSpace_points_of_isQuasiCompactSpace_isAbsolutelyQuasiSeparated`:
  **Stacks 0A4G**, the point space of a quasi-compact quasi-separated algebraic space over `S`
  is spectral.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here, so every statement reads `pointTopology` on every point space.

Quasi-separatedness of `X` is taken in the absolute sense of Tag 0AHR, which is the hypothesis
`AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`. That predicate is stated relative to the
terminal scheme and therefore mentions a containment of the terminal scheme in the site; the
containment is not a hypothesis, since `AlgebraicGeometry.BigFppfSite.contains_terminal`
discharges it for every big fppf site, and it is written out that way.

Decency is reached along the implications of Tag 03JX: `(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ) ⇒ (γ)`, and
condition `(γ)` is condition (1) of Tag 03JV, which is equivalent to the definition of decency
used in this repository.

Quasi-separatedness of the point space is checked directly on a pair of quasi-compact opens:
each corresponds to an open subspace under Tag 03BZ, that subspace is quasi-compact because
its points form a compact subset, so it has an affine étale chart, and the fibre product of
the two charts over `X` has quasi-compact underlying scheme by Tag 0AHR. The image of its
point space is the intersection of the two opens, by Tag 03H4 for one inclusion and
functoriality of the map on points for the other.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 0A4G](https://stacks.math.columbia.edu/tag/0A4G)
* [Stacks Project, Tag 0AHR](https://stacks.math.columbia.edu/tag/0AHR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point space of an algebraic space over `S` is prespectral: an étale chart from a
scheme is continuous, open and surjective on points by Tags 03BX, 03IR and 03H5, the point
space of the chart is the underlying space of a scheme by clause (1) of Tag 03BX, and that
space is prespectral. -/
theorem prespectralSpace_points (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) : PrespectralSpace (points B S hS X) := by
  obtain ⟨U, p, hpSurj, hpEt⟩ := hX.exists_atlas
  have hchart : PrespectralSpace (points B S hS (yoneda.obj U)) :=
    (schemePointsHomeomorph B S hS U).isOpenEmbedding.prespectralSpace
  exact prespectralSpace_of_isOpenMap_surjective (continuous_pointsMap B S hS p)
    (isOpenMap_pointsMap_of_isEtale B S hS p (isAlgebraicSpace_yoneda B S hS U) hX
      (isEtale_of_presheaf_etale B S hS hpEt))
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX U p).mp hpSurj)

/-- A quasi-separated algebraic space over `S` is decent: quasi-separatedness is condition
`(η)` of Tag 03JX, and `(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ) ⇒ (γ)` ends at condition (1) of Tag 03JV, which
is the definition of decency used here. -/
theorem isDecentSpace_of_isAbsolutelyQuasiSeparated (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X) :
    IsDecentSpace B S hS X :=
  (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX).2
    (hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace B S hS X hX
      (isReasonableSpace_of_isVeryReasonableSpace B S hS X hX
        (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS
          B.contains_terminal X hX
          (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS X
            B.contains_terminal hX hqs))))

/-- An open subspace of an algebraic space over `S` whose set of points is a compact subset of
the ambient point space is quasi-compact: the inclusion is an open embedding on points by Tags
06RV and 03IR, so the point space of the subspace is compact, which is Tag 03E4. -/
theorem isQuasiCompactSpace_of_isCompact_range
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hcompact : IsCompact (Set.range (pointsMap B S hS G.toFunctor G.ι))) :
    IsQuasiCompactSpace B S hS G.toFunctor := by
  have hembed : IsOpenEmbedding (pointsMap B S hS G.toFunctor G.ι) :=
    isOpenEmbedding_iff_continuous_injective_isOpenMap.2
      ⟨continuous_pointsMap B S hS G.ι, pointsMap_injective_of_mono B S hS G.ι,
        isOpenMap_pointsMap_of_isEtale B S hS G.ι hG.1 hX (isEtale_ι_of_isOpenSubspace hG)⟩
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS G.toFunctor hG.1).mpr
    (isCompact_univ_iff.mp (hembed.isEmbedding.isCompact_iff.mpr ?_))
  simpa only [Set.image_univ] using hcompact

/-- The point space of a quasi-separated algebraic space over `S` is quasi-separated.

Two quasi-compact open subsets of the point space are the images of the point spaces of two
quasi-compact open subspaces, by Tag 03BZ; each of those has an affine étale chart by Tag 03H6,
the fibre product of the two charts over `X` is represented by an object of the site with
quasi-compact underlying scheme by Tag 0AHR, and the image of its point space is exactly the
intersection of the two given opens. -/
theorem quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X) :
    QuasiSeparatedSpace (points B S hS X) := by
  classical
  refine ⟨fun A D hAopen hAcompact hDopen hDcompact ↦ ?_⟩
  let eOpen := openSubspacesOrderIso B S hS X hX
  -- a quasi-compact open of the point space is the image of an affine chart of `X`
  have chart (T : Set (points B S hS X)) (hTo : IsOpen T) (hTc : IsCompact T) :
      ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
          Set.range (pointsMap B S hS (yoneda.obj U) f) = T := by
    let Tsub : Subfunctor X := (eOpen.symm ⟨T, hTo⟩).1
    have hTsub : IsOpenSubspace B S hS Tsub := (eOpen.symm ⟨T, hTo⟩).2
    have hrange : Set.range (pointsMap B S hS Tsub.toFunctor Tsub.ι) = T := by
      rw [← openSubspacesOrderIso_apply B S hS X hX (eOpen.symm ⟨T, hTo⟩)]
      exact congrArg (fun O : Opens _ ↦ O.carrier) (eOpen.apply_symm_apply ⟨T, hTo⟩)
    obtain ⟨U, α, hUaffine, hαsurj, -⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Tsub.toFunctor
        hTsub.1).mp (isQuasiCompactSpace_of_isCompact_range B S hS hX hTsub (hrange ▸ hTc))
    refine ⟨U, α ≫ Tsub.ι, hUaffine, ?_⟩
    rw [pointsMap_comp, Set.range_comp, ((presheafSurjective_iff_isSurjective_yoneda B S hS
      Tsub.toFunctor hTsub.1 U α).mp hαsurj).range_eq, Set.image_univ, hrange]
  obtain ⟨UA, fA, hUAaffine, hA⟩ := chart A hAopen hAcompact
  obtain ⟨VD, fD, hVDaffine, hD⟩ := chart D hDopen hDcompact
  obtain ⟨W, hWcompact, ⟨e⟩⟩ :=
    (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS B.contains_terminal X
      hX).mp hqs UA VD fA fD hUAaffine hVDaffine
  -- the fibre product of the two charts, as a cartesian square of algebraic spaces
  let AObj : AlgebraicSpaces B S hS := ⟨yoneda.obj UA, isAlgebraicSpace_yoneda B S hS UA⟩
  let DObj : AlgebraicSpaces B S hS := ⟨yoneda.obj VD, isAlgebraicSpace_yoneda B S hS VD⟩
  let XObj : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let fAObj : AObj ⟶ XObj := ObjectProperty.homMk fA
  let fDObj : DObj ⟶ XObj := ObjectProperty.homMk fD
  let PObj := AlgebraicSpaces.fiberProduct B S hS fAObj fDObj
  obtain ⟨pObj, qObj, hsq⟩ : ∃ (pObj : PObj ⟶ AObj) (qObj : PObj ⟶ DObj),
      IsPullback pObj qObj fAObj fDObj :=
    ⟨_, _, AlgebraicSpaces.isPullback_fiberProduct B S hS fAObj fDObj⟩
  let eP : yoneda.obj W ≅ PObj.obj := e
  have hcomp : pObj.hom ≫ fA = qObj.hom ≫ fD := congrArg (fun g ↦ g.hom) hsq.w
  have hePts : Function.Surjective (pointsMap B S hS (yoneda.obj W) eP.hom) := fun z ↦
    ⟨pointsMap B S hS PObj.obj eP.inv z, by
      rw [← pointsMap_comp_apply, eP.inv_hom_id, pointsMap_id, id_eq]⟩
  -- the image of the point space of `W` is the intersection of the two opens
  have hrange : Set.range (pointsMap B S hS (yoneda.obj W) (eP.hom ≫ pObj.hom ≫ fA)) =
      A ∩ D := by
    rw [pointsMap_comp, Set.range_comp, hePts.range_eq, Set.image_univ, ← hA, ← hD]
    apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      exact ⟨⟨pointsMap B S hS PObj.obj pObj.hom w, (pointsMap_comp_apply B S hS _ _ w).symm⟩,
        ⟨pointsMap B S hS PObj.obj qObj.hom w, by
          rw [hcomp]
          exact (pointsMap_comp_apply B S hS _ _ w).symm⟩⟩
    · rintro _ ⟨⟨a, rfl⟩, ⟨d, hd⟩⟩
      obtain ⟨z, hz, -⟩ := exists_point_of_isPullback B S hS hsq a d hd.symm
      exact ⟨z, by rw [pointsMap_comp_apply, hz]⟩
  -- the point space of `W` is compact, so the intersection is compact
  have hWpts : CompactSpace (points B S hS (yoneda.obj W)) :=
    have : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := hWcompact
    (schemePointsHomeomorph B S hS W).symm.compactSpace
  rw [← hrange, ← Set.image_univ]
  exact isCompact_univ.image (continuous_pointsMap B S hS _)

/-- **Stacks 0A4G.** The point space of a quasi-compact quasi-separated algebraic space over
`S` is a spectral space. -/
@[stacks 0A4G]
theorem spectralSpace_points_of_isQuasiCompactSpace_isAbsolutelyQuasiSeparated
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X) :
    SpectralSpace (points B S hS X) :=
  have hdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hqs
  have : CompactSpace (points B S hS X) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).mp hqc
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdec
  have : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdec
  have : QuasiSeparatedSpace (points B S hS X) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS X hX hqs
  have : PrespectralSpace (points B S hS X) := prespectralSpace_points B S hS X hX
  SpectralSpace.mk

end AlgebraicGeometry.Space

end
