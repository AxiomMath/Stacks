module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitenessFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.LocalModel

/-!
# The projection of a vector bundle on an algebraic space

Let `W` be an algebraic space over a scheme `S` in a big fppf site and `ℰ` a finite locally free
`𝒪_W`-module, with vector bundle `p : E = \underline{Spec}_W(Sym(ℰ)) ⟶ W`. Étale locally on `W`
the projection is the structure morphism of affine space `𝐀^n_V ⟶ V`
(`AlgebraicGeometry.Space.isPullback_vectorBundleChart`), and the affine charts trivializing `ℰ`
form an étale covering of `W`. So every property of morphisms of schemes which holds for the
projections of affine spaces, is étale local on the source and target, and whose chart form is
local on the base for the fpqc topology, holds for `p`: this gives that `p` is flat and locally
of finite type. The relative dimension of `p` is read pointwise through the cartesian squares
over the charts (Stacks 04NS): it is `r` when `ℰ` has rank `r`.

## Main results

* `AlgebraicGeometry.Space.isEtaleCovering_trivializingAffineCharts`: the affine charts on which
  `ℰ` is free of finite rank form an étale covering of `W`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_vectorBundleProjection`: the transfer
  principle above.
* `AlgebraicGeometry.Space.isFlat_vectorBundleProjection`: `p` is flat.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_vectorBundleProjection`: `p` is locally of
  finite type.
* `AlgebraicGeometry.Space.hasRelativeDimension_vectorBundleProjection`: for `ℰ` of rank `r`,
  `p` has relative dimension `r`.
* `AlgebraicGeometry.Space.isGood_vectorBundle`: in the situation of Stacks 0EDT, the vector
  bundle of a finite locally free module on a good algebraic space is good.

## References

* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 041S](https://stacks.math.columbia.edu/tag/041S)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]

/-- The affine étale charts of `W` on which `ℰ` is free on a finite type. -/
abbrev TrivializingAffineChart : Type (u + 1) :=
  {V : SmallEtale B S hS W.1 // IsAffine (chartScheme V) ∧ ∃ (ι : Type u) (_ : Finite ι),
    Nonempty (F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)}

/-- **The affine charts trivializing `ℰ` form an étale covering of `W`.** -/
theorem isEtaleCovering_trivializingAffineCharts :
    IsEtaleCovering B S hS (fun V : TrivializingAffineChart B S hS W F => yoneda.obj V.1.obj.left)
      (fun V => V.1.obj.hom) where
  target_isAlgebraicSpace := W.2
  source_isAlgebraicSpace V := isAlgebraicSpace_yoneda B S hS _
  etale V := isEtale_of_presheaf_etale B S hS V.1.property
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨V, ι, hι, e, z, hV, rfl⟩ := exists_trivializing_affine_chart B S hS W F x
    exact Set.mem_iUnion.2 ⟨⟨V, hV, ι, hι, ⟨e⟩⟩,
      (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS W.1).obj V)).symm z,
      (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS W.1 V z).symm⟩

/-- **A property of the projections of affine spaces holds for the projection of a vector
bundle**, when it is étale local on the source and target and its chart form is local on the
base for the fpqc topology. -/
theorem holdsOnEveryEtaleChart_vectorBundleProjection (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, u + 1} .fpqc B S hS)]
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hA : ∀ (T : Scheme.{u}) (n : Type u) [Finite n], P (𝔸(n; T) ↘ T)) :
    HoldsOnEveryEtaleChart B S hS P (vectorBundleProjection B S hS W F).hom := by
  classical
  have _ := IsEtaleLocalOnSourceAndTarget.respectsIso P hP
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃X Y⦄ (f : X ⟶ Y) => HoldsOnEveryEtaleChart B S hS P f.hom
  let Yi : TrivializingAffineChart B S hS W F → AlgebraicSpaces B S hS :=
    fun V => ⟨yoneda.obj V.1.obj.left, isAlgebraicSpace_yoneda B S hS _⟩
  let g : ∀ V, Yi V ⟶ W := fun V => ObjectProperty.homMk V.1.obj.hom
  have hR : Presieve.ofArrows Yi g ∈ (Topology.precoverage.{u, u + 1} .fpqc B S hS).coverings W :=
    ⟨_, Yi, g, rfl, W.2, fun V => (Yi V).2,
      isFpqcCovering_of_isEtaleCovering B S hS _ _
        (isEtaleCovering_trivializingAffineCharts B S hS W F)⟩
  change Q (vectorBundleProjection B S hS W F)
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := Q) hR ?_
  intro U k _ hk
  obtain ⟨V⟩ := hk
  obtain ⟨V, hV, ι, hι, ⟨e⟩⟩ := V
  have : IsAffine (chartScheme V) := hV
  have hsq := AlgebraicSpaces.isPullback_hom B S hS
    (IsPullback.of_hasPullback (vectorBundleProjection B S hS W F) (g ⟨V, hV, ι, hι, ⟨e⟩⟩))
  have sq := isPullback_vectorBundleChart B S hS W F V
  change HoldsOnEveryEtaleChart B S hS P
    (pullback.snd (vectorBundleProjection B S hS W F) (g ⟨V, hV, ι, hι, ⟨e⟩⟩)).hom
  rw [← hsq.isoIsPullback_hom_snd _ _ sq]
  have _ := holdsOnEveryEtaleChart_respectsIso_presheaf B S hS P
  refine (MorphismProperty.cancel_left_of_respectsIso
    (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
      HoldsOnEveryEtaleChart B S hS P f) _ _).2 ?_
  refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP _).2 ?_
  rw [← vectorBundleChartIso_hom_over B S hS W F V e (Equiv.refl ι)]
  exact (P.cancel_left_of_respectsIso _ _).2 (hA _ ι)

/-- **The projection of a vector bundle is flat.** -/
theorem isFlat_vectorBundleProjection :
    IsFlat B S hS (vectorBundleProjection B S hS W F).hom :=
  holdsOnEveryEtaleChart_vectorBundleProjection B S hS W F (@Flat)
    Flat.isEtaleLocalOnSourceAndTarget fun T n _ => flat_affineSpace n T

/-- **The projection of a vector bundle is locally of finite type.** -/
theorem isLocallyOfFiniteType_vectorBundleProjection :
    IsLocallyOfFiniteType B S hS (vectorBundleProjection B S hS W F).hom :=
  holdsOnEveryEtaleChart_vectorBundleProjection B S hS W F (@LocallyOfFiniteType)
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget fun _ _ _ => inferInstance

/-- **The projection of the vector bundle of a finite locally free module of rank `r` has
relative dimension `r`.** At a point of `E`, choose an affine chart `V` trivializing `ℰ` through
its image; by Stacks 04NS the relative dimension there is that of `𝐀^r_V ⟶ V`, which is `r`. -/
theorem hasRelativeDimension_vectorBundleProjection (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r] :
    HasRelativeDimension r B S hS (vectorBundleProjection B S hS W F).hom := by
  classical
  intro x
  obtain ⟨V, ι, hι, e, ε, z, hV, hz⟩ := exists_trivializing_affine_chart_of_rank B S hS W F r
    (pointsMap B S hS _ (vectorBundleProjection B S hS W F).hom x)
  have : IsAffine (chartScheme V) := hV
  have sq := (isPullback_vectorBundleChart B S hS W F V).flip
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm] at hz
  obtain ⟨w, -, rfl⟩ := exists_point_of_isPullback_presheaf B S hS sq _ x hz
  refine (hasRelativeDimensionAt_iff_of_isPullback' B S hS r sq
    (vectorBundle B S hS W F).obj.left.2 W.2 (isAlgebraicSpace_yoneda B S hS _)
    (isLocallyOfFiniteType_vectorBundleProjection B S hS W F) w).1 ?_
  -- the relative dimension of the chart morphism `𝐀^r_V ⟶ V`
  let T := BigFppfOver.toScheme B S hS
  let h := vectorBundleChartHom B S hS W F V
  let ε' : ι ≃ ULift.{u} (Fin r) := ε.trans Equiv.ulift.symm
  have hP : locallyOfFiniteTypeRelativeDimension.{u} r (T.map h) := by
    rw [← vectorBundleChartIso_hom_over B S hS W F V e ε']
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
      ⟨inferInstance, Stacks.Chow.relativeDimension_affineSpaceOver (chartScheme V) r⟩
  obtain ⟨hft, hdim⟩ := hP
  obtain ⟨u, rfl⟩ := (pointsEquivScheme B S hS (vectorBundleChart B S hS W F V)).symm.surjective w
  have key := hasRelativeDimensionAt_pointsMap_iff B S hS (r : ℕ∞) (yoneda.map h)
    (vectorBundleChart B S hS W F V) V.obj.left (yoneda.map (𝟙 _)) (yoneda.map (𝟙 _)) h
    (presheaf_yoneda_map_id_etale B S hS _) (presheaf_yoneda_map_id_etale B S hS _)
    (by simp) u
  rw [CategoryTheory.Functor.map_id, pointsMap_id] at key
  refine key.2 ?_
  exact_mod_cast
    (AlgebraicGeometry.relativeDimension_iff_forall_topologicalKrullDimAt (T.map h) r).1 hdim u

/-- **The vector bundle of a finite locally free module on a good algebraic space is good.** In
the situation of Stacks 0EDT, if `W/B` is good then so is `E/B`, with structure morphism
`E ⟶ W ⟶ B`: the projection is affine, hence quasi-separated, and locally of finite type, and
both properties are stable under composition. -/
theorem isGood_vectorBundle (D : BaseSpaceDimensionSituation.{u})
    (W : AlgebraicSpaces D.site D.base D.base_mem)
    (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] (sW : W.1 ⟶ D.space)
    (hW : D.IsGood sW) :
    D.IsGood ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW) := by
  have hE := (vectorBundle D.site D.base D.base_mem W F).obj.left.2
  refine ⟨hE, ?_, ?_⟩
  · exact isQuasiSeparated_comp D.site D.base D.base_mem hE W.2 _ sW
      (isQuasiSeparated_of_isAffineHom D.site D.base D.base_mem _ hE W.2
        (isAffineHom_vectorBundleProjection D.site D.base D.base_mem W F)) hW.2.1
  · exact isLocallyOfFiniteType_comp D.site D.base D.base_mem hE W.2 D.isAlgebraicSpace _ sW
      (isLocallyOfFiniteType_vectorBundleProjection D.site D.base D.base_mem W F) hW.2.2

end AlgebraicGeometry.Space

end
