module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The small étale topos inside a big étale topos

For a morphism `f : T ⟶ S` in a big étale site, postcomposition with `f` sends the small étale
category of `T` into the big étale category over `S`. This functor is both continuous and
cocontinuous, so it induces a morphism of topoi

`i_f : Sh(T_ét) ⟶ Sh((Sch/S)_ét)`

whose inverse image is simply restriction along the functor. Because the functor also preserves
fibre products and equalizers, the inverse image has in addition a *left* adjoint `i_{f,!}`,
itself left exact.

## Main definitions

* `AlgebraicGeometry.smallEtaleToBigEtaleFunctor` — postcomposition with `f`.
* `AlgebraicGeometry.smallEtaleToBigEtaleMorphism` — the induced morphism of topoi.
* `AlgebraicGeometry.smallEtaleToBigEtaleLowerShriek` — the left adjoint of inverse image.

## Main results

* `AlgebraicGeometry.smallEtaleToBigEtaleFunctor_isCocontinuous` and
  `AlgebraicGeometry.smallEtaleToBigEtaleFunctor_isContinuous` — the functor is cocontinuous
  and continuous.
* `CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` — the formula
  identifying inverse image with restriction.
* `AlgebraicGeometry.smallEtaleToBigEtaleLowerShriekAdjunction` — the lower-shriek adjunction;
  the two preservation instances following it give its left exactness.

## Implementation notes

The morphism of topoi is assembled from the general construction for a cocontinuous functor,
and continuity is recorded separately because it is what identifies inverse image with
restriction and what makes the lower shriek exist. The displayed formula on sections is then
the general isomorphism of inverse image with restriction along a functor that is both
continuous and cocontinuous; stating it that way retains naturality in both the sheaf and the
small étale object.

Cocontinuity is the substantive half. A covering of the image object pulls back to a covering
of the source because an object of the big étale category over `S` lying over an object of the
small étale category of `T` is itself étale over `T` — the structure morphisms compose, and
étale morphisms are closed under composition and cancellable on the left. The precoverage
identifications `*_precoverage_eq_comap` are what let this be checked at the level of
precoverages rather than of generated topologies, and the two injectivity lemmas for presieves
transported along the fully faithful inclusions are what make those identifications
well-posed.

Left exactness of the lower shriek comes from preservation of fibre products and equalizers by
the functor itself, which holds because the small étale category has a final object and fibre
products, and the slice forgetful functor preserves connected limits.

## References

* [Stacks Project, Lemma 34.4.3 (Tag 021F)](https://stacks.math.columbia.edu/tag/021F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 021F "the inverse-image formula"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

include f

/-- Send an étale object `U / T` to the composite `U / S`. -/
@[stacks 021F "the functor"]
public abbrev smallEtaleToBigEtaleFunctor :
    SmallEtale B T.obj T.property ⥤ BigEtaleOver B S.obj S.property :=
  SmallEtale.inclusion B T.obj T.property ⋙ Over.map f

private instance smallEtale_hasBinaryProducts :
    HasBinaryProducts (SmallEtale B T.obj T.property) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

private instance smallEtale_hasEqualizers :
    HasEqualizers (SmallEtale B T.obj T.property) :=
  hasEqualizers_of_hasPullbacks_and_binary_products

private instance smallEtaleInclusion_preservesTerminalShape :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SmallEtale.inclusion B T.obj T.property) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

private instance smallEtaleInclusion_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (SmallEtale.inclusion B T.obj T.property) :=
  preservesBinaryProducts_of_preservesTerminal_and_pullbacks _

private instance smallEtaleInclusion_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (SmallEtale.inclusion B T.obj T.property) :=
  preservesEqualizers_of_preservesPullbacks_and_binaryProducts _

private instance overMap_preservesLimitsOfConnectedShape
    (I : Type*) [SmallCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over (B.obj T.obj T.property))]
    [HasLimitsOfShape I (Over (B.obj S.obj S.property))] :
    PreservesLimitsOfShape I (Over.map f) := by
  have h : PreservesLimitsOfShape I
      ((Over.map f) ⋙ Over.forget (B.obj S.obj S.property)) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (Over.forget (B.obj S.obj S.property))

private instance smallEtaleToBigEtale_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallEtaleToBigEtaleFunctor B T S f) :=
  inferInstance

private instance smallEtaleToBigEtale_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (smallEtaleToBigEtaleFunctor B T S f) :=
  inferInstance

private theorem smallEtaleToBigEtale_maps_precoverage
    {X : SmallEtale B T.obj T.property} {R : Presieve X}
    (hR : R ∈ SmallEtale.precoverage B T.obj T.property X) :
    R.map (smallEtaleToBigEtaleFunctor B T S f) ∈
      BigEtaleOver.precoverage B S.obj S.property
        ((smallEtaleToBigEtaleFunctor B T S f).obj X) := by
  rw [SmallEtale.mem_precoverage_iff] at hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [BigEtaleOver.mem_precoverage_iff]
  refine ⟨E.map (smallEtaleToBigEtaleFunctor B T S f),
    (PreZeroHypercover.presieve₀_map
      (F := smallEtaleToBigEtaleFunctor B T S f) E).symm, ?_⟩
  have hbase :
      smallEtaleToBigEtaleFunctor B T S f ⋙ Over.forget (B.obj S.obj S.property) =
        SmallEtale.inclusion B T.obj T.property ⋙
          Over.forget (B.obj T.obj T.property) := by
    dsimp [smallEtaleToBigEtaleFunctor]
    rw [Functor.assoc, Over.mapForget_eq]
  show B.IsCovering ⟨
    (smallEtaleToBigEtaleFunctor B T S f ⋙ Over.forget (B.obj S.obj S.property)).obj X,
    E.map (smallEtaleToBigEtaleFunctor B T S f ⋙
      Over.forget (B.obj S.obj S.property))⟩
  change B.IsCovering ⟨
    (SmallEtale.inclusion B T.obj T.property ⋙
      Over.forget (B.obj T.obj T.property)).obj X,
    E.map (SmallEtale.inclusion B T.obj T.property ⋙
      Over.forget (B.obj T.obj T.property))⟩ at hE
  rwa [hbase]

/-- A covering family of the image of `X` in the big étale site over `S`, viewed as a family
in the small étale site of `T` with the same index set and the same arrows. -/
public def smallEtaleCoveringLift {X : SmallEtale B T.obj T.property}
    (E : PreZeroHypercover.{u + 1} ((smallEtaleToBigEtaleFunctor B T S f).obj X))
    (hE : BigEtaleOver.IsCovering B S.obj S.property ⟨_, E⟩) :
    PreZeroHypercover.{u + 1} X :=
  ⟨E.I₀, fun i => ⟨Over.mk ((E.f i).left ≫ X.obj.hom), by
      change B.IsCovering _ at hE
      have hcover := AlgebraicGeometry.BigEtaleSite.IsCovering.etale hE
      change (E.map (BigEtaleOver.toScheme B S.obj S.property)).presieve₀ ∈
        Scheme.jointlySurjectivePrecoverage _ ∧
          (E.map (BigEtaleOver.toScheme B S.obj S.property)).presieve₀ ∈
            (MorphismProperty.precoverage @Etale) _ at hcover
      change Etale (B.inclusion.map ((E.f i).left ≫ X.obj.hom))
      have hEtale : Etale ((BigEtaleOver.toScheme B S.obj S.property).map (E.f i)) :=
        (MorphismProperty.ofArrows_mem_precoverage.mp hcover.2) i
      have : Etale (B.inclusion.map (E.f i).left) := by
        simpa [BigEtaleOver.toScheme] using hEtale
      have : Etale (B.inclusion.map X.obj.hom) := X.property
      rw [Functor.map_comp]
      infer_instance⟩,
    fun i => CategoryTheory.ObjectProperty.homMk (Over.homMk (E.f i).left rfl)⟩

/-- The objects of `smallEtaleCoveringLift` map back to the objects of the original family. -/
public theorem smallEtaleToBigEtaleFunctor_obj_smallEtaleCoveringLift
    {X : SmallEtale B T.obj T.property}
    (E : PreZeroHypercover.{u + 1} ((smallEtaleToBigEtaleFunctor B T S f).obj X))
    (hE : BigEtaleOver.IsCovering B S.obj S.property ⟨_, E⟩) (i : E.I₀) :
    (smallEtaleToBigEtaleFunctor B T S f).obj
      ((smallEtaleCoveringLift B T S f E hE).X i) = E.X i := by
  apply CostructuredArrow.obj_ext
    ((smallEtaleToBigEtaleFunctor B T S f).obj ((smallEtaleCoveringLift B T S f E hE).X i))
    (E.X i) rfl
  show (E.X i).hom = ((E.f i).left ≫ X.obj.hom) ≫ f
  simpa [Category.assoc] using (Over.w (E.f i)).symm

/-- The lift of a big étale covering family is a small étale covering family. -/
public theorem smallEtaleCoveringLift_isCovering {X : SmallEtale B T.obj T.property}
    (E : PreZeroHypercover.{u + 1} ((smallEtaleToBigEtaleFunctor B T S f).obj X))
    (hE : BigEtaleOver.IsCovering B S.obj S.property ⟨_, E⟩) :
    SmallEtale.IsCovering B T.obj T.property ⟨X, smallEtaleCoveringLift B T S f E hE⟩ := by
  show B.IsCovering
    ⟨(Over.forget (B.obj T.obj T.property)).obj X.obj,
      (smallEtaleCoveringLift B T S f E hE).map (SmallEtale.inclusion B T.obj T.property ⋙
        Over.forget (B.obj T.obj T.property))⟩
  have hfamilies :
      (smallEtaleCoveringLift B T S f E hE).map (SmallEtale.inclusion B T.obj T.property ⋙
        Over.forget (B.obj T.obj T.property)) =
      E.map (Over.forget (B.obj S.obj S.property)) := by
    ext <;> rfl
  rwa [hfamilies]

/-- Postcomposition from the small étale site of `T` to the big étale site over `S`
is cocontinuous. -/
@[stacks 021F "cocontinuity"]
public instance smallEtaleToBigEtaleFunctor_isCocontinuous :
    (smallEtaleToBigEtaleFunctor B T S f).IsCocontinuous
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property) := by
  refine ⟨fun {X R} hR => ?_⟩
  change R ∈ (BigEtaleOver.precoverage B S.obj S.property).toGrothendieck
    ((smallEtaleToBigEtaleFunctor B T S f).obj X) at hR
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨Q, hQ, hQR⟩ := hR
  rw [BigEtaleOver.mem_precoverage_iff] at hQ
  obtain ⟨E, hQE, hE⟩ := hQ
  have hER : E.presieve₀ ≤ R := by simpa [hQE] using hQR
  let E' := smallEtaleCoveringLift B T S f E hE
  have hobj := smallEtaleToBigEtaleFunctor_obj_smallEtaleCoveringLift B T S f E hE
  have hE'pre : E'.presieve₀ ∈ SmallEtale.precoverage B T.obj T.property X :=
    (SmallEtale.mem_precoverage_iff B T.obj T.property).mpr
      ⟨E', rfl, smallEtaleCoveringLift_isCovering B T S f E hE⟩
  apply (SmallEtale.topology B T.obj T.property).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hE'pre)
  rw [Sieve.generate_le_iff]
  intro Y g hg
  have hi : R ((smallEtaleToBigEtaleFunctor B T S f).map (E'.f hg.idx)) := by
    have hmap : (smallEtaleToBigEtaleFunctor B T S f).map (E'.f hg.idx) =
        eqToHom (hobj (hg.idx)) ≫ E.f (hg.idx) := by
      have hleft :
          ((smallEtaleToBigEtaleFunctor B T S f).obj (E'.X hg.idx)).left =
            (E.X hg.idx).left := rfl
      have hhomleft : (eqToHom (hobj hg.idx)).left = eqToHom hleft := by
        rw [Over.eqToHom_left]
      apply Over.OverMorphism.ext
      simp [Over.comp_left, hhomleft]
      rfl
    rw [hmap]
    exact R.downward_closed (hER _ _ (E.presieve₀_f hg.idx)) _
  change R ((smallEtaleToBigEtaleFunctor B T S f).map g)
  rw [Presieve.ofArrows.eq_eqToHom_comp_hom_idx hg, Functor.map_comp]
  exact R.downward_closed hi _

/-- Postcomposition also preserves coverings and fibre products, hence is continuous. -/
@[stacks 021F "continuity"]
public instance smallEtaleToBigEtaleFunctor_isContinuous :
    (smallEtaleToBigEtaleFunctor B T S f).IsContinuous
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  exact fun _ _ hR => smallEtaleToBigEtale_maps_precoverage B T S f hR

/-- The geometric morphism `i_f : Sh(Tₑₜ) ⟶ Sh((Sch/S)ₑₜ)` induced by
postcomposition. -/
@[stacks 021F "the morphism of topoi"]
public noncomputable def smallEtaleToBigEtaleMorphism :
    MorphismOfTopoi
      (Sheaf (SmallEtale.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigEtaleOver.topology B S.obj S.property) (Type (u + 1))) :=
  { pushforward := (smallEtaleToBigEtaleFunctor B T S f).sheafPushforwardCocontinuous
      (Type (u + 1)) (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)
    inverseImage := (smallEtaleToBigEtaleFunctor B T S f).sheafPullbackCocontinuous
      (Type (u + 1)) (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)
    adj := (smallEtaleToBigEtaleFunctor B T S f).sheafAdjunctionPullbackCocontinuous
      (Type (u + 1)) (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)
    preservesFiniteLimits := by infer_instance }

/-- The left adjoint `i_{f,!}` of inverse image. -/
public noncomputable abbrev smallEtaleToBigEtaleLowerShriek :
    Sheaf (SmallEtale.topology B T.obj T.property) (Type (u + 1)) ⥤
      Sheaf (BigEtaleOver.topology B S.obj S.property) (Type (u + 1)) :=
  (smallEtaleToBigEtaleFunctor B T S f).sheafPullback (Type (u + 1))
    (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)

/-- The lower shriek is left adjoint to inverse image. -/
@[stacks 021F "existence of lower shriek"]
public noncomputable def smallEtaleToBigEtaleLowerShriekAdjunction :
    smallEtaleToBigEtaleLowerShriek B T S f ⊣
      (smallEtaleToBigEtaleMorphism B T S f).inverseImage :=
  (((smallEtaleToBigEtaleFunctor B T S f).sheafAdjunctionLowerShriek
      (Type (u + 1)) (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)).ofNatIsoLeft
        (Functor.sheafPullbackConstruction.sheafPullbackIso
          (smallEtaleToBigEtaleFunctor B T S f) (Type (u + 1))
          (SmallEtale.topology B T.obj T.property)
          (BigEtaleOver.topology B S.obj S.property)).symm).ofNatIsoRight
    ((smallEtaleToBigEtaleFunctor B T S f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)).symm

/-- The lower shriek preserves fibre products. -/
@[stacks 021F "lower shriek preserves fibre products"]
public instance smallEtaleToBigEtaleLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      (smallEtaleToBigEtaleLowerShriek B T S f) :=
  Functor.preservesLimitsOfShape_sheafPullback (smallEtaleToBigEtaleFunctor B T S f)
    (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property) (I := WalkingCospan)

/-- The lower shriek preserves equalizers. -/
@[stacks 021F "lower shriek preserves equalizers"]
public instance smallEtaleToBigEtaleLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (smallEtaleToBigEtaleLowerShriek B T S f) :=
  Functor.preservesLimitsOfShape_sheafPullback (smallEtaleToBigEtaleFunctor B T S f)
    (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property) (I := WalkingParallelPair)

end AlgebraicGeometry
