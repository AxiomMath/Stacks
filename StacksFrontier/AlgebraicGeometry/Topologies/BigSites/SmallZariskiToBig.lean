module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Precoverage
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The small Zariski topos of a scheme inside a big Zariski topos

For a morphism `f : T ⟶ S` in a big Zariski site, postcomposition with `f` carries the small
Zariski site of `T` into the big Zariski site over `S`. That functor is both continuous and
cocontinuous, so it induces a morphism of topoi

`i_f : Sh(T_Zar) ⟶ Sh((Sch/S)_Zar)`

whose inverse image is restriction — `(i_f⁻¹ 𝒢)(U/T) = 𝒢(U/S)` — and which in addition admits
a left adjoint `i_{f,!}` to its inverse image, left exact in the sense that it preserves fibre
products and equalizers.

## Main definitions

* `AlgebraicGeometry.smallZariskiToBigZariskiFunctor` — postcomposition with `f`.
* `AlgebraicGeometry.smallZariskiToBigZariskiMorphism` — the induced morphism of topoi `i_f`.
* `AlgebraicGeometry.smallZariskiToBigZariskiLowerShriek` — the left adjoint `i_{f,!}`.

## Main results

* `AlgebraicGeometry.smallZariskiToBigZariskiFunctor_isCocontinuous` and
  `AlgebraicGeometry.smallZariskiToBigZariskiFunctor_isContinuous` are the two site-level
  properties of the functor.
* `AlgebraicGeometry.smallZariskiToBigZariskiLowerShriekAdjunction` is the lower-shriek
  adjunction, and the two `preserves` instances are its left exactness.

## Implementation notes

The formula for the inverse image is not restated here: having both continuity and
cocontinuity, the general comparison
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` identifies the
inverse image of `i_f` with plain restriction along the functor, simultaneously for all sheaves
and all small-site objects, which is what the source's formula on sections says.

Cocontinuity is the one statement that has to be proved by hand: a covering family of the big
site at an object coming from the small site consists of open immersions, and each of its
members is again an open subscheme of `T`, so the family is already a covering family of the
small site. Continuity is cover preservation together with preservation of fibre products, and
both come from the fact that postcomposition and the small-site inclusion induce the same
family of schemes.

## References

* [Stacks Project, Tag 020Y](https://stacks.math.columbia.edu/tag/020Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


add_to_stacks 020Y "the inverse-image formula"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous

variable (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

include f

private instance smallZariski_hasTerminal : HasTerminal (SmallZariski B T.obj T.property) :=
  (SmallZariski.finalIsTerminal B T.obj T.property).hasTerminal

private instance smallZariski_hasBinaryProducts :
    HasBinaryProducts (SmallZariski B T.obj T.property) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

private instance smallZariski_hasEqualizers : HasEqualizers (SmallZariski B T.obj T.property) :=
  hasEqualizers_of_hasPullbacks_and_binary_products

private instance smallZariskiInclusion_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (SmallZariski.inclusion B T.obj T.property) :=
  preservesBinaryProducts_of_preservesTerminal_and_pullbacks _

private instance smallZariskiInclusion_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (SmallZariski.inclusion B T.obj T.property) :=
  have : HasBinaryProducts (BigZariskiOver B T.obj T.property) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  preservesEqualizers_of_preservesPullbacks_and_binaryProducts _

private instance overMap_preservesLimitsOfConnectedShape
    (I : Type*) [SmallCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over (⟨T.obj, T.property⟩ : B.Schemes))]
    [HasLimitsOfShape I (Over (⟨S.obj, S.property⟩ : B.Schemes))] :
    PreservesLimitsOfShape I (Over.map f) := by
  have h : PreservesLimitsOfShape I
      ((Over.map f) ⋙ Over.forget (⟨S.obj, S.property⟩ : B.Schemes)) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (Over.forget (⟨S.obj, S.property⟩ : B.Schemes))

/-- Send an open immersion `U ⟶ T` to the composite `U ⟶ S`. -/
@[stacks 020Y "the functor"]
public abbrev smallZariskiToBigZariskiFunctor :
    SmallZariski B T.obj T.property ⥤ BigZariskiOver B S.obj S.property :=
  SmallZariski.inclusion B T.obj T.property ⋙ Over.map f

private instance smallZariskiToBigZariskiFunctor_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallZariskiToBigZariskiFunctor B T S f) := by
  dsimp [smallZariskiToBigZariskiFunctor]
  infer_instance

private instance smallZariskiToBigZariskiFunctor_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (smallZariskiToBigZariskiFunctor B T S f) := by
  dsimp [smallZariskiToBigZariskiFunctor]
  infer_instance

/-- Postcomposition from the small Zariski site is cocontinuous. -/
@[stacks 020Y "cocontinuity"]
public instance smallZariskiToBigZariskiFunctor_isCocontinuous :
    (smallZariskiToBigZariskiFunctor B T S f).IsCocontinuous
      (SmallZariski.topology B T.obj T.property)
      (BigZariskiOver.topology B S.obj S.property) := by
  refine ⟨?_⟩
  intro X R hR
  change R ∈ (BigZariskiOver.precoverage B S.obj S.property).toGrothendieck
    ((smallZariskiToBigZariskiFunctor B T S f).obj X) at hR
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨Q, hQ, hQR⟩ := hR
  obtain ⟨E, hQE, hE⟩ := (BigZariskiOver.mem_precoverage_iff _ _ _).1 hQ
  have hER : E.presieve₀ ≤ R := by simpa [hQE] using hQR
  let E' : PreZeroHypercover.{u + 1} X :=
    ⟨E.I₀, fun i => ⟨Over.mk ((E.f i).left ≫ X.obj.hom), by
      change IsOpenImmersion (B.inclusion.map ((E.f i).left ≫ X.obj.hom))
      have hEi : IsOpenImmersion (B.inclusion.map (E.f i).left) := by
        have hZ : IsZariskiCovering
            ⟨(Over.forget (⟨S.obj, S.property⟩ : B.Schemes)).obj
                ((smallZariskiToBigZariskiFunctor B T S f).obj X),
              E.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes))⟩ := hE.1
        change
          (E.map (BigZariskiOver.toScheme B S.obj S.property)).presieve₀ ∈
            Scheme.zariskiPretopology
              ((BigZariskiOver.toScheme B S.obj S.property).obj
                ((smallZariskiToBigZariskiFunctor B T S f).obj X)) at hZ
        exact hZ.2 ((E.map (BigZariskiOver.toScheme B S.obj S.property)).presieve₀_f i)
      have hX : IsOpenImmersion (B.inclusion.map X.obj.hom) := X.property
      rw [Functor.map_comp]
      infer_instance⟩,
      fun i => CategoryTheory.ObjectProperty.homMk (Over.homMk (E.f i).left rfl)⟩
  have hobj (i : E.I₀) :
      (smallZariskiToBigZariskiFunctor B T S f).obj (E'.X i) = E.X i := by
    apply CostructuredArrow.obj_ext
      ((smallZariskiToBigZariskiFunctor B T S f).obj (E'.X i)) (E.X i) rfl
    change (E.X i).hom = ((E.f i).left ≫ X.obj.hom) ≫ f
    simpa [Category.assoc] using (Over.w (E.f i)).symm
  have hcover' : SmallZariski.IsCovering B T.obj T.property ⟨X, E'⟩ := by
    change B.IsCovering
      ⟨(Over.forget (⟨T.obj, T.property⟩ : B.Schemes)).obj X.obj,
        E'.map (SmallZariski.inclusion B T.obj T.property ⋙
          Over.forget (⟨T.obj, T.property⟩ : B.Schemes))⟩
    have hfamilies :
        E'.map (SmallZariski.inclusion B T.obj T.property ⋙
          Over.forget (⟨T.obj, T.property⟩ : B.Schemes)) =
        E.map (Over.forget (⟨S.obj, S.property⟩ : B.Schemes)) := by
      ext <;> rfl
    rwa [hfamilies]
  apply (SmallZariski.topology B T.obj T.property).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck
      ((SmallZariski.mem_precoverage_iff B T.obj T.property).2 ⟨E', rfl, hcover'⟩))
  rw [Sieve.generate_le_iff]
  intro Y g hg
  have hi : R ((smallZariskiToBigZariskiFunctor B T S f).map (E'.f hg.idx)) := by
    have hmap : (smallZariskiToBigZariskiFunctor B T S f).map (E'.f hg.idx) =
        eqToHom (hobj (hg.idx)) ≫ E.f (hg.idx) := by
      have hleft :
          ((smallZariskiToBigZariskiFunctor B T S f).obj (E'.X hg.idx)).left =
            (E.X hg.idx).left := rfl
      have hhomleft : (eqToHom (hobj hg.idx)).left = eqToHom hleft := by
        rw [Over.eqToHom_left]
      apply Over.OverMorphism.ext
      simp [Over.comp_left, hhomleft]
      rfl
    rw [hmap]
    exact R.downward_closed (hER _ _ (E.presieve₀_f hg.idx)) _
  change R ((smallZariskiToBigZariskiFunctor B T S f).map g)
  rw [Presieve.ofArrows.eq_eqToHom_comp_hom_idx hg, Functor.map_comp]
  exact R.downward_closed hi _

/-- Postcomposition preserves coverings and fibre products, hence is continuous. -/
@[stacks 020Y "continuity"]
public instance smallZariskiToBigZariskiFunctor_isContinuous :
    (smallZariskiToBigZariskiFunctor B T S f).IsContinuous
      (SmallZariski.topology B T.obj T.property)
      (BigZariskiOver.topology B S.obj S.property) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  intro X R hR
  rw [SmallZariski.mem_precoverage_iff] at hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [Precoverage.mem_comap_iff, BigZariskiOver.mem_precoverage_iff]
  refine ⟨E.map (smallZariskiToBigZariskiFunctor B T S f),
    (PreZeroHypercover.presieve₀_map
      (F := smallZariskiToBigZariskiFunctor B T S f) E).symm, ?_⟩
  have hbase :
      smallZariskiToBigZariskiFunctor B T S f ⋙ Over.forget (⟨S.obj, S.property⟩ : B.Schemes) =
        SmallZariski.inclusion B T.obj T.property ⋙
          Over.forget (⟨T.obj, T.property⟩ : B.Schemes) := by
    dsimp [smallZariskiToBigZariskiFunctor]
    rw [Functor.assoc, Over.mapForget_eq]
  change B.IsCovering ⟨
    (smallZariskiToBigZariskiFunctor B T S f ⋙
      Over.forget (⟨S.obj, S.property⟩ : B.Schemes)).obj X,
    E.map (smallZariskiToBigZariskiFunctor B T S f ⋙
      Over.forget (⟨S.obj, S.property⟩ : B.Schemes))⟩
  change B.IsCovering ⟨
    (SmallZariski.inclusion B T.obj T.property ⋙
      Over.forget (⟨T.obj, T.property⟩ : B.Schemes)).obj X,
    E.map (SmallZariski.inclusion B T.obj T.property ⋙
      Over.forget (⟨T.obj, T.property⟩ : B.Schemes))⟩ at hE
  rwa [hbase]

/-- The geometric morphism `i_f : Sh(T_Zar) ⟶ Sh((Sch/S)_Zar)`. -/
@[stacks 020Y "the morphism of topoi"]
public noncomputable def smallZariskiToBigZariskiMorphism :
    MorphismOfTopoi
      (Sheaf (SmallZariski.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigZariskiOver.topology B S.obj S.property) (Type (u + 1))) :=
  { pushforward := (smallZariskiToBigZariskiFunctor B T S f).sheafPushforwardCocontinuous
      (Type (u + 1)) (SmallZariski.topology B T.obj T.property)
      (BigZariskiOver.topology B S.obj S.property)
    inverseImage := (smallZariskiToBigZariskiFunctor B T S f).sheafPullbackCocontinuous
      (Type (u + 1)) (SmallZariski.topology B T.obj T.property)
      (BigZariskiOver.topology B S.obj S.property)
    adj := (smallZariskiToBigZariskiFunctor B T S f).sheafAdjunctionPullbackCocontinuous
      (Type (u + 1)) (SmallZariski.topology B T.obj T.property)
      (BigZariskiOver.topology B S.obj S.property)
    preservesFiniteLimits := by infer_instance }

/-- The left adjoint `i_{f,!}` of inverse image. -/
public noncomputable abbrev smallZariskiToBigZariskiLowerShriek :
    Sheaf (SmallZariski.topology B T.obj T.property) (Type (u + 1)) ⥤
      Sheaf (BigZariskiOver.topology B S.obj S.property) (Type (u + 1)) :=
  (smallZariskiToBigZariskiFunctor B T S f).sheafPullback (Type (u + 1))
    (SmallZariski.topology B T.obj T.property)
    (BigZariskiOver.topology B S.obj S.property)

/-- Lower shriek is left adjoint to inverse image. -/
@[stacks 020Y "existence of lower shriek"]
public noncomputable def smallZariskiToBigZariskiLowerShriekAdjunction :
    smallZariskiToBigZariskiLowerShriek B T S f ⊣
      (smallZariskiToBigZariskiMorphism B T S f).inverseImage :=
  (((smallZariskiToBigZariskiFunctor B T S f).sheafAdjunctionLowerShriek
    (Type (u + 1)) (SmallZariski.topology B T.obj T.property)
    (BigZariskiOver.topology B S.obj S.property)).ofNatIsoLeft
      (Functor.sheafPullbackConstruction.sheafPullbackIso
        (smallZariskiToBigZariskiFunctor B T S f) (Type (u + 1))
        (SmallZariski.topology B T.obj T.property)
        (BigZariskiOver.topology B S.obj S.property)).symm).ofNatIsoRight
    (Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (smallZariskiToBigZariskiFunctor B T S f) (Type (u + 1))
      (SmallZariski.topology B T.obj T.property) (BigZariskiOver.topology B S.obj S.property)).symm

/-- Lower shriek preserves fibre products. -/
@[stacks 020Y "lower shriek preserves fibre products"]
public instance smallZariskiToBigZariskiLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      (smallZariskiToBigZariskiLowerShriek B T S f) :=
  Functor.preservesLimitsOfShape_sheafPullback
    (smallZariskiToBigZariskiFunctor B T S f)
    (SmallZariski.topology B T.obj T.property)
    (BigZariskiOver.topology B S.obj S.property) (I := WalkingCospan)

/-- Lower shriek preserves equalizers. -/
@[stacks 020Y "lower shriek preserves equalizers"]
public instance smallZariskiToBigZariskiLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (smallZariskiToBigZariskiLowerShriek B T S f) :=
  Functor.preservesLimitsOfShape_sheafPullback
    (smallZariskiToBigZariskiFunctor B T S f)
    (SmallZariski.topology B T.obj T.property)
    (BigZariskiOver.topology B S.obj S.property) (I := WalkingParallelPair)


end AlgebraicGeometry
