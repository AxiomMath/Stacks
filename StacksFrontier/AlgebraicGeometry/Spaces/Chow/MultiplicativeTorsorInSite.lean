module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraTrivialChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorSectionsBound
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorGenericCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberThroughPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOfRelativeDimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The multiplicative torsor of an invertible sheaf, inside the site

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module.  This file forms
the multiplicative torsor

`q : T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n}) ⟶ X`

as an algebraic space of the big fppf site of `X`, with no hypothesis beyond those of Situation
0EDT, and proves that `q` is affine, surjective and smooth of relative dimension one, the first
clause of Stacks 0EQG.

## Main definitions

* `AlgebraicGeometry.Space.torsorOfInvertible`: `T`, as an algebraic space affine over `X`.
* `AlgebraicGeometry.Space.torsorOfInvertibleSpace`,
  `AlgebraicGeometry.Space.torsorOfInvertibleProjection`: `T` and `q : T ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_trivializing_chart`: every point of `X` lies in the image
  of an affine étale chart trivializing `ℒ`.
* `AlgebraicGeometry.Space.isPullback_torsorOfInvertible_chart`: the base change of `q` to an
  affine chart `V` is `Spec 𝒜(V) ⟶ V`.
* `AlgebraicGeometry.Space.isAffineHom_torsorOfInvertibleProjection`,
  `AlgebraicGeometry.Space.isSurjective_torsorOfInvertibleProjection`,
  `AlgebraicGeometry.Space.isSmoothOfRelativeDimension_torsorOfInvertibleProjection`: `q` is
  affine, surjective and smooth of relative dimension one.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-! ### The torsor -/

/-- The multiplicative torsor `T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n})` of an invertible
`𝒪_X`-module, as an algebraic space affine over `X` in the big fppf site of `X`: the relative
spectrum (Stacks 081W) of the Laurent algebra of `ℒ`. -/
def torsorOfInvertible : AffineOver D.site D.base D.base_mem ⟨X, hp.1⟩ :=
  boundedRelativeSpec D.site D.base D.base_mem
    (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))
    (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL)

/-- The algebraic space `T` of the multiplicative torsor of `ℒ`. -/
abbrev torsorOfInvertibleSpace : AlgebraicSpaces D.site D.base D.base_mem :=
  (torsorOfInvertible D p hp L hL).obj.left

/-- The projection `q : T ⟶ X` of the multiplicative torsor of `ℒ`. -/
abbrev torsorOfInvertibleProjection :
    torsorOfInvertibleSpace D p hp L hL ⟶ ⟨X, hp.1⟩ :=
  (torsorOfInvertible D p hp L hL).obj.hom

/-- `q` is an affine morphism. -/
theorem isAffineHom_torsorOfInvertibleProjection :
    IsAffineHom D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL).hom :=
  (torsorOfInvertible D p hp L hL).property

/-! ### Trivializing charts -/

include hL in
/-- Every point of `X` lies in the image of an affine étale chart over which `ℒ` is trivial. -/
theorem exists_affine_trivializing_chart (x : points D.site D.base D.base_mem X) :
    ∃ V : SmallEtale D.site D.base D.base_mem X, IsAffine (chartScheme V) ∧
      Nonempty (L.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V)) ∧
      x ∈ Set.range (pointsMap D.site D.base D.base_mem
        (yoneda.obj ((SmallEtale.toOver D.site D.base D.base_mem X).obj V)) V.obj.hom) := by
  obtain ⟨I, W, hW, e⟩ := exists_trivializing_cover_laurent D p hp L hL
  obtain ⟨U, a, hs, he⟩ := hp.1.exists_atlas
  let Uc : SmallEtale D.site D.base D.base_mem X := ⟨CostructuredArrow.mk a, he⟩
  have hxU : x ∈ Set.range (pointsMap D.site D.base D.base_mem
      (yoneda.obj ((SmallEtale.toOver D.site D.base D.base_mem X).obj Uc)) Uc.obj.hom) :=
    surjective_pointsMap_of_presheaf_surjective D.site D.base D.base_mem a hs x
  rw [← range_chartSchemeToPoints D.site D.base D.base_mem ⟨X, hp.1⟩ Uc] at hxU
  obtain ⟨z, hz⟩ := hxU
  obtain ⟨Q, φ, ⟨i, ⟨ψ⟩⟩, hQ, w, hw⟩ := SmallEtale.exists_affine_mem_range_of_mem_topology
    D.site D.base D.base_mem X (hW Uc) z
  refine ⟨Q, hQ, ⟨(SheafOfModules.overMap _ ψ).mapIso (e i).some ≪≫
    SheafOfModules.overMapUnitIso ψ⟩, ?_⟩
  rw [← range_chartSchemeToPoints D.site D.base D.base_mem ⟨X, hp.1⟩ Q]
  exact ⟨w, (chartSchemeToPoints_map D.site D.base D.base_mem X φ w).symm.trans
    ((congrArg (chartSchemeToPoints D.site D.base D.base_mem X Uc) hw).trans hz)⟩

/-! ### The base change to an affine chart -/

section Chart

variable (V : SmallEtale D.site D.base D.base_mem X) [IsAffine (chartScheme V)]

/-- The morphism `Spec 𝒜(V) ⟶ T` over an affine chart `V`. -/
abbrev torsorOfInvertibleChartToSpace :
    yoneda.obj (affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
      (laurentAlgebraSheaf D p hp L hL) (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL) V) ⟶
      (torsorOfInvertibleSpace D p hp L hL).obj :=
  affineChartSpecToPoints D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
    (laurentAlgebraSheaf D p hp L hL) (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL) V
    (exists_chartEval_eq D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL) V)

/-- The morphism `Spec 𝒜(V) ⟶ V` of the site, over an affine chart `V`. -/
abbrev torsorOfInvertibleChartHom :
    affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
      (laurentAlgebraSheaf D p hp L hL) (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL) V ⟶
      V.obj.left :=
  affineChartSpecHom D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
    (laurentAlgebraSheaf D p hp L hL) (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL) V

/-- The base change of `q : T ⟶ X` to an affine étale chart `V` is `Spec 𝒜(V) ⟶ V`. -/
theorem isPullback_torsorOfInvertible_chart :
    IsPullback (torsorOfInvertibleChartToSpace D p hp L hL V)
      (yoneda.map (torsorOfInvertibleChartHom D p hp L hL V))
      (torsorOfInvertibleProjection D p hp L hL).hom V.obj.hom :=
  isPullback_affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _ _ V
    (injective_chartEval_of_isAffine D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL) V)
    (exists_chartEval_eq D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL) V)

/-- The base change of `q` to an affine chart, as a cartesian square of algebraic spaces. -/
theorem isPullback_torsorOfInvertible_chart_algebraicSpaces :
    IsPullback
      (ObjectProperty.homMk (torsorOfInvertibleChartToSpace D p hp L hL V) :
        representedAlgebraicSpace D.site D.base D.base_mem _ ⟶ torsorOfInvertibleSpace D p hp L hL)
      (ObjectProperty.homMk (yoneda.map (torsorOfInvertibleChartHom D p hp L hL V)) :
        representedAlgebraicSpace D.site D.base D.base_mem _ ⟶
          representedAlgebraicSpace D.site D.base D.base_mem V.obj.left)
      (torsorOfInvertibleProjection D p hp L hL)
      (ObjectProperty.homMk V.obj.hom :
        representedAlgebraicSpace D.site D.base D.base_mem V.obj.left ⟶ ⟨X, hp.1⟩) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (isPullback_torsorOfInvertible_chart D p hp L hL V).w)
    (isPullback_torsorOfInvertible_chart D p hp L hL V)

end Chart

/-! ### Clause (1) -/

/-- A property of morphisms of algebraic spaces which is fppf local on the base holds for `q` as
soon as it holds for `Spec 𝒜(V) ⟶ V` at every affine étale chart `V` trivializing `ℒ`. -/
theorem torsorOfInvertibleProjection_of_trivializingChart
    (P : MorphismProperty (AlgebraicSpaces D.site D.base D.base_mem))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, u + 1} D.site D.base D.base_mem)]
    (hP : ∀ (V : SmallEtale D.site D.base D.base_mem X) [IsAffine (chartScheme V)],
      Nonempty (L.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V)) →
        P (ObjectProperty.homMk (yoneda.map (torsorOfInvertibleChartHom D p hp L hL V)) :
          representedAlgebraicSpace D.site D.base D.base_mem _ ⟶
            representedAlgebraicSpace D.site D.base D.base_mem V.obj.left)) :
    P (torsorOfInvertibleProjection D p hp L hL) := by
  let I := {V : SmallEtale D.site D.base D.base_mem X // IsAffine (chartScheme V) ∧
    Nonempty (L.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V))}
  let Yi : I → AlgebraicSpaces D.site D.base D.base_mem := fun i =>
    representedAlgebraicSpace D.site D.base D.base_mem i.1.obj.left
  let gi : ∀ i, Yi i ⟶ ⟨X, hp.1⟩ := fun i => ObjectProperty.homMk i.1.obj.hom
  have hjoint : (⋃ i, Set.range (pointsMap D.site D.base D.base_mem (Yi i).obj (gi i).hom)) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨V, hV, he, hx⟩ := exists_affine_trivializing_chart D p hp L hL x
    exact Set.mem_iUnion.2 ⟨⟨V, hV, he⟩, hx⟩
  have hR : Presieve.ofArrows Yi gi ∈
      (Topology.fppf.precoverage.{u, u + 1} D.site D.base D.base_mem).coverings ⟨X, hp.1⟩ :=
    ⟨I, Yi, gi, rfl, hp.1, fun i => (Yi i).property,
      isFppfCovering_of_isEtaleCovering D.site D.base D.base_mem
        ⟨hp.1, fun i => (Yi i).property,
          fun i => (isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem _).2 i.1.property,
          hjoint⟩⟩
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd (P := P) hR).2
    fun g _ hg => ?_
  obtain ⟨i⟩ := hg
  have : IsAffine (chartScheme i.1) := i.2.1
  have sq := isPullback_torsorOfInvertible_chart_algebraicSpaces D p hp L hL i.1
  refine (P.cancel_left_of_respectsIso sq.isoPullback.hom
    (pullback.snd (torsorOfInvertibleProjection D p hp L hL) (gi i))).1 ?_
  rw [sq.isoPullback_hom_snd]
  exact hP i.1 i.2.2

/-- `q` is smooth of relative dimension one. -/
theorem isSmoothOfRelativeDimension_torsorOfInvertibleProjection :
    IsSmoothOfRelativeDimension D.site D.base D.base_mem 1
      (torsorOfInvertibleProjection D p hp L hL).hom := by
  refine torsorOfInvertibleProjection_of_trivializingChart D p hp L hL
    (smoothOfRelativeDimensionProperty D.site D.base D.base_mem 1) fun V hV ⟨e⟩ => ?_
  have : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme D.site D.base D.base_mem).map
      (torsorOfInvertibleChartHom D p hp L hL V)) := by
    rw [toScheme_map_affineChartSpecHom]
    exact smoothOfRelativeDimension_specChartMap_laurentAlgebraSheaf D p hp L hL e
      (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X V hV)
  exact isSmoothOfRelativeDimension_yoneda_map D.site D.base D.base_mem _ 1

/-- `q` is surjective. -/
theorem isSurjective_torsorOfInvertibleProjection :
    IsSurjective D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL).hom := by
  refine torsorOfInvertibleProjection_of_trivializingChart D p hp L hL
    (surjectiveMorphismProperty D.site D.base D.base_mem) fun V hV ⟨e⟩ => ?_
  refine isSurjective_yoneda_map D.site D.base D.base_mem _ ?_
  rw [toScheme_map_affineChartSpecHom]
  exact surjective_specChartMap_laurentAlgebraSheaf D p hp L hL e
    (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X V hV)

end AlgebraicGeometry.Space

end
