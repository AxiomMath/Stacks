module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer

/-!
# Smoothness of relative dimension `d` for morphisms of schemes of the site

A morphism `h : U ⟶ V` of the big fppf site of `S` whose underlying morphism of schemes is smooth
of relative dimension `d` (in Mathlib's sense, `AlgebraicGeometry.SmoothOfRelativeDimension`)
induces a morphism of represented algebraic spaces which is smooth of relative dimension `d` in
the sense of `AlgebraicGeometry.Space.IsSmoothOfRelativeDimension`: the identities are étale
charts, on which the relative dimension of Stacks 04NM is the dimension of the fibres of `h`,
and the fibres of a morphism smooth of relative dimension `d` have dimension `d` at every point
(Stacks 0B9D). The same then holds for the projection `F ×_S U ⟶ F` from the restriction of an
algebraic space `F` to `U`, which is a base change of `h_U ⟶ h_S`.

## Main results

* `AlgebraicGeometry.Space.isSmoothOfRelativeDimension_yoneda_map`: the represented morphism is
  smooth of relative dimension `d`.
* `AlgebraicGeometry.Space.isSmoothOfRelativeDimension_prod_fst_yoneda_obj`: so is the projection
  `F ⨯ h_U ⟶ F`.

## References

* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the site whose morphism of schemes is smooth of relative dimension `d`
represents a morphism of algebraic spaces smooth of relative dimension `d`.** The identities are
étale charts, and on them the relative dimension at a point is the dimension of the fibre of the
morphism of schemes there, which is `d` by Stacks 0B9D. -/
theorem isSmoothOfRelativeDimension_yoneda_map {U V : BigFppfOver B S hS} (h : U ⟶ V) (d : ℕ)
    [SmoothOfRelativeDimension d ((BigFppfOver.toScheme B S hS).map h)] :
    IsSmoothOfRelativeDimension B S hS d (yoneda.map h) := by
  refine ⟨(isSmooth_yoneda_map_iff B S hS h).2
    (SmoothOfRelativeDimension.smooth d ((BigFppfOver.toScheme B S hS).map h)), fun x => ?_⟩
  obtain ⟨u, rfl⟩ := (pointsEquivScheme B S hS U).symm.surjective x
  have key := hasRelativeDimensionAt_pointsMap_iff B S hS (d : ℕ∞) (yoneda.map h) U V
    (𝟙 _) (𝟙 _) h (presheaf_etale_id B S hS U) (presheaf_etale_id B S hS V) (by simp) u
  rw [pointsMap_id] at key
  exact key.2 (fiberDimensionAt_eq_of_smoothOfRelativeDimension _ d u)

/-- **The projection `h_a ⨯ F ⟶ F` is smooth of relative dimension `d`** when the structure
morphism of `a` is: it is the base change of `h_a ⟶ h_S` along the structure morphism of `F`. -/
theorem isSmoothOfRelativeDimension_prod_snd_yoneda_obj (a : BigFppfOver B S hS) (d : ℕ)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    [SmoothOfRelativeDimension d
      ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))] :
    IsSmoothOfRelativeDimension B S hS d (prod.snd : yoneda.obj a ⨯ F ⟶ F) := by
  have hya : IsAlgebraicSpace B S hS (yoneda.obj a) := isAlgebraicSpace_yoneda B S hS a
  have hterm : IsAlgebraicSpace B S hS
      (yoneda.obj (Over.mk (𝟙 (B.obj hS))) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    isAlgebraicSpace_yoneda B S hS _
  have hpa : IsAlgebraicSpace B S hS (yoneda.obj a ⨯ F) :=
    isAlgebraicSpace_prod_yoneda_obj a hF
  have sq := isPullback_prod_fst_snd_yoneda_obj a F
  have sqSp : IsPullback
      (ObjectProperty.homMk (prod.fst : yoneda.obj a ⨯ F ⟶ yoneda.obj a) :
        (⟨yoneda.obj a ⨯ F, hpa⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj a, hya⟩)
      (ObjectProperty.homMk (prod.snd : yoneda.obj a ⨯ F ⟶ F) :
        (⟨yoneda.obj a ⨯ F, hpa⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk (yoneda.map (Over.mkIdTerminal.from a)) :
        (⟨yoneda.obj a, hya⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hterm⟩)
      (ObjectProperty.homMk ((isTerminal_yoneda_obj_base B S hS).from F) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hterm⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) (by simpa using sq)
  exact (smoothOfRelativeDimensionProperty B S hS d).of_isPullback sqSp
    (isSmoothOfRelativeDimension_yoneda_map B S hS (Over.mkIdTerminal.from a) d)

/-- **The projection from the restriction of an algebraic space to an object of the site is
smooth of relative dimension `d`** as soon as the structure morphism of that object is a
morphism of schemes smooth of relative dimension `d`: it is the base change of `h_a ⟶ h_S`
along the structure morphism of `F`. -/
theorem isSmoothOfRelativeDimension_prod_fst_yoneda_obj (a : BigFppfOver B S hS) (d : ℕ)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    [SmoothOfRelativeDimension d
      ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))] :
    IsSmoothOfRelativeDimension B S hS d (prod.fst : F ⨯ yoneda.obj a ⟶ F) := by
  have hpa : IsAlgebraicSpace B S hS (yoneda.obj a ⨯ F) :=
    isAlgebraicSpace_prod_yoneda_obj a hF
  have hFa : IsAlgebraicSpace B S hS (F ⨯ yoneda.obj a) :=
    isAlgebraicSpace_of_iso B S hS (prod.braiding F (yoneda.obj a)).symm hpa
  let e : (⟨F ⨯ yoneda.obj a, hFa⟩ : AlgebraicSpaces B S hS) ≅ ⟨yoneda.obj a ⨯ F, hpa⟩ :=
    ObjectProperty.isoMk _ (prod.braiding F (yoneda.obj a))
  have : (smoothOfRelativeDimensionProperty B S hS d).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h : IsSmoothOfRelativeDimension B S hS d
      ((prod.braiding F (yoneda.obj a)).hom ≫ (prod.snd : yoneda.obj a ⨯ F ⟶ F)) :=
    ((smoothOfRelativeDimensionProperty B S hS d).cancel_left_of_respectsIso e.hom
      (ObjectProperty.homMk (prod.snd : yoneda.obj a ⨯ F ⟶ F) :
        (⟨yoneda.obj a ⨯ F, hpa⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)).2
      (isSmoothOfRelativeDimension_prod_snd_yoneda_obj B S hS a d hF)
  simpa using h

end AlgebraicGeometry.Space

end
