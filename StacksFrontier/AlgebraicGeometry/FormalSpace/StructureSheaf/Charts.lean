module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective

/-!
# Affine étale formal charts and their reductions

Let `X` be a fppf sheaf over `S` with a reduction `X_red`. An object `φ : U ⟶ X` of the category
of Stacks 0DEE over `X` — `U` an affine formal algebraic space, `φ` representable by algebraic
spaces and étale — has, as its reduction, an affine object `W` of `X_affine,étale` together with
a morphism `a : W ⟶ U` exhibiting `W` as `U ×_X X_red` (a *reduction square*). This file
collects what the construction of the structure sheaf needs about such charts and squares.

## Main results

* `AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts.isRepresentableEtale_hom_left`: a
  morphism of charts over `X` is representable by algebraic spaces and étale (Stacks 0AQ0 and
  Stacks 03FV, in the form of `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp'`).
* `AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts.pullbackChart`: the fibre product of two
  morphisms of charts is a chart.
* `AlgebraicGeometry.FormalSpace.Reduction.exists_affineEtale_hom_of_isPullback` and
  `AlgebraicGeometry.FormalSpace.Reduction.affineEtale_hom_ext_of_isPullback`: a morphism of
  charts induces a unique morphism of their reductions.
* `AlgebraicGeometry.FormalSpace.Reduction.bijective_app_of_isPullback` and
  `AlgebraicGeometry.FormalSpace.Reduction.surjective_pointsMapULift_of_isPullback`: the
  morphism from the reduction of a chart to the chart is bijective on sections over reduced
  objects of the site, hence surjective on points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : FppfSheaf B S hS}

/-! ### Morphisms of charts -/

namespace AffineEtaleFormalCharts

/-- **A morphism of affine étale formal charts over `X` is representable by algebraic spaces and
étale.** Both structure morphisms to `X` are, so the morphism between them is, by the
cancellation property of representable étale morphisms. -/
theorem isRepresentableEtale_hom_left {U V : AffineEtaleFormalCharts B S hS X} (g : U ⟶ V) :
    IsRepresentableEtale B S hS g.hom.left :=
  isRepresentableEtale_of_comp' B S hS g.hom.left V.obj.hom V.property.2
    (by rw [Over.w g.hom]; exact U.property.2)

/-- A morphism of affine étale formal charts over `X` is representable by schemes and affine
over every object of the site (Stacks 0AKN). -/
theorem relative_isAffineHom_hom_left {U V : AffineEtaleFormalCharts B S hS X} (g : U ⟶ V) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) g.hom.left :=
  relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS g.hom.left U.property.1
    V.property.1 (isRepresentableEtale_hom_left g).1

variable {U₁ U₂ V : AffineEtaleFormalCharts B S hS X} (g₁ : U₁ ⟶ V) (g₂ : U₂ ⟶ V)

/-- The fibre product of two morphisms of affine étale formal charts over `X` is an affine étale
formal chart: it is affine over `U₂`, hence an affine formal algebraic space, and representable
étale over `U₂`, hence over `X`. -/
noncomputable def pullbackChart : AffineEtaleFormalCharts B S hS X :=
  ⟨Over.mk (pullback.snd g₁.hom.left g₂.hom.left ≫ U₂.obj.hom),
    isAffineFormalAlgebraicSpace_of_affine B S hS (pullback.snd g₁.hom.left g₂.hom.left)
      U₂.property.1
      (by
        have := MorphismProperty.relative_isStableUnderBaseChange
          (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
          (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))
        exact MorphismProperty.pullback_snd _ _ (relative_isAffineHom_hom_left g₁)),
    IsRepresentableEtale.comp B S hS
      (isRepresentableEtale_pullback_snd B S hS _ _ (isRepresentableEtale_hom_left g₁))
      U₂.property.2⟩

/-- The first projection of the fibre product of two morphisms of charts. -/
noncomputable def pullbackFst : pullbackChart g₁ g₂ ⟶ U₁ :=
  ObjectProperty.homMk (Over.homMk (pullback.fst g₁.hom.left g₂.hom.left) (by
    change pullback.fst g₁.hom.left g₂.hom.left ≫ U₁.obj.hom =
      pullback.snd g₁.hom.left g₂.hom.left ≫ U₂.obj.hom
    rw [← Over.w g₁.hom, ← Over.w g₂.hom, ← Category.assoc, pullback.condition,
      Category.assoc]))

/-- The second projection of the fibre product of two morphisms of charts. -/
noncomputable def pullbackSnd : pullbackChart g₁ g₂ ⟶ U₂ :=
  ObjectProperty.homMk (Over.homMk (pullback.snd g₁.hom.left g₂.hom.left) rfl)

/-- The underlying morphism of `pullbackFst g₁ g₂` is the first projection
`pullback.fst g₁.hom.left g₂.hom.left`. -/
@[simp]
theorem pullbackFst_hom_left :
    (pullbackFst g₁ g₂).hom.left = pullback.fst g₁.hom.left g₂.hom.left :=
  rfl

/-- The underlying morphism of `pullbackSnd g₁ g₂` is the second projection
`pullback.snd g₁.hom.left g₂.hom.left`. -/
@[simp]
theorem pullbackSnd_hom_left :
    (pullbackSnd g₁ g₂).hom.left = pullback.snd g₁.hom.left g₂.hom.left :=
  rfl

end AffineEtaleFormalCharts

/-! ### Reduction squares -/

namespace Reduction

variable (R : Reduction B S hS X)

/-- **A morphism of charts induces a morphism of their reductions.** Given reduction squares
for two affine étale formal charts `U` and `V` over `X`, a morphism `g : U ⟶ V` over `X` induces
a morphism of the corresponding affine objects of `X_affine,étale` lying over it: the universal
property of the square of `V`, read in the site by full faithfulness of the sheafified Yoneda
embedding. -/
theorem exists_affineEtale_hom_of_isPullback {U V : AffineEtaleFormalCharts B S hS X}
    {W W' : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left}
    {a' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W') ⟶
      V.obj.left}
    (ha : IsPullback a (R.affineChartMap W) U.obj.hom R.inclusion)
    (ha' : IsPullback a' (R.affineChartMap W') V.obj.hom R.inclusion) (g : U ⟶ V) :
    ∃ h : W ⟶ W', (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h) ≫ a' = a ≫ g.hom.left := by
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have hw : (a ≫ g.hom.left) ≫ V.obj.hom = R.affineChartMap W ≫ R.inclusion := by
    rw [Category.assoc, Over.w g.hom]
    exact ha.w
  obtain ⟨m, hm⟩ := (sheafifiedYonedaFF B S hS).map_surjective
    (ha'.lift (a ≫ g.hom.left) (R.affineChartMap W) hw)
  have hm₁ : sY.map m ≫ a' = a ≫ g.hom.left := by
    rw [hm]
    exact ha'.lift_fst _ _ _
  have hm₂ : sY.map m ≫ R.affineChartMap W' = R.affineChartMap W := by
    rw [hm]
    exact ha'.lift_snd _ _ _
  have hc : (schemeSpaceFunctor B S hS).map m ≫ R.affineChartSpaceMap W' =
      R.affineChartSpaceMap W := by
    apply liftSheafMap_injective B S hS
    rw [liftSheafMap_comp]
    rw [affineChartMap, affineChartMap, ← Category.assoc,
      sheafifiedYoneda_map_liftSheafYonedaSpaceIsoSheafifiedYoneda_inv, Category.assoc] at hm₂
    exact (cancel_epi _).mp hm₂
  exact ⟨ObjectProperty.homMk (ObjectProperty.homMk (CostructuredArrow.homMk m
    (congrArg (fun k => k.hom) hc))), hm₁⟩

/-- The morphism of reductions induced by a morphism of charts is unique. -/
theorem affineEtale_hom_ext_of_isPullback {U V : AffineEtaleFormalCharts B S hS X}
    {W W' : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left}
    {a' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W') ⟶
      V.obj.left}
    (ha' : IsPullback a' (R.affineChartMap W') V.obj.hom R.inclusion) (g : U ⟶ V)
    {h₁ h₂ : W ⟶ W'}
    (hh₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h₁) ≫ a' = a ≫ g.hom.left)
    (hh₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h₂) ≫ a' = a ≫ g.hom.left) :
    h₁ = h₂ := by
  have hsY : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((Space.AffineEtale.toOver B S hS R.space.obj).map h₁) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h₂) :=
    ha'.hom_ext (hh₁.trans hh₂.symm)
      ((R.map_affineChartMap h₁).trans (R.map_affineChartMap h₂).symm)
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact CostructuredArrow.hom_ext _ _ ((sheafifiedYonedaFF B S hS).map_injective hsY)

/-- **The reduction of a chart maps bijectively to it on sections over reduced objects.** The
morphism `a : W ⟶ U` of a reduction square is a base change of the inclusion `X_red ⟶ X`, which is
bijective on the sections over a reduced object of the site. -/
theorem bijective_app_of_isPullback {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left}
    (ha : IsPullback a (R.affineChartMap W) U.obj.hom R.inclusion) (T : BigFppfOver B S hS)
    (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T)) :
    Function.Bijective (a.hom.app (op T)) := by
  let ev := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ⋙
    (evaluation _ _).obj (op T)
  have : IsIso (ev.map R.inclusion) :=
    (isIso_iff_bijective _).mpr (R.isReduction.bijective_app T hT)
  exact (isIso_iff_bijective _).mp (ha.map ev).isIso_fst_of_isIso

/-- The morphism from the reduction of a chart to the chart is surjective on points. -/
theorem surjective_pointsMapULift_of_isPullback {U : AffineEtaleFormalCharts B S hS X}
    {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left}
    (ha : IsPullback a (R.affineChartMap W) U.obj.hom R.inclusion) :
    Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _ a.hom) :=
  (bijective_pointsMapULift_of_bijective_app B S hS a.hom fun K _ _ _ =>
    R.bijective_app_of_isPullback ha _
      (inferInstanceAs (IsReduced (Spec (.of K))))).2

end Reduction

end AlgebraicGeometry.FormalSpace

end
