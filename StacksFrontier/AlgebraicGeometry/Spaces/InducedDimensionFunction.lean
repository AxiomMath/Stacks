module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Catenary
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionAntitone
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart

/-!
# The dimension function induced on a space locally of finite type over the base

Let `Y` be a decent, locally Noetherian, universally catenary algebraic space with a dimension
function `δ`, and let `f : X ⟶ Y` be a morphism locally of finite type from a decent algebraic
space. **Stacks 0EDN** says that the function `δ_X` sending `x` to `δ (f x)` plus the
transcendence degree of `x` over `f x` is a dimension function on `|X|`.

The function itself is `AlgebraicGeometry.Space.inducedDimensionValue` of
`StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType`. The theorem lives in this
separate module because its proof imports the twisted affine line and the reduced closed
subspaces of `|Y|`, which themselves depend on that module.

## Main results

* `AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue`: Stacks 0EDN.

## Implementation notes

The proof does not follow the source, whose argument through a finite cover of `Y` by a scheme
has a gap when a branch of codimension one at a point is glued to a branch of codimension two.
Instead `δ` is read on a surjective étale chart `φ : U ⟶ Y` by a locally Noetherian scheme,
where `δ ∘ φ` is a dimension function by
`AlgebraicGeometry.Space.exists_dimensionFunction_comp_chart`. The chart `U` is universally
catenary, so Stacks 02JW propagates `δ ∘ φ` to a chart `A` of `X ×_Y U`, and the resulting
dimension function on `A` is the pullback of `δ_X` because the transcendence degree is computed
on that chart. It descends to `|X|` along the generalizing surjection `|A| ⟶ |X|`, Stacks 03IL.

## References

* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_InducedDimensionFunction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_InducedDimensionFunction
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_InducedDimensionFunction B S hS).has_limit _

/-- **Stacks 0EDN.** Let `Y` be a decent, locally Noetherian, universally catenary algebraic
space and `δ` a dimension function on `|Y|`. If `X` is a decent algebraic space and `f : X ⟶ Y`
is locally of finite type, then `δ_X`, the value of `δ` at the image of a point plus the
transcendence degree of the point over its image, is a dimension function on `|X|`. -/
@[stacks 0EDN]
theorem exists_dimensionFunction_inducedDimensionValue (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (hYN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hYcat : IsUniversallyCatenary B S hS Y) (δ : DimensionFunction (points B S hS Y))
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ d : DimensionFunction (points B S hS X), ∀ x : points B S hS X,
      d x = inducedDimensionValue B S hS δ f x := by
  classical
  obtain ⟨U, φ, hφs, hφe, hUN⟩ := hYN
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hUN
  obtain ⟨dU, hdU⟩ := exists_dimensionFunction_comp_chart B S hS hφs hφe hY hYdec hYcat δ hUN
  have hUcat := isUniversallyCatenary_chart_of_isUniversallyCatenary B S hS hY hYcat U φ
    (isEtale_of_presheaf_etale B S hS hφe)
  /- A chart of `X ×_Y U`, and the morphism of the site it induces to `U`. -/
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hX' := isAlgebraicSpace_pullback B S hS f φ hX hU hY
  obtain ⟨A, α, hαs, hαe⟩ := hX'.exists_atlas
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have := isMultiplicative_presheaf_etale B S hS
  have hfst := MorphismProperty.of_isPullback (IsPullback.of_hasPullback f φ).flip hφe
  set a := α ≫ pullback.fst f φ with ha
  have hae := MorphismProperty.comp_mem _ _ _ hαe hfst
  obtain ⟨τ, hτ⟩ : ∃ τ : A ⟶ U, yoneda.map τ = α ≫ pullback.snd f φ :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hcomm : yoneda.map τ ≫ φ = a ≫ f := by
    rw [hτ, Category.assoc, ← pullback.condition, ← Category.assoc]
  have hτlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map τ) :=
    hf A U a φ τ hae hφe hcomm
  /- Stacks 02JW on the chart. -/
  obtain ⟨dA, hdA⟩ := Stacks.Chow.relativeDimension_isDimensionFunction hUcat dU
    ((BigFppfOver.toScheme B S hS).map τ)
  /- The chart of `X` is a generalizing surjection on points. -/
  have hαsurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) α) :=
    (surjective_iff_surjective_pointsMap B S hS _ hX' A α).mp hαs
  have hφsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (surjective_iff_surjective_pointsMap B S hS Y hY U φ).mp hφs
  have hfstsurj : Function.Surjective (pointsMap B S hS (pullback f φ) (pullback.fst f φ)) := by
    intro z
    obtain ⟨v, hv⟩ := hφsurj (pointsMap B S hS X f z)
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS
      (IsPullback.of_hasPullback f φ) z v hv.symm
    exact ⟨w, hw⟩
  have hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) a) := by
    rw [ha, pointsMap_comp]
    exact hfstsurj.comp hαsurj
  refine exists_dimensionFunction_of_generalizingMap
    ((continuous_pointsMap B S hS a).comp (schemePointsHomeomorph B S hS A).symm.continuous)
    (hasurj.comp (schemePointsHomeomorph B S hS A).symm.surjective)
    (((schemePointsHomeomorph B S hS A).symm.isOpenEmbedding.generalizingMap).comp
      (generalizingMap_pointsMap_of_isDecentSpace B S hS X hX hXdec A a hae)) _ dA ?_
  intro w
  let _ : Algebra (((BigFppfOver.toScheme B S hS).obj U).residueField
      ((BigFppfOver.toScheme B S hS).map τ w))
      (((BigFppfOver.toScheme B S hS).obj A).residueField w) :=
    (((BigFppfOver.toScheme B S hS).map τ).residueFieldMap w).hom.toAlgebra
  have hr := (hasTranscendenceDegreeAt_pointsMap_iff B S hS
    (Cardinal.toENat (Algebra.trdeg
      (((BigFppfOver.toScheme B S hS).obj U).residueField
        ((BigFppfOver.toScheme B S hS).map τ w))
      (((BigFppfOver.toScheme B S hS).obj A).residueField w)))
    f A U a φ τ hae hφe hcomm w).mpr rfl
  have hval := inducedDimensionValue_eq B S hS hX hY δ f hf _ _ hr
  have himg : pointsMap B S hS X f (pointsMap B S hS (yoneda.obj A) a
      ((pointsEquivScheme B S hS A).symm w)) =
      pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm
        ((BigFppfOver.toScheme B S hS).map τ w)) := by
    rw [← pointsMap_comp_apply, ← hcomm, pointsMap_comp_apply,
      ChartBranch.pointsEquivScheme_symm_pointsMap]
  show dA w = inducedDimensionValue B S hS δ f
    (pointsMap B S hS (yoneda.obj A) a ((pointsEquivScheme B S hS A).symm w))
  rw [hdA w, hval, himg, ← hdU, Cardinal.toNat_toENat]
  rfl

end AlgebraicGeometry.Space

end
