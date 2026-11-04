module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineEtaleChartPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingUnitFlatEquivalence

/-!
# Tags 07VX, 07VY and 07W3 from the lift of étale charts across thickenings

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism
and `Y' = Y ⨿_X X'`.  This module states [Stacks Project, Tag 07VX], [Stacks Project, Tag 07VY]
and [Stacks Project, Tag 07W3] in full, each as one declaration, under the hypothesis that
surjective étale scheme charts lift across thickenings,
`AlgebraicGeometry.Space.HasEtaleChartLifts`, the chart form of the essential surjectivity half
of [Stacks Project, Tag 05ZS]; the compatible charts the pushout is built from follow from it by
`AlgebraicGeometry.Space.hasThickeningAffineAtlases_of_chartLift`.

## Main results

* `AlgebraicGeometry.Space.pushout_spec_of_chartLift`: Tag 07VX — the pushout exists, `Y ⟶ Y'`
  is a thickening, and `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}` on the small étale site of `Y'`.
* `AlgebraicGeometry.Space.pushoutGluing_spec_of_chartLift`: Tag 07VY — `F` sends schemes to
  pairs of schemes, `G ⊣ F`, `G(V, U', φ) = V ⨿_U U'`, and `G` sends pairs of schemes to schemes.
* `AlgebraicGeometry.Space.pushoutGluing_flat_of_chartLift`: Tag 07W3 — clauses (1)–(5), the
  counit `G(F(W')) ⟶ W'` is an isomorphism for `W'` flat over `Y'`, and `F`, `G` restrict to
  mutually quasi-inverse functors between flat triples and spaces flat over `Y'`.

## References

* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hlift : HasEtaleChartLifts B S hS)
  {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
  (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)

/-- **[Stacks Project, Tag 07VX], given that charts lift across thickenings.**  Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine morphism.
The pushout `Y' = Y ⨿_X X'` exists in the category of algebraic spaces over `S`, the morphism
`Y ⟶ Y'` is a thickening, and `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}` as sheaves on the small
étale site of `Y'`: over every object `W ⟶ Y'` of that site — indeed over every scheme `W` flat
over `Y'` — the ring of functions on `W` is the fibre product of the rings of functions on
`W ×_{Y'} Y` and on `W ×_{Y'} X'` over the ring of functions on `W ×_{Y'} X`, for any schemes
carrying these base changes.  The sections over `W` of the direct image of a sheaf along a
morphism `T ⟶ Y'` being its sections over `W ×_{Y'} T`, this is the evaluation of the sheaf
formula at `W`. -/
theorem pushout_spec_of_chartLift :
    let hatlas : HasThickeningAffineAtlases B S hS :=
      hasThickeningAffineAtlases_of_chartLift B S hS hlift
    HasPushout i f ∧
      (letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
      IsThickeningHom B S hS (pushout.inr i f) ∧
      ∀ {W WX' WY WX : BigFppfOver B S hS} {cX' : WX' ⟶ W} {cY : WY ⟶ W} {jX' : WX ⟶ WX'}
        {jY : WX ⟶ WY} {w : schemeSpace W ⟶ pushout i f} {pX' : schemeSpace WX' ⟶ X'}
        {pY : schemeSpace WY ⟶ Y} {pX : schemeSpace WX ⟶ X}, IsFlat B S hS w.hom →
        IsPullback (schemeSpaceMap cX') pX' w (pushout.inl i f) →
        IsPullback (schemeSpaceMap cY) pY w (pushout.inr i f) →
        IsPullback (schemeSpaceMap jY) pX pY f → schemeSpaceMap jX' ≫ pX' = pX ≫ i →
        jY ≫ cY = jX' ≫ cX' →
        IsPullback (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map cY).op)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map cX').op)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map jY).op)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map jX').op)) := by
  intro hatlas
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  exact ⟨inferInstance, pushout_inr_isThickening B S hS hatlas i f hi hf,
    fun hw hX'sq hYsq hjYsq hjX'w hsides => isPullback_globalSections_of_isFlat hatlas hi hf
      (IsPushout.of_hasPushout i f) hw hX'sq hYsq hjYsq hjX'w hsides⟩

/-- **[Stacks Project, Tag 07VY], given that charts lift across thickenings.**  Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism and
`Y' = Y ⨿_X X'`.  The base-change functor `F : V' ↦ (V' ×_{Y'} Y, V' ×_{Y'} X', 1)` sends
schemes over `Y'` to pairs of schemes; it has the left adjoint `G`, which sends a triple
`(V, U', φ)` to the pushout `V ⨿_{V ×_Y X} U'` with its structure morphism to `Y'`; and `G`
sends pairs of schemes to schemes. -/
theorem pushoutGluing_spec_of_chartLift :
    let hatlas : HasThickeningAffineAtlases B S hS :=
      hasThickeningAffineAtlases_of_chartLift B S hS hlift
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    (∀ Z : Over (pushout i f), Z.left.1.IsRepresentable →
        ((pushoutBaseChangeFunctor B S hS hatlas i f hi hf).obj Z).obj.left.left.1.IsRepresentable ∧
        ((pushoutBaseChangeFunctor B S hS hatlas i f hi hf).obj
          Z).obj.right.left.1.IsRepresentable) ∧
      Nonempty (pushoutGluingFunctor B S hS hatlas i f hi hf ⊣
        pushoutBaseChangeFunctor B S hS hatlas i f hi hf) ∧
      (∀ T : pushoutGluingData B S hS i f,
        ∃ (v : T.obj.left.left ⟶ ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left)
          (u' : T.obj.right.left ⟶ ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left),
          IsPushout (CategoryTheory.PushoutGluing.sourceMap i f T)
              (pullback.fst T.obj.right.hom i) v u' ∧
            v ≫ ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom =
              T.obj.left.hom ≫ pushout.inr i f ∧
            u' ≫ ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom =
              T.obj.right.hom ≫ pushout.inl i f) ∧
      (∀ T : pushoutGluingData B S hS i f, T.obj.left.left.1.IsRepresentable →
        T.obj.right.left.1.IsRepresentable →
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left.1.IsRepresentable) := by
  intro hatlas
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  exact ⟨fun Z hZ => ⟨isRepresentable_pushoutBaseChangeFunctor_obj_left hatlas i f hi hf Z hZ,
      isRepresentable_pushoutBaseChangeFunctor_obj_right hatlas i f hi hf Z hZ⟩,
    ⟨pushoutGluingAdjunction B S hS hatlas i f hi hf⟩,
    pushoutGluingFunctor_obj_isPushout B S hS hatlas i f hi hf,
    isRepresentable_pushoutGluingFunctor_obj hatlas i f hi hf⟩

/-- **[Stacks Project, Tag 07W3], given that charts lift across thickenings.**  Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism,
`Y' = Y ⨿_X X'` and `G ⊣ F` the gluing adjunction of [Stacks Project, Tag 07VY].  For a triple
`(V, U', φ)`, the glued space `G(V, U', φ) ⟶ Y'` is (1) locally of finite type, (2) flat,
(3) flat and locally of finite presentation, (4) smooth, (5) étale, if and only if both
`V ⟶ Y` and `U' ⟶ X'` are.  If `W'` is flat over `Y'` the counit `G(F(W')) ⟶ W'` is an
isomorphism; the unit is an isomorphism; `F` sends spaces flat over `Y'` to flat triples and
`G` sends flat triples to spaces flat over `Y'`; so `F` and `G` are mutually quasi-inverse
between the spaces flat over `Y'` and the triples with `V ⟶ Y` and `U' ⟶ X'` flat. -/
theorem pushoutGluing_flat_of_chartLift :
    let hatlas : HasThickeningAffineAtlases B S hS :=
      hasThickeningAffineAtlases_of_chartLift B S hS hlift
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    (∀ T : pushoutGluingData B S hS i f,
      (IsLocallyOfFiniteType B S hS
          ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
        IsLocallyOfFiniteType B S hS T.obj.left.hom.hom ∧
          IsLocallyOfFiniteType B S hS T.obj.right.hom.hom) ∧
      (IsFlat B S hS ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
        IsFlat B S hS T.obj.left.hom.hom ∧ IsFlat B S hS T.obj.right.hom.hom) ∧
      ((IsFlat B S hS ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ∧
          IsLocallyOfFinitePresentation B S hS
            ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom) ↔
        ((IsFlat B S hS T.obj.left.hom.hom ∧
            IsLocallyOfFinitePresentation B S hS T.obj.left.hom.hom) ∧
          (IsFlat B S hS T.obj.right.hom.hom ∧
            IsLocallyOfFinitePresentation B S hS T.obj.right.hom.hom))) ∧
      (IsSmooth B S hS ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
        IsSmooth B S hS T.obj.left.hom.hom ∧ IsSmooth B S hS T.obj.right.hom.hom) ∧
      (IsEtale B S hS ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
        IsEtale B S hS T.obj.left.hom.hom ∧ IsEtale B S hS T.obj.right.hom.hom)) ∧
    (∀ Z : Over (pushout i f), IsFlat B S hS Z.hom.hom →
      IsIso ((pushoutGluingAdjunction B S hS hatlas i f hi hf).counit.app Z)) ∧
    IsIso (pushoutGluingAdjunction B S hS hatlas i f hi hf).unit ∧
    (∀ Z : Over (pushout i f), IsFlat B S hS Z.hom.hom →
      IsFlat B S hS ((pushoutBaseChangeFunctor B S hS hatlas i f hi hf).obj Z).obj.left.hom.hom ∧
        IsFlat B S hS
          ((pushoutBaseChangeFunctor B S hS hatlas i f hi hf).obj Z).obj.right.hom.hom) ∧
    (∀ T : pushoutGluingData B S hS i f,
      IsFlat B S hS T.obj.left.hom.hom → IsFlat B S hS T.obj.right.hom.hom →
        IsFlat B S hS ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom) := by
  intro hatlas
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  refine ⟨fun T => ⟨isLocallyOfFiniteType_pushoutGluingFunctor_obj_iff hlift hatlas i f hi hf T,
      isFlat_pushoutGluingFunctor_obj_iff hlift hatlas i f hi hf T,
      isFlat_and_isLocallyOfFinitePresentation_pushoutGluingFunctor_obj_iff hlift hatlas i f hi hf
        T,
      isSmooth_pushoutGluingFunctor_obj_iff hlift hatlas i f hi hf T,
      isEtale_pushoutGluingFunctor_obj_iff hlift hatlas i f hi hf T⟩,
    isIso_pushoutGluingAdjunction_counit_of_isFlat B S hS hatlas i f hi hf,
    isIso_pushoutGluingAdjunction_unit hlift hatlas i f hi hf,
    fun Z hZ => ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback Z.hom (pushout.inr i f)) hZ,
      (isFlat_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback Z.hom (pushout.inl i f)) hZ⟩,
    fun T hV hU => (isFlat_pushoutGluingFunctor_obj_iff hlift hatlas i f hi hf T).2 ⟨hV, hU⟩⟩

end AlgebraicGeometry.Space

end
