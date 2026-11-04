module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleChartLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartLift

/-!
# Pushouts along thickenings: Tags 07VX, 07VY, 07W0, 07W1, 07W2 and 07W3

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine
morphism. This module states, with no hypothesis beyond these, the existence and the structure
sheaf of the pushout `Y' = Y ⨿_X X'` ([Stacks Project, Tag 07VX]), the gluing adjunction between
spaces over `Y'` and triples ([Stacks Project, Tag 07VY]), the fact that restricting the glued
space recovers the triple ([Stacks Project, Tag 07W0]), the two cubes of étale charts of the
proof of [Stacks Project, Tag 07W0] (equations 81.6.5.1 and 81.6.5.2, [Stacks Project, Tag 07W1]
and [Stacks Project, Tag 07W2]), and the flat equivalence ([Stacks Project, Tag 07W3]).

The results of `StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartLift`,
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement` and
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing` take as input that
étale scheme charts lift across thickenings (`AlgebraicGeometry.Space.HasEtaleChartLifts`), or
the compatible charts of a thickening-and-affine span that follow from it
(`AlgebraicGeometry.Space.hasThickeningAffineAtlases_of_chartLift`). That input is proved, as
`AlgebraicGeometry.Space.hasEtaleChartLifts`, and is supplied here.

## Main results

* `AlgebraicGeometry.Space.pushout_spec_of_isThickeningHom`: Tag 07VX.
* `AlgebraicGeometry.Space.pushoutGluing_spec_of_isThickeningHom`: Tag 07VY.
* `AlgebraicGeometry.Space.exists_etaleChartCube`: Tag 07W1.
* `AlgebraicGeometry.Space.exists_etaleChartCube_gluingData`: Tag 07W2.
* `AlgebraicGeometry.Space.pushoutGluing_flat_of_isThickeningHom`: Tag 07W3.
* `AlgebraicGeometry.Space.isIso_pushoutGluingAdjunction_unit_of_isThickeningHom`: Tag 07W0.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
* [Stacks Project, Tag 07W1](https://stacks.math.columbia.edu/tag/07W1)
* [Stacks Project, Tag 07W2](https://stacks.math.columbia.edu/tag/07W2)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section Pushout

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
  (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)

/-- **[Stacks Project, Tag 07VX].** Let `i : X ⟶ X'` be a thickening of algebraic spaces over
`S` and `f : X ⟶ Y` an affine morphism. The pushout `Y' = Y ⨿_X X'` exists in the category of
algebraic spaces over `S`, the morphism `Y ⟶ Y'` is a thickening, and
`𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}` as sheaves on the small étale site of `Y'`: over every
object `W ⟶ Y'` of that site — indeed over every scheme `W` flat over `Y'` — the ring of
functions on `W` is the fibre product of the rings of functions on `W ×_{Y'} Y` and on
`W ×_{Y'} X'` over the ring of functions on `W ×_{Y'} X`. -/
@[stacks 07VX]
theorem pushout_spec_of_isThickeningHom :
    let hatlas : HasThickeningAffineAtlases B S hS :=
      hasThickeningAffineAtlases_of_chartLift B S hS (hasEtaleChartLifts B S hS)
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
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map jX').op)) :=
  pushout_spec_of_chartLift (hasEtaleChartLifts B S hS) i f hi hf

/-- **[Stacks Project, Tag 07VY].** Let `i : X ⟶ X'` be a thickening of algebraic spaces over
`S`, `f : X ⟶ Y` an affine morphism and `Y' = Y ⨿_X X'`. The base-change functor
`F : V' ↦ (V' ×_{Y'} Y, V' ×_{Y'} X', 1)` sends schemes over `Y'` to pairs of schemes; it has
the left adjoint `G`, which sends a triple `(V, U', φ)` to the pushout `V ⨿_{V ×_Y X} U'` with
its structure morphism to `Y'`; and `G` sends pairs of schemes to schemes. -/
@[stacks 07VY]
theorem pushoutGluing_spec_of_isThickeningHom :
    let hatlas : HasThickeningAffineAtlases B S hS :=
      hasThickeningAffineAtlases_of_chartLift B S hS (hasEtaleChartLifts B S hS)
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
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left.1.IsRepresentable) :=
  pushoutGluing_spec_of_chartLift (hasEtaleChartLifts B S hS) i f hi hf

/-- **[Stacks Project, Tag 07W3].** Let `i : X ⟶ X'` be a thickening of algebraic spaces over
`S`, `f : X ⟶ Y` an affine morphism, `Y' = Y ⨿_X X'` and `G ⊣ F` the gluing adjunction of
[Stacks Project, Tag 07VY]. For a triple `(V, U', φ)`, the glued space `G(V, U', φ) ⟶ Y'` is
(1) locally of finite type, (2) flat, (3) flat and locally of finite presentation, (4) smooth,
(5) étale, if and only if both `V ⟶ Y` and `U' ⟶ X'` are. If `W'` is flat over `Y'` the counit
`G(F(W')) ⟶ W'` is an isomorphism; the unit is an isomorphism; `F` sends spaces flat over `Y'`
to flat triples and `G` sends flat triples to spaces flat over `Y'`; so `F` and `G` are mutually
quasi-inverse between the spaces flat over `Y'` and the triples with `V ⟶ Y` and `U' ⟶ X'`
flat. -/
@[stacks 07W3]
theorem pushoutGluing_flat_of_isThickeningHom :
    let hatlas : HasThickeningAffineAtlases B S hS :=
      hasThickeningAffineAtlases_of_chartLift B S hS (hasEtaleChartLifts B S hS)
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
        IsFlat B S hS ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom) :=
  pushoutGluing_flat_of_chartLift (hasEtaleChartLifts B S hS) i f hi hf

/-- **[Stacks Project, Tag 07W0].** Let `i : X ⟶ X'` be a thickening of algebraic spaces over
`S`, `f : X ⟶ Y` an affine morphism, `Y' = Y ⨿_X X'`, and let `G ⊣ F` be the gluing adjunction
of [Stacks Project, Tag 07VY], with `F : V' ↦ (V' ×_{Y'} Y, V' ×_{Y'} X', 1)` and `G` sending a
triple `(V, U', φ)` to `V ⨿_{V ×_Y X} U'`. Then `F ∘ G` is isomorphic to the identity functor
of the category of triples; indeed the unit `𝟭 ⟶ G ⋙ F` of the adjunction is an isomorphism. -/
@[stacks 07W0]
theorem isIso_pushoutGluingAdjunction_unit_of_isThickeningHom :
    let hatlas : HasThickeningAffineAtlases B S hS :=
      hasThickeningAffineAtlases_of_chartLift B S hS (hasEtaleChartLifts B S hS)
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    IsIso (pushoutGluingAdjunction B S hS hatlas i f hi hf).unit ∧
      Nonempty (pushoutGluingFunctor B S hS hatlas i f hi hf ⋙
          pushoutBaseChangeFunctor B S hS hatlas i f hi hf ≅
        𝟭 (pushoutGluingData B S hS i f)) := by
  intro hatlas
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  have hunit : IsIso (pushoutGluingAdjunction B S hS hatlas i f hi hf).unit :=
    (pushoutGluing_flat_of_isThickeningHom i f hi hf).2.2.1
  exact ⟨hunit, ⟨(asIso (pushoutGluingAdjunction B S hS hatlas i f hi hf).unit).symm⟩⟩

end Pushout

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **[Stacks Project, Tag 07W1]**, equation 81.6.5.1 of the proof of Stacks 07W0. Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine morphism.
There is a cube whose back square is the pushout `Y' = Y ⨿_X X'` of algebraic spaces and whose
front square is the pushout `P = V ⨿_U U'` of étale scheme charts, with `U ⟶ U'` a thickening
and `U ⟶ V` affine, whose four lateral squares are cartesian and whose four northeast arrows
are surjective and étale. -/
@[stacks 07W1]
theorem exists_etaleChartCube
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    ∃ (U U' V P : BigFppfOver B S hS) (Y' : AlgebraicSpaces B S hS)
      (aY : X' ⟶ Y') (bY : Y ⟶ Y') (k : U ⟶ U') (g : U ⟶ V) (aP : U' ⟶ P) (bP : V ⟶ P)
      (p : yoneda.obj U ⟶ X.1) (p' : yoneda.obj U' ⟶ X'.1) (q : yoneda.obj V ⟶ Y.1)
      (r : yoneda.obj P ⟶ Y'.1),
      IsPushout i f aY bY ∧
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map aP) ((BigFppfOver.toScheme B S hS).map bP) ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g) ∧
      IsPullback (yoneda.map k) p p' i.hom ∧
      IsPullback p (yoneda.map g) f.hom q ∧
      IsPullback (yoneda.map aP) p' r aY.hom ∧
      IsPullback (yoneda.map bP) q r bY.hom ∧
      IsSurjective B S hS p ∧ IsEtale B S hS p ∧
      IsSurjective B S hS p' ∧ IsEtale B S hS p' ∧
      IsSurjective B S hS q ∧ IsEtale B S hS q ∧
      IsSurjective B S hS r ∧ IsEtale B S hS r :=
  exists_etaleChartCube_of_isThickening_of_isAffineHom B S hS
    (hasThickeningAffineAtlases_of_chartLift B S hS (hasEtaleChartLifts B S hS)) i f hi hf

/-- **[Stacks Project, Tag 07W2]**, equation 81.6.5.2 of the proof of Stacks 07W0. Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism and
`(V, U', φ)` a triple over the span. There is a cube over the span `U' ⟵ U ⟶ V` of the triple
whose back square is the pushout `G(V, U', φ) = V ⨿_U U'` of algebraic spaces and whose front
square is the pushout `G₁ = V₁ ⨿_{U₁} U₁'` of étale scheme charts, whose four lateral squares
are cartesian and whose four northeast arrows are surjective and étale; in particular
`G₁ ⟶ G(V, U', φ)` is surjective étale. -/
@[stacks 07W2]
theorem exists_etaleChartCube_gluingData
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (T : pushoutGluingData B S hS i f) :
    ∃ (U₁ U₁' V₁ G₁ : BigFppfOver B S hS) (G : AlgebraicSpaces B S hS)
      (aG : T.obj.right.left ⟶ G) (bG : T.obj.left.left ⟶ G) (k : U₁ ⟶ U₁') (g : U₁ ⟶ V₁)
      (aG₁ : U₁' ⟶ G₁) (bG₁ : V₁ ⟶ G₁)
      (p : yoneda.obj U₁ ⟶ (pullback T.obj.right.hom i).1)
      (p' : yoneda.obj U₁' ⟶ T.obj.right.left.1)
      (q : yoneda.obj V₁ ⟶ T.obj.left.left.1) (r : yoneda.obj G₁ ⟶ G.1),
      IsPushout (pullback.fst T.obj.right.hom i)
        (CategoryTheory.PushoutGluing.sourceMap i f T) aG bG ∧
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map aG₁) ((BigFppfOver.toScheme B S hS).map bG₁) ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g) ∧
      IsPullback (yoneda.map k) p p' (pullback.fst T.obj.right.hom i).hom ∧
      IsPullback p (yoneda.map g)
        (CategoryTheory.PushoutGluing.sourceMap i f T).hom q ∧
      IsPullback (yoneda.map aG₁) p' r aG.hom ∧
      IsPullback (yoneda.map bG₁) q r bG.hom ∧
      IsSurjective B S hS p ∧ IsEtale B S hS p ∧
      IsSurjective B S hS p' ∧ IsEtale B S hS p' ∧
      IsSurjective B S hS q ∧ IsEtale B S hS q ∧
      IsSurjective B S hS r ∧ IsEtale B S hS r :=
  exists_etaleChartCube_gluingData_of_isThickening_of_isAffineHom B S hS
    (hasThickeningAffineAtlases_of_chartLift B S hS (hasEtaleChartLifts B S hS)) i f hi hf T

end AlgebraicGeometry.Space

end
