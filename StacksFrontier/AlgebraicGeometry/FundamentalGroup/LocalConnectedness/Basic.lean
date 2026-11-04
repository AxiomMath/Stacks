module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper

/-!
# Faithfulness of finite étale base change along a dominant morphism

If a morphism of schemes has dense image, then pulling back finite étale schemes along it is a
faithful functor.

## Main results

* `AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_isDominant` states that base change of
  finite étale schemes along a dominant morphism is faithful.
* `AlgebraicGeometry.eq_of_isDominant_of_finiteEtale` is the rigidity statement the faithfulness
  rests on: two morphisms into a finite étale scheme over a base that agree on a dominant
  subscheme are equal.

## Implementation notes

Finite étale schemes over a scheme are represented by Mathlib's full subcategory
`MorphismProperty.Over` for the intersection of the finite and étale morphism properties. The
base-change functor is its canonical `MorphismProperty.Over.pullback`. The source's dense-image
hypothesis is Mathlib's `AlgebraicGeometry.IsDominant` typeclass.

## References

* [Stacks Project, Tag 0BQE](https://stacks.math.columbia.edu/tag/0BQE)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The equalizer of two morphisms into an étale object of a slice category is an open
subobject of the source. -/
theorem isOpenImmersion_equalizer_ι_left
    {S : Scheme.{u}} {X Y : Over S} [Etale Y.hom]
    (f g : X ⟶ Y) : IsOpenImmersion (Limits.equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

/-- **Two maps into a finite étale scheme that agree on a dominant subscheme agree.** If
`p : Y ⟶ S` is finite étale, `f g : X ⟶ Y` have the same composite with `p`, and `f` and `g`
agree after precomposition with a dominant `j : W ⟶ X`, then `f = g`.

The equalizer of `f` and `g` in `Over S` is an open immersion into `X` (because `p` is étale,
so its diagonal is an open immersion) with closed image (because `p` is finite, so separated)
and dominant (because `j` factors through it); an open immersion that is also surjective is an
isomorphism, so the equalizer is all of `X`. -/
@[sga "7 IX 11.6.8" "partial"]
theorem eq_of_isDominant_of_finiteEtale
    {X Y S W : Scheme.{u}} (p : Y ⟶ S) [IsFinite p] [Etale p]
    {f g : X ⟶ Y} (h : f ≫ p = g ≫ p)
    (j : W ⟶ X) [IsDominant j] (hj : j ≫ f = j ≫ g) : f = g := by
  let X' : Over S := Over.mk (f ≫ p)
  let Y' : Over S := Over.mk p
  let W' : Over S := Over.mk (j ≫ f ≫ p)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let j' : W' ⟶ X' := Over.homMk j
  have : IsSeparated Y'.hom := inferInstanceAs (IsSeparated p)
  have : Etale Y'.hom := inferInstanceAs (Etale p)
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift j' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · exact Over.OverMorphism.ext hj
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have : IsOpenImmersion (equalizer.ι f' g').left := isOpenImmersion_equalizer_ι_left f' g'
  have : IsIso (equalizer.ι f' g').left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

private theorem isDominant_pullback_fst_of_isOpenMap
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsDominant f]
    (hg : IsOpenMap g) : IsDominant (pullback.fst g f) := by
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_fst]
  exact Dense.preimage IsDominant.denseRange hg

private lemma faithful_pullback_finiteEtaleProperty
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f] :
    (MorphismProperty.Over.pullback finiteEtale.{u} ⊤ f).Faithful := by
  refine ⟨fun {A B} g h hgh => ?_⟩
  apply MorphismProperty.Over.Hom.ext
  have : IsFinite A.hom := A.prop.1
  have : Etale A.hom := A.prop.2
  have : IsFinite B.hom := B.prop.1
  have : Etale B.hom := B.prop.2
  have e : (pullback.lift (pullback.fst A.hom f ≫ g.left) (pullback.snd A.hom f)
        (by rw [Category.assoc, MorphismProperty.Over.w g, pullback.condition]) :
          pullback A.hom f ⟶ pullback B.hom f) =
      pullback.lift (pullback.fst A.hom f ≫ h.left) (pullback.snd A.hom f)
        (by rw [Category.assoc, MorphismProperty.Over.w h, pullback.condition]) :=
    congrArg (fun k => k.left) hgh
  have hj : pullback.fst A.hom f ≫ g.left = pullback.fst A.hom f ≫ h.left := by
    simpa only [pullback.lift_fst] using
      congrArg (fun k => k ≫ pullback.fst B.hom f) e
  have : IsDominant (pullback.fst A.hom f) :=
    isDominant_pullback_fst_of_isOpenMap f A.hom (Scheme.Hom.isOpenMap A.hom)
  exact eq_of_isDominant_of_finiteEtale B.hom
    ((MorphismProperty.Over.w g).trans (MorphismProperty.Over.w h).symm) (pullback.fst A.hom f) hj

/-- **Stacks Project, Tag 0BQE.** Pullback of finite étale schemes along a
dominant morphism of schemes is faithful. -/
@[stacks 0BQE]
public lemma faithful_finiteEtaleBaseChange_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f] :
    (MorphismProperty.Over.pullback
      ((@IsFinite ⊓ @Etale) : MorphismProperty Scheme.{u}) ⊤ f).Faithful :=
  faithful_pullback_finiteEtaleProperty f

end AlgebraicGeometry
