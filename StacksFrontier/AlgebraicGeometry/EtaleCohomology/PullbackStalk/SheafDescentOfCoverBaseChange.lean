module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjectiveUnconditional
public import StacksFrontier.CategoryTheory.Sites.Descent.EffectiveDescentOfCoverBaseChange

/-!
# Descent of small étale sheaves, tested after an integral or proper surjective base change

Let `f : X ⟶ Y` be a morphism of schemes and let `g : Z ⟶ Y` be a surjective integral or a
surjective proper morphism. [Stacks, Tag 0GF1] says that if descent of étale sheaves is effective
along the base changes `X ×_Y Z ⟶ Z` and `X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z` of `f`, then it is
effective along `f`. This file proves it for the library's descent functor
`AlgebraicGeometry.smallEtaleSheafDescentFunctor`.

## Main results

* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_baseChange_of_surjective`:
  [Stacks, Tag 0GF1].

## Implementation notes

The source calls the lemma a formal consequence of [Stacks, Tag 0GEZ] and [Stacks, Tag 0GF0].
The formal part is
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_baseChange`, which needs, besides
effective descent along `g` and along its base changes ([Stacks, Tag 0GEZ] resp.
[Stacks, Tag 0GF0]), that morphisms out of an inverse image along the projection
`Z ×_Y Z ×_Y Z ⟶ Z ×_Y Z` are detected after base change to `X ×_Y (Z ×_Y Z ×_Y Z)`: this is
where the cocycle condition of the glued descent datum is checked. That projection is a base
change of `g`, so its direct image commutes with base change, by [Stacks, Tag 0EYP] resp.
[Stacks, Tag 0A3U], and the detection follows from the faithfulness that effective descent along
`X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z` provides
(`CategoryTheory.Pseudofunctor.eq_of_map_eq_of_isIso_mateEquiv`).

## References

* [Stacks Project, Tag 0GF1](https://stacks.math.columbia.edu/tag/0GF1)
* [Stacks Project, Tag 0GEZ](https://stacks.math.columbia.edu/tag/0GEZ)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y)

/-- The base change `X ×_Y (Z ×_Y Z ×_Y Z) ⟶ X ×_Y (Z ×_Y Z)` of the projection
`Z ×_Y Z ×_Y Z ⟶ Z ×_Y Z` onto the first two factors. -/
abbrev coverBaseChangeProj :
    pullback f (pullback.fst (pullback.fst g g ≫ g) g ≫ pullback.fst g g ≫ g) ⟶
      pullback f (pullback.fst g g ≫ g) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst (pullback.fst g g ≫ g) g)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The square formed by `coverBaseChangeProj B f g`, the projection `Z ×_Y Z ×_Y Z ⟶ Z ×_Y Z`
and the second projections of `X ×_Y (Z ×_Y Z ×_Y Z)` and `X ×_Y (Z ×_Y Z)` is a pullback square.
-/
lemma isPullback_coverBaseChangeProj :
    IsPullback (pullback.snd f (pullback.fst (pullback.fst g g ≫ g) g ≫ pullback.fst g g ≫ g))
      (coverBaseChangeProj B f g) (pullback.fst (pullback.fst g g ≫ g) g)
      (pullback.snd f (pullback.fst g g ≫ g)) := by
  refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f (pullback.fst g g ≫ g))).flip
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback f _

variable {B f g}

/-- A morphism property stable under base change holds for `pullback.fst t g` if it holds for `g`.
-/
private lemma inclusion_map_pullback_fst {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] (hg : P (B.inclusion.map g)) {T : B.Scheme} (t : T ⟶ Y) :
    P (B.inclusion.map (pullback.fst t g)) :=
  MorphismProperty.of_isPullback
    (B.inclusion.map_isPullback (IsPullback.of_hasPullback t g).flip) hg

/-- The formal reduction, for the explicit pseudofunctor of small étale sheaves: effective descent
along `g` and its base changes and the base change theorem for the projection
`Z ×_Y Z ×_Y Z ⟶ Z ×_Y Z` reduce effective descent along `f` to effective descent along the base
changes `X ×_Y Z ⟶ Z` and `X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z`. -/
lemma smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_baseChange
    (hg : (smallEtaleSheafInverseImageDescentFunctor B g).IsEquivalence)
    (heff : ∀ ⦃T : B.Scheme⦄ (t : T ⟶ Y),
      (smallEtaleSheafInverseImageDescentFunctor B (pullback.fst t g)).IsEquivalence)
    (hbc : ∀ N, IsIso ((smallEtaleBaseChangeNatTrans.{u} B
      (pullback.snd f (pullback.fst (pullback.fst g g ≫ g) g ≫ pullback.fst g g ≫ g))
      (coverBaseChangeProj B f g) (pullback.fst (pullback.fst g g ≫ g) g)
      (pullback.snd f (pullback.fst g g ≫ g)) (isPullback_coverBaseChangeProj B f g).w).app N))
    (hZ : (smallEtaleSheafInverseImageDescentFunctor B (pullback.snd f g)).IsEquivalence)
    (hZZ : (smallEtaleSheafInverseImageDescentFunctor B
      (pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence) :
    (smallEtaleSheafInverseImageDescentFunctor B f).IsEquivalence := by
  refine Pseudofunctor.isEquivalence_toDescentData_of_baseChange f g hg
    (fun T t ↦ Pseudofunctor.isPrestackFor_pullback_of_equivalence _ (fun _ : Unit ↦ g) t
      (fun _ ↦ pullback t g) (fun _ ↦ pullback.fst t g) (fun _ ↦ pullback.snd t g)
      (fun _ ↦ IsPullback.of_hasPullback t g) (heff t)) hZ hZZ ?_
  intro M N u v huv
  refine Pseudofunctor.eq_of_map_eq_of_isIso_mateEquiv (isPullback_coverBaseChangeProj B f g).w
    (smallEtaleSheafPseudofunctorAdjunction B _) (smallEtaleSheafPseudofunctorAdjunction B _)
    ?_ (fun a b h ↦ (smallEtaleSheafInverseImageDescentFunctor B
      (pullback.snd f (pullback.fst g g ≫ g))).map_injective
        (Pseudofunctor.DescentData.hom_ext fun _ ↦ h)) u v huv
  have h := mateEquiv_commSqTwoSquare_smallEtaleSheafInverseImagePseudofunctor B _ _ _ _
    (isPullback_coverBaseChangeProj B f g).w
  have := hbc N
  rw [← h] at this
  exact this

/-- **Descent of small étale sheaves, tested after a surjective integral or proper base
change.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of a big étale site, with `g` surjective
and either integral or proper. If the functors from sheaves on the small étale sites of `Z` and
of `Z ×_Y Z` to descent data for `{X ×_Y Z ⟶ Z}` and for `{X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}` are
equivalences of categories, then so is the functor from sheaves on the small étale site of `Y`
to descent data for `{X ⟶ Y}`. -/
@[stacks 0GF1]
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_baseChange_of_surjective
    (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective (B.inclusion.map g)]
    (hg : IsIntegralHom (B.inclusion.map g) ∨ IsProper (B.inclusion.map g))
    (hZ : (smallEtaleSheafDescentFunctor B (pullback.snd f g)).IsEquivalence)
    (hZZ : (smallEtaleSheafDescentFunctor B
      (pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  rw [isEquivalence_smallEtaleSheafDescentFunctor_iff] at hZ hZZ ⊢
  have hsurj : ∀ ⦃T : B.Scheme⦄ (t : T ⟶ Y), Surjective (B.inclusion.map (pullback.fst t g)) :=
    fun _ t ↦ inclusion_map_pullback_fst (P := @Surjective) ‹_› t
  have sq := B.inclusion.map_isPullback (isPullback_coverBaseChangeProj B f g)
  have hdesc :=
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
  rcases hg with hg | hg
  · have hint : ∀ ⦃T : B.Scheme⦄ (t : T ⟶ Y), IsIntegralHom (B.inclusion.map (pullback.fst t g)) :=
      fun _ t ↦ inclusion_map_pullback_fst (P := @IsIntegralHom) ‹_› t
    have := hint (pullback.fst g g ≫ g)
    refine smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_baseChange
      (smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective B g)
      (fun _ t ↦ have := hsurj t; have := hint t
        smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective B _)
      (fun N ↦ isIso_smallEtaleBaseChangeNatTrans_app_of_isIntegralHom B _ _ _ _ sq _ N) hZ hZZ
  · have hprop : ∀ ⦃T : B.Scheme⦄ (t : T ⟶ Y), IsProper (B.inclusion.map (pullback.fst t g)) :=
      fun _ t ↦ inclusion_map_pullback_fst (P := @IsProper) ‹_› t
    have := hprop (pullback.fst g g ≫ g)
    have h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
        (f' : X' ⟶ Y') (sq : IsPullback g' f' f g), IsProper f →
          IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w) :=
      fun f g g' f' sq _ ↦ Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper
        f g g' f' sq
    have hbc := SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange B
      _ _ _ _ (isPullback_coverBaseChangeProj B f g).w (h0A3U _ _ _ _ sq ‹_›)
    refine smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_baseChange
      (hdesc B g h0A3U)
      (fun _ t ↦ have := hsurj t; have := hprop t; hdesc B _ h0A3U)
      (fun N ↦ inferInstance) hZ hZZ

end AlgebraicGeometry

end
