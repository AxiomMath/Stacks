module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeOfThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening

/-!
# Surjective étale scheme charts lift across thickenings

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` and let `p : U ⟶ X` be a
surjective étale morphism from a scheme. Then there is a surjective étale morphism
`p' : U' ⟶ X'` from a scheme with `U = X ×_{X'} U'`, the morphism `U ⟶ U'` being a thickening
of schemes. This is `AlgebraicGeometry.Space.HasEtaleChartLifts`, the chart form of the
essential surjectivity half of [Stacks Project, Tag 05ZS].

## Main results

* `AlgebraicGeometry.Space.hasEtaleChartLifts`: surjective étale scheme charts lift across
  every thickening of algebraic spaces over `S`.

## Implementation notes

The étale space `U ⟶ X` is an object of the spaces-étale site of `X`; by the essential
surjectivity of base change along a thickening ([Stacks Project, Tag 05ZH],
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickeningHom`) it is the base change
of an algebraic space `V'` étale over `X'`. The projection `U ⟶ V'` is a base change of `i`,
hence a thickening, so `V'` is a scheme by [Stacks Project, Tag 05ZR]
(`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`). It is
surjective over `X'` because a thickening is surjective on points, and the morphism of charts
is a thickening of schemes because it is the base change of `i` along the chart of `X'`.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme chart `p'` of `X'` is surjective if it receives, compatibly with a thickening
`i : X ⟶ X'`, a map from a surjective scheme chart `p` of `X`. -/
private theorem surjective_of_comp_eq_of_isThickeningHom {X X' : AlgebraicSpaces B S hS}
    {i : X ⟶ X'} (hi : IsThickeningHom B S hS i) {U U' : BigFppfOver B S hS}
    {p : yoneda.obj U ⟶ X.1}
    {p' : yoneda.obj U' ⟶ X'.1} {k : U ⟶ U'} (w : yoneda.map k ≫ p' = p ≫ i.hom)
    (hp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hp' : yoneda.relativelyRepresentable p') :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p' := by
  refine (surjective_iff_pointsMap_surjective B S hS (isAlgebraicSpace_yoneda B S hS _)
    X'.2 p' hp').2 fun x' => ?_
  obtain ⟨x, rfl⟩ := hi.surjective_pointsMap x'
  obtain ⟨y, rfl⟩ := (surjective_iff_pointsMap_surjective B S hS
    (isAlgebraicSpace_yoneda B S hS _) X.2 p hp.1).1 hp x
  refine ⟨pointsMap B S hS _ (yoneda.map k) y, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS _ p'), ← pointsMap_comp, w,
    pointsMap_comp, Function.comp_apply]

/-- **Surjective étale scheme charts lift across thickenings.** Every surjective étale scheme
chart `p : U ⟶ X` of an algebraic space lifts across every thickening `i : X ⟶ X'` of algebraic
spaces over `S` to a surjective étale scheme chart `p' : U' ⟶ X'` with `U = X ×_{X'} U'`, the
morphism of charts `U ⟶ U'` being a thickening of schemes. -/
theorem hasEtaleChartLifts : HasEtaleChartLifts B S hS := by
  intro X X' i hi U p hpsurj hpet
  have := hi.mono
  -- `U` as an object of the spaces-étale site of `X`, and its lift `V'` over `X'`
  let C : SpacesEtale B S hS X :=
    ⟨Over.mk (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X),
      isEtale_of_presheaf_etale B S hS hpet⟩
  have := essSurj_spacesBaseChange_of_isThickeningHom B S hS i hi
  let V' := (spacesBaseChange B S hS i).functor.objPreimage C
  let ε := (SpacesEtale.toSpaces B S hS X).mapIso
    ((spacesBaseChange B S hS i).functor.objObjPreimageIso C)
  have sq : IsPullback (ε.inv ≫ (spacesBaseChange B S hS i).projection.app V')
      (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X) V'.1.hom i := by
    refine IsPullback.of_iso ((spacesBaseChange B S hS i).isPullback V') ε (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
    rw [Iso.refl_hom, Category.comp_id]
    exact (Over.w ((spacesBaseChange B S hS i).functor.objObjPreimageIso C).hom.hom).symm
  -- `V'` is a scheme, by Stacks 05ZR
  have hrep : V'.1.left.1.IsRepresentable :=
    isRepresentable_of_isThickeningHom_of_isRepresentable B S hS _
      (isThickeningHom_of_isPullback B S hS sq.flip hi)
      (inferInstance : (yoneda.obj U).IsRepresentable)
  let eU := Functor.reprW V'.1.left.1
  let p' : yoneda.obj (Functor.reprX V'.1.left.1) ⟶ X'.1 := eU.hom ≫ V'.1.hom.hom
  let top : yoneda.obj U ⟶ V'.1.left.1 :=
    (ε.inv ≫ (spacesBaseChange B S hS i).projection.app V').hom
  obtain ⟨k, hk0⟩ : ∃ k : U ⟶ Functor.reprX V'.1.left.1, yoneda.map k = top ≫ eU.inv :=
    ⟨_, Functor.map_preimage _ _⟩
  have sqP : IsPullback (yoneda.map k) p p' i.hom :=
    IsPullback.of_iso (AlgebraicSpaces.isPullback_hom B S hS sq) (Iso.refl _) eU.symm
      (Iso.refl _) (Iso.refl _) (by simp [hk0, top]) (by simp) (by simp [p']) (by simp)
  -- étaleness of `p'`
  have hp'et : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p' :=
    V'.2 _ eU.hom (presheaf_etale_of_iso B S hS eU)
  refine ⟨Functor.reprX V'.1.left.1, p', k,
    surjective_of_comp_eq_of_isThickeningHom B S hS hi sqP.w hpsurj hp'et.1, hp'et, sqP, ?_⟩
  -- the morphism of charts is the base change of `i` along `p'`, a thickening
  obtain ⟨J, j, η, hpb, hjci, hjsurj⟩ :=
    exists_chart_isClosedImmersion_of_isThickening_range B S hS i hi.2 _ p'
  let φ := sqP.isoIsPullback _ _ hpb
  have hk : k = yoneda.preimage φ.hom ≫ j := yoneda.map_injective <| by
    rw [Functor.map_comp, Functor.map_preimage]
    exact (sqP.isoIsPullback_hom_fst _ _ hpb).symm
  have : IsIso (yoneda.map (yoneda.preimage φ.hom)) := by
    rw [Functor.map_preimage]
    infer_instance
  have : IsIso (yoneda.preimage φ.hom) := Yoneda.fullyFaithful.isIso_of_isIso_map _
  have : Surjective ((BigFppfOver.toScheme B S hS).map j) := ⟨hjsurj⟩
  rw [hk, Functor.map_comp]
  exact ⟨inferInstance, (inferInstance : Surjective (_ ≫ _)).surj⟩

end AlgebraicGeometry.Space

end
