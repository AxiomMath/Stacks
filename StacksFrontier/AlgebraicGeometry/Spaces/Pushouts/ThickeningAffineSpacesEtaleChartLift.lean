module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTopologicalInvarianceChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickeningAdditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtaleOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithfulThickening
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
import all StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces

/-!
# Stacks 05ZS at a thickening of unbounded order: small étale sites and chart lifts

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`. Base change along `i` is an
equivalence of small étale sites of scheme charts (given the two hypotheses `h09YA` and
`hFinitePresentation` of Stacks 07VW), and every surjective étale scheme chart of `X` lifts to one
of `X'` across `i`.

## Main results

* `AlgebraicGeometry.Space.smallEtalePullback_isEquivalence_of_isThickeningHom`
* `AlgebraicGeometry.Space.exists_etaleChart_lift_of_isThickeningHom`

## References

* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfOver.hasSheafify_type

/-- **Stacks 05ZS on the small étale sites of scheme charts, at a thickening of unbounded
order.** Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`. Base change
`V' ↦ X ×_{X'} V'` is an equivalence from the small étale site of `X'` to that of `X`.

This is Stacks 07VW in the form
`AlgebraicGeometry.Space.smallEtalePullback_isEquivalence_of_chartsBounded`, with Stacks 07SQ
applied in its bounded form, and with three of its four remaining hypotheses discharged: `i` is
integral, universally injective and surjective by Stacks 05ZL
(`AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_of_isThickeningHom`),
and the Stacks 05ZH equivalence of *spaces*-étale sites that Stacks 07VW takes as its input is
available at a thickening of unbounded order,
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickeningHom`. What remains
carried are `h09YA` and `hFinitePresentation`, so the statement is not registered as
Stacks 05ZS. -/
theorem smallEtalePullback_isEquivalence_of_isThickeningHom
    {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') (hi : IsThickeningHom B S hS i)
    (h09YA : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS G →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal G →
      ∃ P : IntegralFiniteSystem B S hS g,
        letI := P.indexPreorder; ChartsBounded B S hS P.diagram)
    (hFinitePresentation : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS F →
      IsAffineSpace B S hS G) :
    (smallEtalePullback B S hS i
      (isIntegralHom_of_isClosedImmersion B S hS i.hom hi.isClosedImmersion)).IsEquivalence :=
  smallEtalePullback_isEquivalence_of_chartsBounded B S hS i _
    (universallyInjective_of_isThickeningHom B S hS hi) hi.surjective_pointsMap
    (isEquivalence_spacesBaseChange_of_isThickeningHom B S hS i hi) h09YA hFinitePresentation

/-- **Stacks 05ZS, the lift of an étale scheme chart across a thickening of unbounded order.**
Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` and let `p : U ⟶ X` be a
surjective étale scheme chart of `X`. Then there is a surjective étale scheme chart
`p' : U' ⟶ X'` of `X'` and a morphism `k : U ⟶ U'` of the site making
`U = X ×_{X'} U'`, and `k` is a thickening of schemes.

These are exactly the fields `U'`, `p'`, `k`, `etale_p'`, `surjective_p'`,
`isPullback_thickening` and `isThickening_k` of
`AlgebraicGeometry.Space.ThickeningAffineAtlas`.

The chart is produced by essential surjectivity in
`AlgebraicGeometry.Space.smallEtalePullback_isEquivalence_of_isThickeningHom`, transported from
`AlgebraicGeometry.Space.smallEtalePullback` to the chart base change
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4) — the two agree because both
restrict the spaces-étale base change along the fully faithful comparison functor of
Stacks 03G1. The cartesian square is then the one carried by the representability of `i`, and
`k` is a thickening of schemes because it is a represented base change of `i`, which is a
closed immersion and surjective. Surjectivity of `p'` is read off the points: `p ≫ i` is
surjective on points, and it factors through `p'`. -/
theorem exists_etaleChart_lift_of_isThickeningHom
    {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') (hi : IsThickeningHom B S hS i)
    (h09YA : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS G →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal G →
      ∃ P : IntegralFiniteSystem B S hS g,
        letI := P.indexPreorder; ChartsBounded B S hS P.diagram)
    (hFinitePresentation : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS F →
      IsAffineSpace B S hS G)
    {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1)
    (hpS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hpE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p) :
    ∃ (U' : BigFppfOver B S hS) (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U'),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p' ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p' ∧
      IsPullback (yoneda.map k) p p' i.hom ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k) := by
  have hint := isIntegralHom_of_isClosedImmersion B S hS i.hom hi.isClosedImmersion
  have hrep : yoneda.relativelyRepresentable i.hom := hi.isClosedImmersion.rep
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := smallEtalePullback_isEquivalence_of_isThickeningHom B S hS i hi h09YA
    hFinitePresentation
  have e : smallBaseChange B S hS i hrep ≅ smallEtalePullback B S hS i hint :=
    Functor.fullyFaithfulCancelRight (comparisonFunctor B S hS X)
      (smallBaseChange_comparison B S hS i hrep ≪≫
        (smallEtalePullbackComparisonIso B S hS i hint).symm)
  have : (smallBaseChange B S hS i hrep).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  -- the given chart, as an object of the small étale site of `X`
  let C : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk p, hpE⟩
  let D : SmallEtale B S hS X'.1 := (smallBaseChange B S hS i hrep).objPreimage C
  let ψ : ((smallBaseChange B S hS i hrep).obj D).1 ≅ C.1 :=
    (ObjectProperty.ι (IsEtaleChart B S hS X.1)).mapIso
      ((smallBaseChange B S hS i hrep).objObjPreimageIso C)
  let eL : hrep.pullback D.1.hom ≅ U := (CostructuredArrow.proj yoneda X.1).mapIso ψ
  have hwL : yoneda.map eL.hom ≫ p = hrep.fst D.1.hom := CostructuredArrow.w ψ.hom
  have hsq : IsPullback (yoneda.map (eL.inv ≫ hrep.snd D.1.hom)) p D.1.hom i.hom := by
    refine (hrep.isPullback D.1.hom).flip.of_iso (yoneda.mapIso eL) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom] using hwL.symm
    · simp
    · simp
  refine ⟨D.1.left, D.1.hom, eL.inv ≫ hrep.snd D.1.hom, ?_, D.property, hsq, ?_⟩
  · -- surjectivity of the lifted chart, on points
    refine (presheafSurjective_iff_isSurjective_yoneda B S hS X'.1 X'.property
      D.1.left D.1.hom).mpr ?_
    have hcomp : Function.Surjective (pointsMap B S hS (yoneda.obj U) (p ≫ i.hom)) := by
      rw [pointsMap_comp]
      exact hi.surjective_pointsMap.comp
        ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.property U p).mp hpS)
    rw [← hsq.w, pointsMap_comp] at hcomp
    exact hcomp.of_comp
  · -- the morphism of charts is a thickening of schemes
    have hci : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hrep.snd D.1.hom)) :=
      hi.isClosedImmersion.property_snd D.1.hom
    have hsj : _root_.AlgebraicGeometry.Surjective
        ((BigFppfOver.toScheme B S hS).map (hrep.snd D.1.hom)) :=
      hi.surjective.property_snd D.1.hom
    rw [Functor.map_comp]
    exact ⟨inferInstance, (inferInstance :
      _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map eL.inv ≫
        (BigFppfOver.toScheme B S hS).map (hrep.snd D.1.hom))).surj⟩

end AlgebraicGeometry.Space

end
