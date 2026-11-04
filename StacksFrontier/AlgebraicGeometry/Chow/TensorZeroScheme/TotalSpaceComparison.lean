module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.InverseSituationBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionFactor

/-!
# The zero section under base change of a line bundle

Let `D` be a line-bundle situation: a morphism of schemes `f : X ⟶ S` together with an invertible
`𝒪_X`-module `L`, and let `g : X' ⟶ X` be an arbitrary morphism of schemes. The canonical
morphism of total spaces `Tot(g^*L) ⟶ Tot(L)` of
`Stacks.LineBundle.Situation.baseChangeToTotalSpace` carries the zero section to the zero
section. The same holds for the line bundle `L(M) = Tot(M^{⊗ -1})` of an invertible module `M`,
where the canonical morphism is `Stacks.LineBundle.totalSpaceBaseChange`.

## Main results

* `Stacks.LineBundle.pullbackPushforwardTranspose_zero`: the transposition across the
  pullback–pushforward adjunction of a base change sends the zero morphism to zero.
* `Stacks.LineBundle.Situation.zeroSection_comp_baseChangeToTotalSpace`: the canonical morphism
  of total spaces along a base change carries the zero section to the zero section, for an
  arbitrary line-bundle situation.
* `Stacks.LineBundle.zeroSection_comp_totalSpaceBaseChange`: the same for the line bundle of an
  invertible module: `o' ≫ β = q ≫ o`.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

/-! ### The zero section under the base change of a situation -/

/-- For `g : Y' ⟶ Y`, an `𝒪_Y`-module `A` and `h : W ⟶ Y'`, the transpose of the zero morphism
across the pullback–pushforward adjunction of `g`, followed by the comparison
`Scheme.Modules.pushforwardComp h g` of the composite direct images of `𝒪_W`, is zero. -/
theorem pullbackPushforwardTranspose_zero {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (A : Y.Modules)
    {W : Scheme.{u}} (h : W ⟶ Y') :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A
          ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)) 0 ≫
        (Scheme.Modules.pushforwardComp h g).hom.app (SheafOfModules.unit W.ringCatSheaf) = 0 := by
  rw [Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

variable (D : Situation.{u}) {X' : Scheme.{u}} (g : X' ⟶ D.X)

/-- The canonical morphism of total spaces `Tot(g^*L) ⟶ Tot(L)` along a base change
`g : X' ⟶ X` carries the zero section to the zero section. -/
theorem Situation.zeroSection_comp_baseChangeToTotalSpace :
    (D.baseChange g).zeroSection ≫ D.baseChangeToTotalSpace g = g ≫ D.zeroSection := by
  refine (D.totalSpaceHomEquiv X').injective ?_
  refine Eq.trans (D.totalSpaceHomEquiv_comp_baseChangeToTotalSpace g
    (D.baseChange g).zeroSection) ?_
  refine Eq.trans (congrArg (D.baseChangePoint (W := X') g)
    (D.baseChange g).totalSpaceHomEquiv_zeroSection) ?_
  refine Eq.trans ?_ (D.totalSpaceHomEquiv_comp_zeroSection g).symm
  exact Eq.trans
    (sigma_mk_congr (Eq.trans (D.transposeEquiv_apply g _ _)
      (pullbackPushforwardTranspose_zero g D.L _)))
    (sigma_mk_zero_congr D.L (Category.id_comp g))

/-! ### The zero section under the base change of a line bundle -/

variable {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-- For an invertible `𝒪_Y`-module `M` and `q : Y' ⟶ Y`, the canonical morphism
`β : L(q^*M) ⟶ L(M)` carries the zero section to the zero section: `o' ≫ β = q ≫ o`. -/
theorem zeroSection_comp_totalSpaceBaseChange :
    (inverseSituation Y' ((Scheme.Modules.pullback q).obj M)).zeroSection ≫
        totalSpaceBaseChange q M = q ≫ (inverseSituation Y M).zeroSection :=
  have := isInvertible_baseChange_inverse q M
  Eq.trans
    (Category.assoc (inverseSituation Y' ((Scheme.Modules.pullback q).obj M)).zeroSection
      (inverseSituationBaseChangeIso q M).hom
      ((inverseSituation Y M).baseChangeToTotalSpace q)).symm
    (Eq.trans
      (congrArg
        (fun z : Y' ⟶ ((inverseSituation Y M).baseChange q).totalSpace =>
          z ≫ (inverseSituation Y M).baseChangeToTotalSpace q)
        (((inverseSituation Y M).baseChange q).zeroSection_comp_totalSpaceIsoOfIso_hom
          (inverseSituation Y' ((Scheme.Modules.pullback q).obj M)).L
          (inverseSituationPullbackIso q M)))
      ((inverseSituation Y M).zeroSection_comp_baseChangeToTotalSpace q))

end Stacks.LineBundle

end
