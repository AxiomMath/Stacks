module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.AffineLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcSheaf

/-!
# The relative Hom functor is affine of finite presentation as soon as it is over affine bases

In Situation 08JT, the relative Hom functor `Hom(F, G)` of Stacks 08JT is an fpqc sheaf on the
test schemes over the base (Stacks 08JV), and its restriction to the test schemes over a test
scheme `Z ⟶ base` is the relative Hom functor of the base-changed situation of Stacks 08JW.  So
`Hom(F, G)` is an algebraic space affine and of finite presentation over the base as soon as,
for every affine scheme `Z` of the site and every morphism `Z ⟶ base`, the relative Hom functor
of the base change to `Z` is represented by a scheme affine and of finite presentation over `Z`.

This is the first paragraph of the proofs of Stacks 08K6 and 08JX — "we may check
representability étale locally on the base … hence we may assume that `B` is an affine scheme"
— for the relative Hom functor.

## Main results

* `HomSituation.homFunctor_eq`: the relative Hom functor does not depend on the coherence datum
  it is formed with.
* `HomSituation.isSheaf_homFunctor`: Stacks 08JV at an arbitrary coherence datum.
* `HomSituation.isAffineFinitePresentationAlgebraicSpaceOverBase_of_baseChange`: the reduction to
  an affine base.

## References

* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 08JV](https://stacks.math.columbia.edu/tag/08JV)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : HomSituation B S hS)

/-- **The relative Hom functor does not depend on the coherence datum.**  Only the two functor
laws of `AlgebraicGeometry.Space.HomSituation.homFunctor` use the datum, and they are
propositions. -/
theorem homFunctor_eq (hc hc' : ModulePushforwardCoherence B S hS) :
    s.homFunctor hc = s.homFunctor hc' :=
  rfl

/-- **Stacks 08JV at an arbitrary coherence datum**: the relative Hom functor is an fpqc sheaf on
the test schemes over the base. -/
theorem isSheaf_homFunctor (hc : ModulePushforwardCoherence B S hS) :
    Presheaf.IsSheaf (fpqcTopology s.base) (s.homFunctor hc) :=
  s.isSheaf_homFunctor_fpqc

/-- **The relative Hom functor is an algebraic space affine and of finite presentation over the
base as soon as it is one over every affine base change.**  If, for every affine scheme `Z` of
the site and every morphism `p : Z ⟶ base`, the relative Hom functor of the base-changed
situation of Stacks 08JW is represented by a scheme affine and of finite presentation over `Z`,
then `Hom(F, G)` is an algebraic space affine and of finite presentation over the base.

The restriction of `Hom(F, G)` to the test schemes over `Z` is the Hom functor of the base change
(Stacks 08JW), and `Hom(F, G)` is an fpqc sheaf (Stacks 08JV), so the representability criterion
`AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_of_affineLocal` applies. -/
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_baseChange
    (hc : ModulePushforwardCoherence B S hS)
    (h : ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ p : (schemeSpaceFunctor B S hS).obj Z ⟶ s.base,
        ∃ (W : BigFppfOver B S hS) (w : W ⟶ Z),
          _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
            LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
              Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ⋙
                  uliftFunctor.{u + 1, u} ≅
                (s.baseChangedSituation p).homFunctor (modulePushforwardCoherence B S hS))) :
    s.IsAffineFinitePresentationAlgebraicSpaceOverBase hc := by
  refine isAffineFinitePresentationAlgebraicSpaceOver_of_affineLocal _ (s.isSheaf_homFunctor hc)
    fun Z hZ => ?_
  obtain ⟨W, w, hw, hwfp, ⟨e⟩⟩ := h Z.left hZ Z.hom
  exact ⟨W, w, hw, hwfp, ⟨e ≪≫ s.homFunctorBaseChange Z.hom⟩⟩

end AlgebraicGeometry.Space.HomSituation

end
