module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcompose
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Post-composition is left adjoint to base change, and `U ⨯ -` is base change

Let `B` be a big étale site containing a scheme `X`, and let `U` be an object of the small
étale site of `X`, with étale structure morphism `p_U : U ⟶ X`. Post-composition with `p_U` is
left adjoint to base change along `p_U`, and base change along `p_U`, read on the slice at `U`
through the localization equivalence, is the binary product `W ↦ U ⨯ W`.

## Main results

* `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction`: post-composition with `p_U` is
  left adjoint to base change along `p_U`.
* `AlgebraicGeometry.SmallEtale.baseChangeIsoStarCompInverse`: base change along `p_U` is
  `U ⨯ -` followed by the localization equivalence.
* `AlgebraicGeometry.SmallEtale.baseChangeLocalizationIsoStar`: the same identification in the
  form `(ε_{p_U})^{-1} ⋙ localization ≅ U ⨯ -`.

## References

* [Stacks Project, Tag 03PM](https://stacks.math.columbia.edu/tag/03PM)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- **Post-composition with `p_U : U ⟶ X` is left adjoint to base change along `p_U`**, as
functors between the small étale site of `U` and the small étale site of `X`. -/
@[sga "3 I 1.6" "special case"]
public def postcomposeBaseChangeAdjunction :
    postcompose B X hX U ⊣ smallEtaleBaseChange B U.obj.hom :=
  letI := hasPullbacks_bigEtaleSite B
  (Over.mapPullbackAdj U.obj.hom).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι
      (BigEtaleOver.IsEtaleOver B U.obj.left.obj U.obj.left.property))
    (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B X hX))
    (eqToIso rfl)
    (eqToIso (smallEtaleBaseChange_comp_inclusion B U.obj.hom).symm)

/-- Post-composition with `p_U`, exhibited as the localization equivalence followed by the slice
projection, is left adjoint to `U ⨯ -` followed by the inverse of the localization
equivalence. -/
@[sga "3 I 1.6" "special case"]
public def postcomposeStarAdjunction :
    postcompose B X hX U ⊣ Over.star U ⋙ (localizationEquivalence B X hX U).inverse :=
  ((localizationEquivalence B X hX U).toAdjunction.comp (Over.forgetAdjStar U)).ofNatIsoLeft
    (eqToIso (localizationEquivalence_restriction B X hX U))

/-- **Base change along `p_U` is `U ⨯ -`, read through the localization equivalence.** -/
public def baseChangeIsoStarCompInverse :
    smallEtaleBaseChange B U.obj.hom ≅
      Over.star U ⋙ (localizationEquivalence B X hX U).inverse :=
  (postcomposeBaseChangeAdjunction B X hX U).rightAdjointUniq
    (postcomposeStarAdjunction B X hX U)

/-- **A binary product with `U` in the small étale site of `X` is the fibre product over `X`.**
Base change along `p_U`, read back on the slice at `U` through the localization equivalence, is
`W ↦ U ⨯ W`. -/
public def baseChangeLocalizationIsoStar :
    smallEtaleBaseChange B U.obj.hom ⋙ (localizationEquivalence B X hX U).functor ≅
      Over.star U :=
  Functor.isoWhiskerRight (baseChangeIsoStarCompInverse B X hX U) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (localizationEquivalence B X hX U).counitIso ≪≫
    Functor.rightUnitor _

end AlgebraicGeometry.SmallEtale

end
