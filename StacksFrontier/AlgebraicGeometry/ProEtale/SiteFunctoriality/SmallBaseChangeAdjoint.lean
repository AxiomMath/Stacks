module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.CategoryTheory.Sites.PushforwardFullyFaithful

/-!
# Small pro-étale base change with a fully faithful left adjoint

Let `f : T ⟶ S` be a morphism in a big pro-étale site and let `u` be the induced base change
functor from the small pro-étale site of `S` to that of `T`.  The direct image of the associated
morphism of topoi is restriction along `u`, so as soon as `u` admits a fully faithful left
adjoint `v`, that direct image is fully faithful and the canonical map `f⁻¹f_*F ⟶ F` is an
isomorphism.  The inverse image commutes with limits as soon as it is itself a right adjoint.

These are the three assertions of Stacks 09AA for `f`, each carrying as a hypothesis the input
that Stacks 09AA obtains from the affine case: the left adjoint `v` of Stacks 09BK, and the left
adjoint `i^{Sh}_!` of the inverse image of Stacks 09BL (3).

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleMorphismPushforwardFullyFaithfulOfAdjoint` — the
  direct image is fully faithful when base change has a fully faithful left adjoint.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_isIso_counit_of_adjoint` — in that case the
  counit `f⁻¹f_*F ⟶ F` is an isomorphism.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_inverseImage_preservesLimits` — the inverse
  image commutes with limits when it has a left adjoint.

## Implementation notes

The adjoint `v` is a hypothesis, not a construction: no left adjoint of pro-étale base change is
available here.  Continuity of `v` is not required, because full faithfulness of the direct
image is settled on underlying presheaves.

The statements below are for an arbitrary morphism `f` of the chosen big site, which is the
generality the arguments have; the closed-immersion hypothesis of Stacks 09AA enters only in
producing the two adjoints.  For a closed immersion the three assertions hold with no hypothesis
at all, by the Zariski reduction to the affine case of Stacks 09BL in
`StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedImmersionEmbedding`:
`smallProetaleMorphism_inverseImage_preservesLimits_of_isClosedImmersion`,
`smallProetaleMorphism_pushforward_fullyFaithful_of_isClosedImmersion` and
`smallProetaleMorphism_counit_isIso_of_isClosedImmersion`, all in the namespace
`AlgebraicGeometry.ProEtale`.

Base change is continuous because it is a morphism of sites, and the direct image recorded in
`AlgebraicGeometry.ProEtale.smallProetaleMorphism` is the pushforward attached to that
continuity; the two statements about it are therefore instances of
`CategoryTheory.Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint`.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)
  {v : SmallProetale B T.obj T.property ⥤ SmallProetale B S.obj S.property}
  (adjv : v ⊣ smallProetaleBaseChange B T S f)

/-- **Stacks 09AA (2) given the adjoint of Stacks 09BK.** If small pro-étale base change along
`f` admits a fully faithful left adjoint, the direct image `f_*` on small pro-étale sheaves of
sets is fully faithful.

The direct image is restriction along base change, which is fully faithful on presheaves because
restriction along the left adjoint is a left adjoint of it with invertible counit. -/
@[stacks 09AA "(2), the direct image is fully faithful, given that pro-etale base change admits \
a fully faithful left adjoint -- the adjoint that Tag 09BK supplies for a closed immersion"]
public noncomputable def smallProetaleMorphismPushforwardFullyFaithfulOfAdjoint
    [v.Full] [v.Faithful] :
    (smallProetaleMorphism B T S f).pushforward.FullyFaithful := by
  letI := (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  change ((smallProetaleBaseChange B T S f).sheafPushforwardContinuous
    (Type (u + 1)) (SmallProetale.topology B S.obj S.property)
    (SmallProetale.topology B T.obj T.property)).FullyFaithful
  exact Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint _ _ adjv _ _

include adjv in
/-- **Stacks 09AA (3) given the adjoint of Stacks 09BK.** If small pro-étale base change along
`f` admits a fully faithful left adjoint, the counit `f⁻¹f_*F ⟶ F` of the morphism of topoi is an
isomorphism, so `f⁻¹f_*` is the identity on small pro-étale sheaves of sets. -/
@[stacks 09AA "(3), the counit of the morphism of topoi is an isomorphism, given that pro-etale \
base change admits a fully faithful left adjoint"]
public theorem smallProetaleMorphism_isIso_counit_of_adjoint [v.Full] [v.Faithful] :
    IsIso (smallProetaleMorphism B T S f).adj.counit := by
  have hff := smallProetaleMorphismPushforwardFullyFaithfulOfAdjoint B T S f adjv
  have := hff.full
  have := hff.faithful
  exact (smallProetaleMorphism B T S f).adj.counit_isIso_of_R_fully_faithful

/-- **Stacks 09AA (1) given the left adjoint of Stacks 09BL (3).** If the inverse image `f⁻¹` on
small pro-étale sheaves of sets admits a left adjoint, it commutes with limits. -/
@[stacks 09AA "(1), the inverse image commutes with limits, given that it admits a left \
adjoint -- which is clause (3) of Tag 09BL"]
public theorem smallProetaleMorphism_inverseImage_preservesLimits
    [(smallProetaleMorphism B T S f).inverseImage.IsRightAdjoint] :
    PreservesLimits (smallProetaleMorphism B T S f).inverseImage :=
  inferInstance

end AlgebraicGeometry.ProEtale

end
