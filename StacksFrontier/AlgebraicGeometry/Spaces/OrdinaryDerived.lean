module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Full faithfulness of the small étale direct image, reduced to its counit

Stacks 0AEH asserts that for an integral universally injective morphism `f : Y ⟶ X` of
algebraic spaces the direct image along `f` on small étale sites is fully faithful, for
sheaves of sets and for abelian sheaves, and that the inverse image is a left inverse to it.

This file proves that the two assertions are *equivalent*: the direct image is fully faithful
exactly when the counit of the inverse-image/direct-image adjunction is an isomorphism. So the
four full-faithfulness assertions of Stacks 0AEH and its two left-inverse assertions are one
statement per coefficient category, and only the counit isomorphism carries geometric content.

## Main results

* `AlgebraicGeometry.Space.smallEtalePushforward_isRightAdjoint` and
  `AlgebraicGeometry.Space.smallEtalePushforwardAb_isRightAdjoint`: for sheaves of sets and for
  abelian sheaves the small étale direct image along a representable morphism is a right
  adjoint unconditionally.
* `AlgebraicGeometry.Space.smallEtalePushforward_counit_isIso_iff_fullyFaithful` and
  `AlgebraicGeometry.Space.smallEtalePushforwardAb_counit_isIso_iff_fullyFaithful`: the counit
  of the adjunction is an isomorphism if and only if the direct image is full and faithful.
* `AlgebraicGeometry.Space.smallEtalePushforward_full_of_counit_isIso`,
  `AlgebraicGeometry.Space.smallEtalePushforward_faithful_of_counit_isIso`,
  `AlgebraicGeometry.Space.smallEtalePushforwardAb_full_of_counit_isIso` and
  `AlgebraicGeometry.Space.smallEtalePushforwardAb_faithful_of_counit_isIso` are the four
  separate implications in the direction Stacks 0AEH uses.

## Implementation notes

Everything here is about an arbitrary *representable* morphism of algebraic spaces, because
representability is all that the direct image needs: it is what makes base change of étale
scheme charts available, through `AlgebraicGeometry.Space.smallBaseChange` and
`AlgebraicGeometry.Space.smallBaseChange_isMorphismOfSites`. Integrality and universal
injectivity are the hypotheses of Stacks 0AEH under which the counit *is* an isomorphism, and
they play no role in the reduction, so they are absent from these statements. Consequently
none of these declarations carries the tag `0AEH`: each is an implication between two of its
assertions, not one of them.

The hypothesis of representability is taken as an explicit argument. Deriving it from
integrality is the implication (2) ⇒ (1) of Stacks 03ZQ, which is available for a morphism of
algebraic spaces as
`AlgebraicGeometry.Space.isIntegralHom_iff_representable` of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae`; it is not used here, since none of
these statements assumes integrality.

For sheaves of sets the direct image is a right adjoint by synthesis, because sheafification of
`Type (max (u + 1) v)`-valued presheaves on the small étale site is available. For abelian
sheaves at the same universe synthesis fails, but the statement still holds, and it is proved
here rather than assumed. What fails is only
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`, which needs coefficients with `u`-small
morphisms and so does not apply to `AddCommGrpCat.{max (u + 1) v}`. What does apply is
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`, because the small étale site
of an algebraic space over a scheme in universe `u` has its objects in `Type (u + 1)` and its
morphisms in `Type u`, so that `max (u + 1) u ≤ max (u + 1) v`. It is a theorem and not an
instance, so it has to be supplied by hand; that is
`AlgebraicGeometry.Space.smallEtalePushforwardAb_isRightAdjoint`, and the abelian statements
below use it through `Classical.choice` rather than taking right-adjointness as a hypothesis.

The same argument is already carried out unconditionally for a closed immersion as
`AlgebraicGeometry.Space.smallEtalePushforward_isRightAdjoint_abelian` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardFullyFaithful`, a module downstream
of this one; the statement here needs only representability, so that one is the special case.

## References

* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hr : yoneda.relativelyRepresentable f.hom)

/-! ### Sheaves of sets -/

/-- The counit of an adjunction is objectwise an isomorphism iff the right adjoint is full and
faithful. -/
private theorem counit_app_isIso_iff_full_and_faithful {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    (∀ F, IsIso (adj.counit.app F)) ↔ R.Full ∧ R.Faithful := by
  refine ⟨fun h => ?_, fun h F => ?_⟩
  · have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
    exact ⟨(Adjunction.fullyFaithfulROfIsIsoCounit adj).full,
      (Adjunction.fullyFaithfulROfIsIsoCounit adj).faithful⟩
  · obtain ⟨_, _⟩ := h
    infer_instance

/-- The small étale direct image of sheaves of sets along a representable morphism of
algebraic spaces is a right adjoint, its left adjoint being the inverse image. -/
theorem smallEtalePushforward_isRightAdjoint :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    Nonempty (((smallBaseChange B S hS f hr).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).IsRightAdjoint) :=
  let _ := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
  ⟨inferInstance⟩

/-- The counit of the inverse-image/direct-image adjunction on sheaves of sets is an
isomorphism exactly when the direct image is full and faithful. The direction from left to
right is the one by which Stacks 0AEH derives full faithfulness from its left-inverse
assertion; the converse holds for any adjunction. -/
theorem smallEtalePushforward_counit_isIso_iff_fullyFaithful :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    (∀ F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (max (u + 1) v)),
        IsIso (((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
          (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).counit.app F)) ↔
      (((smallBaseChange B S hS f hr).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).Full ∧
        ((smallBaseChange B S hS f hr).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).Faithful) := by
  let _ := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
  exact counit_app_isIso_iff_full_and_faithful _

/-- **Stacks 0AEH, part (1), fullness, reduced to the left-inverse assertion.** -/
theorem smallEtalePushforward_full_of_counit_isIso
    (hc : letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
      ∀ F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (max (u + 1) v)),
        IsIso (((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
          (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).counit.app F)) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    ((smallBaseChange B S hS f hr).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).Full :=
  ((smallEtalePushforward_counit_isIso_iff_fullyFaithful.{v} B S hS f hr).mp hc).1

/-- **Stacks 0AEH, part (1), faithfulness, reduced to the left-inverse assertion.** -/
theorem smallEtalePushforward_faithful_of_counit_isIso
    (hc : letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
      ∀ F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (max (u + 1) v)),
        IsIso (((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
          (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).counit.app F)) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    ((smallBaseChange B S hS f hr).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).Faithful :=
  ((smallEtalePushforward_counit_isIso_iff_fullyFaithful.{v} B S hS f hr).mp hc).2

/-! ### Abelian sheaves -/

/-- The small étale direct image of abelian sheaves along a representable morphism of algebraic
spaces is a right adjoint, its left adjoint being the inverse image.

Unlike for sheaves of sets this is not available by synthesis, because
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify` needs coefficients with `u`-small
morphisms and `AddCommGrpCat.{max (u + 1) v}` does not have them. What does apply is
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`, because the small étale site
has its objects in `Type (u + 1)` and its morphisms in `Type u`; it is a theorem and not an
instance, so it is supplied by hand. -/
theorem smallEtalePushforwardAb_isRightAdjoint :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    Nonempty (((smallBaseChange B S hS f hr).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).IsRightAdjoint) := by
  let _ := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
  have : HasSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{max (u + 1) v} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) v, u, u + 1}
      (SmallEtale.topology B S hS Y.1)
  exact ⟨inferInstance⟩

/-- The counit of the inverse-image/direct-image adjunction on abelian sheaves is an
isomorphism exactly when the direct image is full and faithful. The adjunction is the one
whose existence is `AlgebraicGeometry.Space.smallEtalePushforwardAb_isRightAdjoint`, so no
right-adjointness hypothesis is needed. -/
theorem smallEtalePushforwardAb_counit_isIso_iff_fullyFaithful :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    letI := Classical.choice (smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f hr)
    (∀ F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{max (u + 1) v},
        IsIso (((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).counit.app F)) ↔
      (((smallBaseChange B S hS f hr).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).Full ∧
        ((smallBaseChange B S hS f hr).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).Faithful) := by
  let _ := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
  let _ := Classical.choice (smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f hr)
  exact counit_app_isIso_iff_full_and_faithful _

/-- **Stacks 0AEH, part (2), fullness, reduced to the left-inverse assertion.** -/
theorem smallEtalePushforwardAb_full_of_counit_isIso
    (hc : letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
      letI := Classical.choice (smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f hr)
      ∀ F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{max (u + 1) v},
        IsIso (((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).counit.app F)) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    ((smallBaseChange B S hS f hr).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).Full :=
  ((smallEtalePushforwardAb_counit_isIso_iff_fullyFaithful.{v} B S hS f hr).mp hc).1

/-- **Stacks 0AEH, part (2), faithfulness, reduced to the left-inverse assertion.** -/
theorem smallEtalePushforwardAb_faithful_of_counit_isIso
    (hc : letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
      letI := Classical.choice (smallEtalePushforwardAb_isRightAdjoint.{v} B S hS f hr)
      ∀ F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{max (u + 1) v},
        IsIso (((smallBaseChange B S hS f hr).sheafAdjunctionContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).counit.app F)) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    ((smallBaseChange B S hS f hr).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).Faithful :=
  ((smallEtalePushforwardAb_counit_isIso_iff_fullyFaithful.{v} B S hS f hr).mp hc).2

end AlgebraicGeometry.Space

end
