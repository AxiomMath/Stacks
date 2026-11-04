module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Sections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections

/-!
# A further direct image is acyclic on the direct image of an injective étale sheaf

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms in a big étale site and let `I` be an injective
abelian sheaf on the small étale site of `X`. The direct image `f_* I` is acyclic for `g_*`.

## Main results

* `AlgebraicGeometry.pushforward_injective_rightAcyclic_pushforward` — the direct image of an
  injective abelian étale sheaf is acyclic for a further direct image, with the sheafification
  and enough-injectives inputs as instance binders.
* `AlgebraicGeometry.pushforward_injective_rightAcyclic_pushforward_of_smallEtale` — the same
  with all of those binders discharged.

## Implementation notes

This is the third clause of Stacks 03QB, and the source deduces it from the second one
(`AlgebraicGeometry.pushforward_injective_rightAcyclic_sections`) together with the
description of `R^p g_*` as the sheafification of `V ↦ H^p(Y ×_Z V, -)` from Stacks 03Q8.

Acyclicity for `g_*` is the vanishing of `R^p g_* (f_* I)` for `p > 0`, by
`Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived`. Stacks 03Q8's objectwise comparison
`Stacks.HigherDirectImage.higherDirectImageSheafificationIso` rewrites that as the vanishing
of the sheafification of the cohomology presheaf `V ↦ H^p(Y ×_Z V, f_* I)`, and sheafification
kills a presheaf that is already zero, so it suffices that the cohomology presheaf vanishes.
Its value at `V` is `R^p Γ(Y ×_Z V, -)` evaluated at `f_* I`, by
`Stacks.HigherDirectImage.preimageCohomologyPresheafEvaluationIso`, and that vanishes because
sections over the object `Y ×_Z V` of the small étale site of `Y` are acyclic on `f_* I` —
which is the second clause. The étale object `V` of the source statement therefore enters only
through the sheafification, so the conclusion is about the whole sheaf `R^p g_* (f_* I)` and
does not mention `V`.

As in `AlgebraicGeometry.pushforward_injective_rightAcyclic_sections_of_smallEtale`,
sheafification and enough injectives on the small étale sites need not be assumed: the first
comes from Mathlib's plus construction at the coefficient universe `u + 1`, the second from
`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ`.

## References

* [Stacks Project, Tag 03QB](https://stacks.math.columbia.edu/tag/03QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

-- As in `AlgebraicGeometry.pushforward_injective_rightAcyclic_sections`, Grothendieck
-- abelianness of the sheaf category is what supplies its enough injectives, and it is stated
-- rather than registered, so it is installed here and the global instance set is unchanged.
attribute [local instance] _root_.AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ

-- As in `AlgebraicGeometry.pushforward_injective_rightAcyclic_sections`, raising the priority
-- of this instance is what lets the right derived functors below be found; at the default
-- priority the search times out.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Stacks 03QB.** The direct image of an injective abelian étale sheaf is acyclic for a
further direct image.

The homological-algebra inputs on the two target sites appear as the instance binders
`HasSheafify` and `EnoughInjectives`; they hold outright at the coefficient universe `u + 1`, and
the form of the statement with no such binder is
`AlgebraicGeometry.pushforward_injective_rightAcyclic_pushforward_of_smallEtale`. -/
public theorem pushforward_injective_rightAcyclic_pushforward
    (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}]
    [HasSheafify (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1}]
    [EnoughInjectives
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    [Injective I] :
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)).rightAcyclic
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj I) := by
  set F := ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)).obj I with hF
  refine (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived
    (Stacks.HigherDirectImage.pushforward.{u, u + 1} B g) F).2 fun p hp => ?_
  have hpresheaf : IsZero (Stacks.HigherDirectImage.preimageCohomologyPresheaf B g F p) := by
    refine Functor.isZero _ fun V => ?_
    have hsections : (Stacks.HigherDirectImage.sectionsOnPreimage.{u, u + 1} B g
        V.unop).rightAcyclic F :=
      hF ▸ pushforward_injective_rightAcyclic_sections B f I
        ((smallEtaleBaseChange B g).obj V.unop)
    exact ((Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived
        (Stacks.HigherDirectImage.sectionsOnPreimage B g V.unop) F).1 hsections p hp).of_iso
      (Stacks.HigherDirectImage.preimageCohomologyPresheafEvaluationIso B g F V.unop p)
  exact (Functor.map_isZero (presheafToSheaf (Stacks.HigherDirectImage.JY B (Y := Z))
      AddCommGrpCat.{u + 1}) hpresheaf).of_iso
    (Stacks.HigherDirectImage.higherDirectImageSheafificationIso B g F p)

/-- **Stacks 03QB, with no homological-algebra side condition.** The direct image of an injective
abelian étale sheaf is acyclic for a further direct image.

This is `AlgebraicGeometry.pushforward_injective_rightAcyclic_pushforward` with all three of its
instance binders discharged, exactly as in
`AlgebraicGeometry.pushforward_injective_rightAcyclic_sections_of_smallEtale`: sheafification
comes from Mathlib's plus construction at the coefficient universe `u + 1` and the enough
injectives from `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ`. -/
@[stacks 03QB "pushforward_acyclic"]
public theorem pushforward_injective_rightAcyclic_pushforward_of_smallEtale
    (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    [Injective I] :
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)).rightAcyclic
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj I) :=
  pushforward_injective_rightAcyclic_pushforward B f g I

end AlgebraicGeometry
