module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.C.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity

/-!
# Čech vanishing for the direct image of an injective étale sheaf

Let `f : X ⟶ Y` be a morphism in a big étale site and let `I` be an injective abelian sheaf on
the small étale site of `X`. The positive-degree Čech cohomology of the direct image of `I`
vanishes for every family of étale morphisms with fixed target over `Y` — the family need not
be a covering.

## Main results

* `AlgebraicGeometry.pushforward_injective_cechCohomology_isZero` — positive-degree Čech
  cohomology of the direct image of an injective abelian étale sheaf vanishes.

## Implementation notes

Čech cohomology of a sheaf is the Čech cohomology of its underlying presheaf, and the
positive-degree Čech cohomology of an injective presheaf vanishes for every family for which
the Čech complex is defined. So the statement is the injectivity of the underlying presheaf of
the direct image, which `AlgebraicGeometry.injective_smallEtalePushforward_obj` supplies.

## References

* [Stacks Project, Tag 03QB](https://stacks.math.columbia.edu/tag/03QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 03QB.** The direct image of an injective abelian sheaf on the small étale site of
`X` has vanishing positive-degree Čech cohomology for every family of morphisms in the small
étale site of `Y`. -/
@[stacks 03QB "cech_vanishing"]
public theorem pushforward_injective_cechCohomology_isZero
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    [Injective I]
    (E : Covering.{u + 1, u, u + 1} (SmallEtale B Y.obj Y.property))
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E.2
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj I).obj p) :=
  have := injective_smallEtalePushforward_obj B f I
  Stacks.CechSite.injective_presheaf_cechCohomology_isZero.{u + 1, u, u + 1, 0} E.2 _ p hp

end AlgebraicGeometry
