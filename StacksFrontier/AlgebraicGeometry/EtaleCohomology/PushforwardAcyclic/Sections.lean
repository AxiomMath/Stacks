module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism

/-!
# Sections are acyclic on the direct image of an injective étale sheaf

Let `f : X ⟶ Y` be a morphism in a big étale site and let `I` be an injective abelian sheaf on
the small étale site of `X`. Taking sections over an object of the small étale site of `Y` is
acyclic on the direct image of `I`.

## Main results

* `AlgebraicGeometry.pushforward_injective_rightAcyclic_sections` — the direct image of an
  injective abelian étale sheaf is acyclic for sections over any object of the small étale
  site of the target, with the sheafification and enough-injectives inputs as instance binders.
* `AlgebraicGeometry.pushforward_injective_rightAcyclic_sections_of_smallEtale` — the same with
  both of those binders discharged.

## Implementation notes

Sections over an object are a left exact additive functor, and an injective object is acyclic
for such a functor. The direct image of an injective abelian étale sheaf is injective, which
is what `AlgebraicGeometry.injective_smallEtalePushforward` supplies, so no vanishing argument
on the sheaf itself is needed. Left exactness of sections is read off the identification of
the sections functor with evaluation of the underlying presheaf.

The homological-algebra inputs need not be assumed, and the second statement below assumes
neither. Abelian presheaves on the small étale site of a scheme in `Scheme.{u}` have a
sheafification with coefficients in `AddCommGrpCat.{u + 1}` by Mathlib's plus construction, the
site having its objects in `Type (u + 1)`, and the resulting abelian category of sheaves has
enough injectives because `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ` makes
it Grothendieck abelian at that coefficient universe.

## References

* [Stacks Project, Tag 03QB](https://stacks.math.columbia.edu/tag/03QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

-- Grothendieck abelianness of the sheaf category is what supplies its enough injectives; it is
-- stated rather than registered, so it is installed here and the global instance set is
-- unchanged.
attribute [local instance] _root_.AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ

-- Raising the priority of this instance is what lets the right derived functor of sections be
-- found while elaborating the statement below; at the default priority the search times out.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Stacks 03QB.** The direct image of an injective abelian étale sheaf is acyclic for
sections over any object of the small étale site of the target.

The homological-algebra inputs on the target site appear as the instance binders
`HasSheafify` and `EnoughInjectives`; they hold outright at the coefficient universe `u + 1`, and
the form of the statement with no such binder is
`AlgebraicGeometry.pushforward_injective_rightAcyclic_sections_of_smallEtale`. -/
public theorem pushforward_injective_rightAcyclic_sections
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}]
    [EnoughInjectives
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    [Injective I] (V : SmallEtale B Y.obj Y.property) :
    ((sheafSections (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{u + 1}).obj (Opposite.op V)).rightAcyclic
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj I) := by
  let J := SmallEtale.topology B Y.obj Y.property
  have : PreservesFiniteLimits
      ((sheafSections J AddCommGrpCat.{u + 1}).obj (Opposite.op V)) :=
    preservesFiniteLimits_of_natIso
      (sheafSectionsNatIsoEvaluation (J := J) (A := AddCommGrpCat.{u + 1}) (X := V)).symm
  have := injective_smallEtalePushforward B f I
  exact Stacks.BoundedBelowEdge.rightAcyclic_of_injective _ _

/-- **Stacks 03QB, with no homological-algebra side condition.** The direct image of an injective
abelian étale sheaf is acyclic for sections over any object of the small étale site of the
target.

This is `AlgebraicGeometry.pushforward_injective_rightAcyclic_sections` with both of its instance
binders discharged: abelian presheaves on the small étale site of a scheme in `Scheme.{u}` have a
sheafification with coefficients in `AddCommGrpCat.{u + 1}` by Mathlib's plus construction, the
site having its objects in `Type (u + 1)`, and the resulting abelian category of sheaves has
enough injectives because `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ` makes it
Grothendieck abelian at that coefficient universe. -/
@[stacks 03QB "sections_acyclic"]
public theorem pushforward_injective_rightAcyclic_sections_of_smallEtale
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    [Injective I] (V : SmallEtale B Y.obj Y.property) :
    ((sheafSections (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{u + 1}).obj (Opposite.op V)).rightAcyclic
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj I) :=
  pushforward_injective_rightAcyclic_sections B f I V

end AlgebraicGeometry
