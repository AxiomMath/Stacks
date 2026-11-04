module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Left exactness of restriction along a continuous functor of sites

Let `F : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`. Mathlib's
`Functor.sheafPushforwardContinuous` is the induced functor `Sheaf K A ⥤ Sheaf J A`, given on
underlying presheaves by precomposition with `F.op`. This file proves that this functor
commutes with limits, and in particular that it is left exact.

This is the left-exactness ingredient of the relocalization of a (ringed) topos along a
morphism of sheaves (Stacks 04J4). There the site of elements of a sheaf `G` maps to the site
of elements of a sheaf `F` by postcomposition with a morphism `G ⟶ F`, that functor is
continuous, and left exactness of the resulting restriction functor is exactly what makes the
pair (restriction, its cocontinuous partner) a morphism of topoi.

## Main results

* `CategoryTheory.Functor.preservesLimitsOfShape_sheafPushforwardContinuous`: restriction along
  a continuous functor of sites commutes with limits of any shape the value category admits.
* `CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`: restriction along a
  continuous functor of sites is left exact.

## Implementation notes

The proof is the pointwise one, and is deliberately routed through the forgetful functor to
presheaves rather than through any adjointness. Mathlib does supply
`(F.sheafPushforwardContinuous A J K).IsRightAdjoint`, from which limit preservation would
follow, but only under a package of hypotheses that make sheafification available: `A`
concrete with limits and filtered colimits, its forgetful functor preserving limits and
reflecting isomorphisms, and both sites *small* in a single universe (see
`Mathlib/CategoryTheory/Sites/Pullback.lean`). None of that is needed here. On underlying
presheaves `F.sheafPushforwardContinuous A J K` is precomposition with `F.op`, which commutes
with limits because limits of presheaves are computed pointwise
(`whiskeringLeft_preservesLimitsOfShape`); `sheafToPresheaf` creates limits, hence both
preserves and reflects them; and a functor whose composite with a limit-reflecting functor
preserves limits preserves them itself.

So the only hypotheses are `HasLimitsOfShape`/`HasFiniteLimits` on the value category, and the
universes of the two sites, of their morphisms and of the value category are all independent.
That independence is what a statement about localization at an arbitrary object of a topos
needs: the site of elements of a sheaf is not the base site, and nothing forces its universes
to agree with those of the value category.

Both results are stated as instances, since that is how the relocalization data consumes them,
and both are `noncomputable` because `CategoryTheory.Sheaf.createsLimitsOfShape` is.

## References

* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
  [F.IsContinuous J K] (A : Type w') [Category.{w} A]

/-- Restriction of sheaves along a continuous functor of sites commutes with limits of any
shape that the value category admits. -/
noncomputable instance preservesLimitsOfShape_sheafPushforwardContinuous
    (T : Type*) [Category T] [HasLimitsOfShape T A] :
    PreservesLimitsOfShape T (F.sheafPushforwardContinuous A J K) := by
  have : PreservesLimitsOfShape T
      (F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A) :=
    preservesLimitsOfShape_of_natIso
      (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (F.sheafPushforwardContinuous A J K) (sheafToPresheaf J A)

/-- **Stacks 04J4**, left exactness of relocalization: restriction of sheaves along a
continuous functor of sites is left exact. For the relocalization of a topos at a morphism of
sheaves `G ⟶ F` the continuous functor is postcomposition with that morphism on the sites of
elements, and this is the left exactness that makes the relocalization a morphism of topoi. -/
@[stacks 04J4 "left exactness of relocalization",
  sga "4 III 1.8" "partial",
  sga "4½ Arcata 2.3.3" "more general",
  sga "7 VI 3.1(a)" "partial"]
noncomputable instance preservesFiniteLimits_sheafPushforwardContinuous [HasFiniteLimits A] :
    PreservesFiniteLimits (F.sheafPushforwardContinuous A J K) :=
  ⟨fun T _ _ ↦ preservesLimitsOfShape_sheafPushforwardContinuous J K F A T⟩

end CategoryTheory.Functor

end
