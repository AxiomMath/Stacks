module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
import StacksCore.Tactic.StacksAttribute

/-!
# The identity functor of a site is a morphism of sites

The identity functor of a site is continuous, and the functor it induces on sheaves of sets is
the identity, hence exact. So it is a morphism of sites in the sense of Stacks 00X1, presenting
the identity morphism of the associated topos.

## Main definitions

* `CategoryTheory.Functor.sheafPullbackIdIso`: the functor on sheaves with values in any
  category induced by the identity functor of a site is the identity functor.

## Main results

* `CategoryTheory.Functor.isMorphismOfSites_id`: the identity functor of a site is a morphism
  of sites.

## Implementation notes

The direct image along the identity functor is the identity functor of the category of sheaves,
by `CategoryTheory.Functor.sheafPushforwardContinuousId`. The induced functor on sheaves is its
left adjoint, so it is the identity by uniqueness of left adjoints; exactness then reduces to
exactness of the identity functor. Right exactness would hold for any continuous functor, the
induced functor being a left adjoint, so only left exactness is argued.

Nothing in the first identification is about sheaves of sets: the direct image along the
identity functor is the identity functor for sheaves with values in any category, so
`sheafPullbackIdIso` is stated for an arbitrary coefficient category admitting the induced
functor at all, i.e. one for which the direct image has a left adjoint. Sheaves of sets, where
the left adjoint is supplied by sheafification, is the case the morphism-of-sites condition
asks about; sheaves of commutative rings is the case a change of coefficient rings on a fixed
site asks about, the inverse image of the structure sheaf along such a morphism being the
structure sheaf itself.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ u

namespace CategoryTheory.Functor

variable {C : Type u} [SmallCategory C] (A : Type u₁) [Category.{v₁} A]
  (J : GrothendieckTopology C)

/-- **The functor on sheaves induced by the identity functor of a site is the identity
functor.** It is the left adjoint of the direct image along the identity functor, which is the
identity functor of the category of sheaves. -/
noncomputable def sheafPullbackIdIso
    [((𝟭 C).sheafPushforwardContinuous A J J).IsRightAdjoint] :
    (𝟭 C).sheafPullback A J J ≅ 𝟭 (Sheaf J A) :=
  Adjunction.leftAdjointUniq ((𝟭 C).sheafAdjunctionContinuous A J J) Adjunction.id

/-- The functor on sheaves of sets induced by the identity functor of a site is left exact. -/
theorem preservesFiniteLimits_sheafPullback_id :
    PreservesFiniteLimits ((𝟭 C).sheafPullback (Type u) J J) :=
  preservesFiniteLimits_of_natIso (sheafPullbackIdIso (Type u) J).symm

/-- **The identity functor of a site is a morphism of sites**, presenting the identity morphism
of the associated topos. -/
theorem isMorphismOfSites_id : (𝟭 C).IsMorphismOfSites J J :=
  (isMorphismOfSites_iff_preservesFiniteLimits (𝟭 C) J J).2
    (preservesFiniteLimits_sheafPullback_id J)

end CategoryTheory.Functor

end
