module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact

/-!
# Restriction to a simplicial component preserves injectives (Stacks 09WH)

Stacks 09WH says that an injective abelian sheaf on the total site of a simplicial site restricts
to an injective abelian sheaf on every component. Its proof is the standard Homology 015Z step:
restriction to the component is right adjoint to lower shriek, lower shriek is exact by
Stacks 09WG (7), and a right adjoint whose left adjoint preserves monomorphisms preserves
injectives.

The adjunction is
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, exactness of lower
shriek is `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor`, and the
015Z step is Mathlib's `CategoryTheory.Adjunction.map_injective`. Exactness holds for an
arbitrary simplicial-site situation, so the statement below does too.

## Main results

* `CategoryTheory.SimplicialSiteSituation.injective_componentRestriction`: **Stacks 09WH**, first
  assertion, for an arbitrary simplicial-site situation.
* `CategoryTheory.CocontinuousSimplicialSite.injective_componentRestriction`: its case-(B)
  instance.

## Implementation notes

The coefficients here are the abelian groups of the site's own universe. The source says
nothing about universes; at a coefficient universe other than the site's, the restriction functor
has no left adjoint — neither sheafification on the total topology nor the pointwise left Kan
extensions along the component inclusion exist there — so the Homology 015Z argument has no
input. The second assertion of the same tag, also at the site universe, is in
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentKInjective.lean`.

`CategoryTheory.Adjunction.map_injective` asks for its left adjoint to preserve monomorphisms,
and Mathlib derives that from preservation of limits of shape `WalkingCospan` only; the
`PreservesFiniteLimits` half of exactness is therefore instantiated at that shape explicitly.

## References

* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory.SimplicialSiteSituation

universe u

/-- **Stacks 09WH**, first assertion: the restriction of an injective abelian sheaf on the total
site of a simplicial-site situation to a component is injective.

Restriction to the component is right adjoint to lower shriek, which is exact by
`CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor` and so preserves
monomorphisms; Mathlib's `CategoryTheory.Adjunction.map_injective` is then the Homology 015Z
step. Exactness holds for an arbitrary situation, so no case distinction is made.

Coefficients sit at the site universe: at an independent coefficient universe the adjunction used
here is not available from the data of a situation, since neither `HasLeftKanExtension` nor
`HasWeakSheafify S.totalTopology Ab` holds there in general. -/
@[stacks 09WH "component_injective"]
lemma injective_componentRestriction (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (Inj : Sheaf S.totalTopology Ab.{u}) [Injective Inj] :
    Injective ((S.restrictAb n).obj Inj) := by
  have hlex := (componentLowerShriek_exactFunctor S n).1
  have : PreservesLimitsOfShape WalkingCospan
      (sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
        (S.componentTopology n) S.totalTopology) :=
    hlex.preservesFiniteLimits WalkingCospan
  exact (sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentFunctor S n) Ab.{u}
    (S.componentTopology n) S.totalTopology).map_injective Inj inferInstance


/-- Restriction of abelian sheaves to a simplicial component is left exact, being the right
adjoint of lower shriek. -/
noncomputable instance preservesFiniteLimits_componentRestrictionAb
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    PreservesFiniteLimits (S.restrictAb n) :=
  haveI : PreservesLimitsOfSize.{0, 0} (S.restrictAb n) :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentFunctor S n) Ab.{u}
      (S.componentTopology n) S.totalTopology).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Restriction of abelian sheaves to a simplicial component is right exact, being the left
adjoint of the direct image of the cocontinuous component inclusion. -/
noncomputable instance preservesFiniteColimits_componentRestrictionAb
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    PreservesFiniteColimits (S.restrictAb n) :=
  haveI : PreservesColimitsOfSize.{0, 0} ((componentFunctor S n).sheafPushforwardContinuous
      Ab.{u} (S.componentTopology n) S.totalTopology) :=
    ((componentFunctor S n).sheafAdjunctionCocontinuous Ab.{u}
      (S.componentTopology n) S.totalTopology).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restriction of abelian sheaves to a simplicial component is additive, being exact. -/
instance additive_componentRestrictionAb (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (S.restrictAb n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Stacks 09WH**, as a preservation property of the restriction functor: restriction of
abelian sheaves to a simplicial component preserves injective objects. -/
@[sga "4 VI 7.4.15" "special case"]
instance preservesInjectiveObjects_componentRestrictionAb (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (S.restrictAb n).PreservesInjectiveObjects where
  injective_obj {Inj} h := letI := h; injective_componentRestriction S n Inj

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation

universe u

variable (C : CocontinuousSimplicialSite.{u}) (n : SimplexCategory)

/-- **Stacks 09WH**, first assertion, in case (B): the case-(B) instance of
`CategoryTheory.SimplicialSiteSituation.injective_componentRestriction`. -/
lemma injective_componentRestriction
    (Inj : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
    [Injective Inj] :
    Injective (((componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
      n).sheafPushforwardContinuous Ab.{u}
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj Inj) :=
  SimplicialSiteSituation.injective_componentRestriction _ n Inj

end CategoryTheory.CocontinuousSimplicialSite

end
