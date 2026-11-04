module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Limits.CoproductConnectedLimits
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafSumFormula

/-!
# Lower shriek from a simplicial component commutes with finite connected limits

Stacks 09WG (4) says that `g^{Sh}_{n!}`, the left adjoint of inverse image along the inclusion of
one component of a simplicial site into the total site, commutes with finite connected limits.
The source proves it in one sentence — *"the exactness properties of `g^{Sh}_{n!}` and `g_{n!}`
follow from the formulas given for these functors"* — and this file carries that sentence out for
sheaves of sets, in three steps.

* Every object of the total category lies in one of the components, so a functor into sheaves on
  the total site preserves limits of a given shape as soon as its composite with restriction to
  each degree does
  (`CategoryTheory.SimplicialSiteSituation.preservesLimitsOfShape_of_componentRestriction`).
* Restricted to degree `m`, lower shriek is the coproduct over the simplex maps `φ : [n] ⟶ [m]`
  of the transition inverse images — clause (3) of the tag, already proved as
  `CategoryTheory.SimplicialSiteSituation.componentLowerShriekRestrictionIsoCoproductType`.
* A coproduct of functors each of which commutes with finite connected limits commutes with
  finite connected limits (`CategoryTheory.Limits.preservesLimitsOfShape_sigma`, resting on the
  fact that a coproduct of sheaves of sets is a colimit over a discrete, hence almost-directed,
  index category), and each transition inverse image is the inverse image of a morphism of topoi,
  so it is left exact.

## Main results

* `CategoryTheory.SimplicialSiteSituation.preservesLimitsOfShape_transitionInverseImageType`:
  the transition inverse images of sheaves of sets are left exact.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_preservesLimitsOfShape`:
  **Stacks 09WG (4)**.

## Implementation notes

The route through the coproduct formula is the source's own, and it is the one available here.
The general criterion of Stacks 00XS —
`CategoryTheory.Functor.preservesLimitsOfShape_sheafPullback`, used for the topological analogue
Stacks 09W0 — asks that the source site have fibre products and equalizers which the functor
preserves; Situation 09WE assumes neither of the component sites, so that criterion would need
four hypotheses the source does not make, and the clause it proved would not be the tag's.

Connectedness of the limit shape is where the argument is sharp: lower shriek does not preserve
the final sheaf, the coproduct of the final sheaves over the `[n] ⟶ [m]` not being final.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 002Y](https://stacks.math.columbia.edu/tag/002Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- The transition inverse images of sheaves of sets are left exact: each is, up to the
comparison `transitionInverseImageTypeIso`, the inverse image of the morphism of topoi attached
to the transition. -/
lemma preservesLimitsOfShape_transitionInverseImageType (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (L : Type) [SmallCategory L] [FinCategory L] :
    PreservesLimitsOfShape L (transitionInverseImageType S φ) :=
  have : PreservesLimitsOfShape L (S.transitionMorphism φ).inverseImage :=
    (S.transitionMorphism φ).preservesFiniteLimits.preservesFiniteLimits L
  preservesLimitsOfShape_of_natIso (transitionInverseImageTypeIso S φ)

/-- **Stacks 09WG (4).** Lower shriek from one component of a simplicial site to the total site
commutes with finite connected limits. -/
@[stacks 09WG "sheaf_connected_limits"]
theorem componentLowerShriek_preservesLimitsOfShape (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) (L : Type) [SmallCategory L] [FinCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (componentLowerShriek.{u, u} S n) := by
  refine preservesLimitsOfShape_of_componentRestriction S L _ fun m => ?_
  have : ∀ φ : n ⟶ m, PreservesLimitsOfShape L (transitionInverseImageType S φ) :=
    fun φ => preservesLimitsOfShape_transitionInverseImageType S φ L
  have : PreservesLimitsOfShape L
      (colim : (Discrete (n ⟶ m) ⥤ Sheaf (S.componentTopology m) (Type u)) ⥤
        Sheaf (S.componentTopology m) (Type u)) :=
    preservesLimitsOfShape_colim_discrete_sheaf.{u, u, u, 0, 0}
      (S.componentTopology m) (n ⟶ m) L
  have : PreservesLimitsOfShape L (∐ fun φ : n ⟶ m => transitionInverseImageType S φ) :=
    preservesLimitsOfShape_sigma _ L
  exact preservesLimitsOfShape_of_natIso
    (componentLowerShriekRestrictionIsoCoproductType S n m).symm

end CategoryTheory.SimplicialSiteSituation

end
