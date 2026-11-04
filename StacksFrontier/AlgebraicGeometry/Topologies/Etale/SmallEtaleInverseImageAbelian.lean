module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Exactness of the inverse image on abelian sheaves of the small étale site

Let `f : X ⟶ Y` be a morphism of schemes. The inverse image `f⁻¹` on sheaves of abelian
groups for the small étale sites is the left adjoint of the direct image, and it is exact.

Right exactness is free: a left adjoint preserves all colimits. Left exactness is the
content, and it is the general statement about lower shriek on abelian sheaves: `f⁻¹` is the
sheafification of the left Kan extension along the opposite of base change, sheafification is
exact, and the Kan extension is a pseudofiltered colimit because the small étale site of `Y`
has fibre products and equalizers which base change preserves.

## Main results

* `Stacks.EtaleCohomology.smallEtaleAbSheafPullback_preservesFiniteLimits` and
  `Stacks.EtaleCohomology.smallEtaleAbSheafPullback_preservesFiniteColimits` — the two halves.
* `Stacks.EtaleCohomology.smallEtaleAbSheafPullback_exact` — the inverse image on abelian
  étale sheaves is exact.

## Implementation notes

The inverse image is Mathlib's `CategoryTheory.Functor.sheafPullback`, the chosen left adjoint
of the direct image, rather than any one construction of it; left exactness is proved for the
left-Kan-extension-and-sheafification model and transported along
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`, which identifies the two.

Coefficients are `Ab.{u + 1}` for a scheme universe `u`. That cutoff is what makes the
coefficient category receive the colimits computing the left Kan extension along base change:
the small étale site of a scheme in `Scheme.{u}` has its objects in `Type (u + 1)` and its
morphisms in `Type u`, so the comma categories indexing those colimits are `(u + 1)`-sized.
It also matches the coefficients of the sheaves-of-sets statement for the same source result.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The inverse image on abelian sheaves of the small étale sites preserves finite limits. It
is the sheafification of the left Kan extension along the opposite of base change, and base
change preserves the fibre products and equalizers of the small étale site, so the general
left-exactness statement for lower shriek on abelian sheaves applies. -/
public instance smallEtaleAbSheafPullback_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits
      ((smallEtaleBaseChange f).sheafPullback Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X)) :=
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange f) Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X)) :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u, u, u + 1, u + 1}
      (smallEtaleBaseChange f) (smallEtaleTopology Y) (smallEtaleTopology X)
  preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange f) Ab.{u + 1}
      (smallEtaleTopology Y) (smallEtaleTopology X)).symm

/-- The inverse image on abelian sheaves of the small étale sites preserves finite colimits,
being a left adjoint. -/
public instance smallEtaleAbSheafPullback_preservesFiniteColimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    PreservesFiniteColimits
      ((smallEtaleBaseChange f).sheafPullback Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X)) :=
  have := ((smallEtaleBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (smallEtaleTopology Y) (smallEtaleTopology X)).isLeftAdjoint
  inferInstance

/-- **Stacks 03Q1.** For a morphism of schemes `f : X ⟶ Y`, the inverse image functor
`f⁻¹ : Ab(Y_étale) ⥤ Ab(X_étale)` between the categories of abelian sheaves on the small
étale sites is exact: it preserves finite limits and finite colimits. -/
@[stacks 03Q1 "exact_abelian"]
public theorem smallEtaleAbSheafPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    exactFunctor
      (Sheaf (smallEtaleTopology Y) Ab.{u + 1})
      (Sheaf (smallEtaleTopology X) Ab.{u + 1})
      ((smallEtaleBaseChange f).sheafPullback Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X)) :=
  (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

end Stacks.EtaleCohomology

end
