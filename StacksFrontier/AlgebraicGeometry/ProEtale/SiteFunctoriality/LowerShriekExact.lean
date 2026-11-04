module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Exact lower shriek for the pro-étale inclusion

Let `f : T ⟶ S` be a morphism in a chosen big pro-étale site. Restriction from abelian sheaves
on the big pro-étale site over `S` to abelian sheaves on the small pro-étale site of `T` has an
exact left adjoint.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleLowerShriek_exact` — exactness of the
  abelian lower-shriek functor.

## Implementation notes

The lower shriek is the canonical sheafified left Kan extension along the site functor
`AlgebraicGeometry.ProEtale.smallProetaleToBigProetaleFunctor`, and its adjunction with
restriction is
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`; what is added
here is exactness. Left exactness needs the site functor to preserve fibre products and
equalizers, which instance search finds from its definition as a composite, and right
exactness is formal from the adjunction. The Kan-extension and sheafification hypotheses make
the construction available at the chosen coefficient universe.

## References

* [Stacks Project, Tag 098P](https://stacks.math.columbia.edu/tag/098P)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.ProEtale

/-- The left adjoint to restriction from the big pro-étale site over `S` to the
small pro-étale site of `T` is exact on abelian sheaves. -/
public theorem smallProetaleToBigProetaleLowerShriek_exact
    (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)
    [∀ F : (SmallProetale B T.obj T.property)ᵒᵖ ⥤ Ab.{w},
      (smallProetaleToBigProetaleFunctor B T S f).op.HasPointwiseLeftKanExtension F]
    [HasSheafify (BigProetaleOver.topology B S.obj S.property) Ab.{w}] :
    exactFunctor
      (Sheaf (SmallProetale.topology B T.obj T.property) Ab.{w})
      (Sheaf (BigProetaleOver.topology B S.obj S.property) Ab.{w})
      (Functor.sheafPullbackConstruction.sheafPullback
        (smallProetaleToBigProetaleFunctor B T S f) Ab.{w}
        (SmallProetale.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property)) := by
  rw [exactFunctor_iff]
  exact ⟨Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits _ _ _,
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits Ab.{w} _ _ _⟩

end AlgebraicGeometry.ProEtale

end
