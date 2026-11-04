module

public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Precoverage
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExistence
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfSites

/-!
# Morphisms of big Zariski topoi

A morphism `f : T ⟶ S` in a big Zariski site induces a functor from the big Zariski category
over `T` to the one over `S`, by composing structure morphisms with `f`. That functor is
cocontinuous, and it has a continuous right adjoint given by base change along `f`. The two
functors determine the *same* morphism from the big Zariski topos of `T` to that of `S`, so
that morphism can be described from either side:

* inverse image is restriction along composition, `f⁻¹(G)(U / T) ≅ G(U / S)`;
* direct image is restriction along base change, `f_*(F)(U / S) ≅ F(U ×_S T / T)`.

Since composition with `f` preserves fibre products and equalizers, the inverse image also has
a left adjoint `f_!`, itself left exact.

The morphism of topoi itself, `AlgebraicGeometry.bigZariskiMorphism`, the continuity properties
it rests on and the lower shriek `AlgebraicGeometry.bigZariskiLowerShriekAdjunction` are taken
from `StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism`.

## Main results

* `AlgebraicGeometry.bigZariskiMorphismInverseImageIso` and
  `AlgebraicGeometry.bigZariskiMorphismPushforwardIso` — the two formulas on sections, which
  together say that the two descriptions agree.

## Implementation notes

The big Zariski category over a scheme is a slice category, so composition, base change and
their adjunction are Mathlib's `Over.map`, `Over.pullback` and `Over.mapPullbackAdj`, and are
referenced rather than redefined.

The formulas on sections are recorded as natural isomorphisms with restriction functors rather
than as equalities of section sets, which keeps their naturality in both the sheaf and the
object. Following the treatment of morphisms of topoi elsewhere in the library, equality of the
two induced geometric morphisms is represented by the canonical isomorphism of their
direct-image functors.

Fibre products in the underlying category of the big Zariski site come from
`StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Limits`, imported transitively; the
`Over.pullback` of the statements below is formed with that instance, so that this file and the
rest of the Zariski development speak about the same base-change functor.

## References

* [Stacks Project, Lemma 34.3.7 (Tag 0210)](https://stacks.math.columbia.edu/tag/0210)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

include f

/-- Inverse image is restriction along composition with `f`: on an object `U / T` this is the
formula `f_big⁻¹(G)(U / T) ≅ G(U / S)`. -/
public noncomputable def bigZariskiMorphismInverseImageIso :
    (bigZariskiMorphism B T S f).inverseImage ≅
      (Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (BigZariskiOver.topology B T.obj T.property)
        (BigZariskiOver.topology B S.obj S.property) :=
  (Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (BigZariskiOver.topology B T.obj T.property)
    (BigZariskiOver.topology B S.obj S.property)

/-- Direct image is restriction along base change: on an object `U / S` this is the formula
`f_{big,*}(F)(U / S) ≅ F(U ×_S T / T)`. -/
public noncomputable def bigZariskiMorphismPushforwardIso :
    (bigZariskiMorphism B T S f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigZariskiOver.topology B S.obj S.property)
        (BigZariskiOver.topology B T.obj T.property) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))

end AlgebraicGeometry
