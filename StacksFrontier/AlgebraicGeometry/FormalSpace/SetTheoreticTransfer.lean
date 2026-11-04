module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas

/-!
# The set-theoretic condition descends along a representable morphism

Let `S` be a scheme contained in a big fppf site `B` and let `g : X ⟶ Y` be a morphism of fppf
sheaves over `S` which is representable by algebraic spaces. If `Y` satisfies the set-theoretic
condition of **Stacks 0AIS** then so does `X`.

This is what makes the condition usable. It is *not* automatic — it is false for a morphism
which is not representable: the colimit of `Spec R[x_t : t ∈ T]/(x_s x_t)` over the sets `T` of
cardinality below the size cutoff of the site is a directed system of thickenings of affine
schemes of the site whose colimit admits no surjection from an object of the site at all, and
it maps to `Spec R`, which does. That map is not representable by algebraic spaces, and
representability is exactly what the argument below consumes.

## The argument

The condition on `Y` gives an object `U` of the site with a surjection `t : U ⟶ Y` of sheaves
and an object `R` of the site with a surjection `r : R ⟶ U ×_Y U`.

*The surjection onto `X`.* Put `P = U ×_Y X`. Its projection to `U` is a base change of `g`,
hence representable by algebraic spaces, and `U` is an algebraic space over `S`, so `P` is an
algebraic space over `S` by **Stacks 03XY**. Its étale scheme atlas (Definition **025Y**) is an
object `R₁` of the site surjecting onto `P`, and the projection `P ⟶ X` is a base change of `t`,
hence a surjection. The composite `a : R₁ ⟶ X` is the required surjection.

*The surjection onto the kernel pair.* Write `K = R₁ ×_X R₁`, `A = P ×_X P` and
`D = R₁ ×_X P`. The maps `K ⟶ D ⟶ A` are two base changes of the atlas `R₁ ⟶ P`, which is
representable by algebraic spaces because `P` is an algebraic space; and `A ⟶ U ×_Y U` is a base
change of `g`, because `A = (U ×_Y U) ×_Y X`
(`AlgebraicGeometry.FormalSpace.isPullback_chartRelation`). So `K ⟶ U ×_Y U` is representable by
algebraic spaces, and the fibre product `W = R ×_{U ×_Y U} K` is an algebraic space over `S`
lying over the algebraic space `R` and surjecting onto `K`, since `r` does onto `U ×_Y U`. The
étale scheme atlas of `W` is the required object of the site.

Only the *second* half of the condition on `Y` is doing work that the representability of the
diagonal of `Y` would otherwise do. That is the point of the second half: it is the weak
substitute for **Stacks 0AIP**, which this library has for an affine formal algebraic space
only.

## Main results

All in the namespace `AlgebraicGeometry.FormalSpace.SetTheoreticDescent`:

* `isRepresentableByAlgebraicSpacesULift_point_of_isAlgebraicSpace`: a scheme-valued point of an
  algebraic space over `S` is representable by algebraic spaces.
* `isAlgebraicSpaceULift_pullback_of_representable`: **Stacks 03XY** for fppf sheaves over `S`.
* `exists_representable_epi_of_representable_over`: the first half of the condition for the source
  of a morphism representable by algebraic spaces.
* `satisfiesSetTheoreticCondition_of_representable_over`: the transfer itself.

## Implementation notes

The statement is not registered on Stacks 0AIS. Its hypothesis is the condition for another
sheaf, and the tag's own observations are registered elsewhere
(`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`,
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`); what this
module is for is the removal of hypotheses from the consumers, which is where the tags are.

Representability of a scheme-valued point of an algebraic space is the representability of the
diagonal of that algebraic space, read through
`CategoryTheory.Functor.relativelyRepresentable.of_diag`, and is therefore representability by
*objects of the site*; it is weakened to representability by algebraic spaces at once, that
being the form in which base change and composition are available here.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.FormalSpace

end
