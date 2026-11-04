module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.UnramifiedConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Unramifiedness of a local complete intersection morphism of algebraic spaces

A local complete intersection morphism of algebraic spaces over a scheme `S` is unramified
exactly when it is formally unramified in the sense of [Stacks Project, Tag 049S]: the local
finite type half of the characterization of unramifiedness is automatic for a Koszul morphism.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocalCompleteIntersection`: a local
  complete intersection morphism of algebraic spaces is locally of finite type.
* `AlgebraicGeometry.Space.isUnramified_iff_formallyUnramified_of_isLocalCompleteIntersection`:
  a local complete intersection morphism of algebraic spaces is unramified if and only if it is
  formally unramified.

## References

* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
* [Stacks Project, Tag 06B9](https://stacks.math.columbia.edu/tag/06B9)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A local complete intersection morphism of algebraic spaces is locally of finite type. -/
public theorem isLocallyOfFiniteType_of_isLocalCompleteIntersection {f : X ⟶ Y}
    (hf : IsLocalCompleteIntersection B S hS f) :
    IsLocallyOfFiniteType B S hS f := fun U V a b h ha hb hsq =>
  locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism (hf U V a b h ha hb hsq)

/-- A local complete intersection morphism of algebraic spaces over `S` is unramified if and
only if it is formally unramified. -/
@[stacks 06CB "the equivalence: unramified iff formally unramified"]
public theorem isUnramified_iff_formallyUnramified_of_isLocalCompleteIntersection
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocalCompleteIntersection B S hS f) :
    IsUnramified B S hS f ↔ FormallyUnramified f :=
  (isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified B S hS hX hY f).trans
    (and_iff_right (isLocallyOfFiniteType_of_isLocalCompleteIntersection B S hS hf))

end AlgebraicGeometry.Space

end
