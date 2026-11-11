module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.TopologicalInvariance.SmallEtale

/-!
# Schemes under an integral bijection of algebraic spaces, unconditionally (Stacks 07VV)

An integral morphism `f : X ⟶ Y` of algebraic spaces over `S` which is a bijection
`|X| → |Y|` on points has a scheme source exactly when it has a scheme target (Stacks 07VV).
Being a scheme is `CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the space.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_iff_isRepresentable_of_isIntegralHom_of_bijective`:
  **Stacks 07VV.**

## Implementation notes

The base declarations `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective` and
`AlgebraicGeometry.Space.isRepresentable_iff_of_isIntegralHom_of_bijective` of
`StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection` take as binders the three inputs
`h09YA`, `h07SQ` and `hFinitePresentation` of the conditional form of Stacks 07VT. They cannot be
instantiated: the binder `h07SQ`, which asks Stacks 07SQ for index sets of every size, is
refuted in this size model by
`AlgebraicGeometry.Space.Refute07SQ.not_forall_exists_isAffineSpace_system_obj`.

The two implications are instead taken from base declarations with no hypotheses beyond the
source's. The implication from the source is
`AlgebraicGeometry.Space.isRepresentable_target_of_isIntegralHom_of_bijective` of
`StacksFrontier.AlgebraicGeometry.Spaces.TopologicalInvariance.SmallEtale`, the source's argument
with its affineness step supplied by Stacks 07VT as proved with no hypotheses,
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`.
The implication from the target is `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom`,
which needs no bijectivity.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 07VV.** Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Assume `f` is integral and induces a bijection `|X| → |Y|`. Then `X` is a scheme if
and only if `Y` is a scheme.

The implication from the source is
`AlgebraicGeometry.Space.isRepresentable_target_of_isIntegralHom_of_bijective`, through Stacks
07VT, and the implication from the target is
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom`, which needs no bijectivity. -/
@[stacks 07VV "for an integral morphism of algebraic spaces bijective on points, the source is a \
scheme if and only if the target is"]
theorem isRepresentable_iff_isRepresentable_of_isIntegralHom_of_bijective
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsIntegralHom B S hS f) (hbij : Function.Bijective (pointsMap B S hS F f)) :
    F.IsRepresentable ↔ G.IsRepresentable :=
  ⟨isRepresentable_target_of_isIntegralHom_of_bijective B S hS hF hG f hf hbij,
    isRepresentable_of_isIntegralHom B S hS hF f hf⟩

end AlgebraicGeometry.Space

end
