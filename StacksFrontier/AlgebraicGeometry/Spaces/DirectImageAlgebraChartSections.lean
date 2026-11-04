module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence

/-!
# The sections of a direct-image algebra over an étale chart

Let `X` be an algebraic space and `Y ⟶ X` a morphism with representable structure morphism.
The direct-image algebra `Y.hom_* 𝒪_Y` of
`AlgebraicGeometry.Space.pushforwardAlgebra` is a sheaf of commutative rings on the small
étale site of `X`, and Stacks 03G8 identifies its direct image with base change of étale
scheme charts: `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`.  Reading
that identification at one chart `V` of `X` gives the ring of sections of `Y.hom_* 𝒪_Y` over
`V` as the regular functions on the base-changed chart `Y ×_X V`, and this file names that
isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`: the ring isomorphism
  `(Y.hom_* 𝒪_Y)(V) ≅ Γ(Y ×_X V, 𝒪)`.

## Implementation notes

The isomorphism is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing` at the
structure sheaf of `Y`, evaluated at `V` through `CategoryTheory.sheafToPresheaf` and
`CategoryTheory.evaluation`.  Its target is stated as `Γ(Y ×_X V, 𝒪)` rather than as the
sections of the structure sheaf of `Y` over the base-changed chart: the two are equal by
`rfl`, because `AlgebraicGeometry.Space.structurePresheaf` is `CategoryTheory.Functor.comp`
with `AlgebraicGeometry.Scheme.Γ` and
`CategoryTheory.Functor.sheafPushforwardContinuous` is restriction along the base-change
functor, so no transport is involved.

Only the underlying bijection of types of this isomorphism was used before it was named; the
one consumer, `AlgebraicGeometry.Space.mk_sections_pushforwardAlgebra_lt_cutoff` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceObstruction`, built it
inline.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sections of a direct-image algebra over an étale chart are the regular functions on
the base-changed chart.**  For `Y` an algebraic space over `X` with representable structure
morphism and `V` an étale scheme chart of `X`, the ring of sections of `Y.hom_* 𝒪_Y` over `V`
is the ring of global regular functions on the scheme `Y ×_X V`.

This is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`, Stacks 03G8, read
at the structure sheaf of `Y` and at the single chart `V`. -/
noncomputable def pushforwardAlgebraSectionsIso {X : AlgebraicSpaces B S hS} (Y : Over X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom) (V : SmallEtale B S hS X.1) :
    (pushforwardAlgebra B S hS Y).right.obj.obj (op V) ≅
      Γ(chartScheme ((smallBaseChange B S hS Y.hom hY).obj V), ⊤) :=
  let := (smallBaseChange_isMorphismOfSites B S hS Y.hom hY).toIsContinuous
  (sheafToPresheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} ⋙
      (evaluation (SmallEtale B S hS X.1)ᵒᵖ CommRingCat.{u}).obj (op V)).mapIso
    ((smallEtaleRingedToposHom_representableRing B S hS Y.hom hY).app
      (smallEtaleRingedTopos B S hS Y.left).O)

end AlgebraicGeometry.Space

end
