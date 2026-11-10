module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Families of nodal curves of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *at-worst-nodal of relative dimension
one* when the scheme morphism it induces in every commuting square of étale charts is
at-worst-nodal of relative dimension one. This is the notion of a family of nodal curves
parametrized by an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.IsAtWorstNodalOfRelativeDimensionOne` is the predicate above:
  **Stacks 0DSE**.

## Main results

* `AlgebraicGeometry.Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange`:
  **Stacks 0DSF** — the predicate is preserved by base change.
* `AlgebraicGeometry.Space.isAtWorstNodalOfRelativeDimensionOne_tfae`: **Stacks 0DSG** — the
  eight equivalent criteria, testing the predicate after base change to every scheme or to
  every affine scheme, on one surjective étale chart of the target, on the composite with one
  surjective étale chart of the source, in every or in one surjective commuting square of
  étale charts, and over a pair of Zariski coverings.

## Implementation notes

The definition is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to the
scheme-morphism property `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne` of
Stacks 0C5A, so criteria (1) and (6) of Stacks 0DSG are the same condition read in two ways;
(6) is stated here in its spelled-out form over commuting squares of étale charts.

Both results are instances of statements holding for any property of scheme morphisms which
is étale local on the source and target, stable under base change and Zariski local on the
target: `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isStableUnderBaseChange` of
Stacks 0AMM and `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae_of_isLocalAtTarget`.
Being at-worst-nodal of relative dimension one has those three properties by Stacks 0C5B,
0C5D, 0CD8 and 0C5E. Note that it is neither stable under composition nor implied by
étaleness, so the nine criteria of Stacks 03MM are unavailable for it.

The definition does not impose algebraicity of the source or target; as with the
conditions of `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms`, that is imposed by
clients, exactly as in the source definition.

## References

* [Stacks Project, Tag 0DSE](https://stacks.math.columbia.edu/tag/0DSE)
* [Stacks Project, Tag 0DSF](https://stacks.math.columbia.edu/tag/0DSF)
* [Stacks Project, Tag 0DSG](https://stacks.math.columbia.edu/tag/0DSG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0DSE.** A morphism of algebraic spaces over `S` is *at-worst-nodal of
relative dimension one* when every commuting square of étale scheme charts induces a
scheme morphism which is at-worst-nodal of relative dimension one. -/
@[stacks 0DSE]
abbrev IsAtWorstNodalOfRelativeDimensionOne (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne.{u} :
      MorphismProperty Scheme.{u}) f

/-- **Stacks 0DSF.** Being at-worst-nodal of relative dimension one is preserved by base
change of morphisms of algebraic spaces over `S`. -/
@[stacks 0DSF]
theorem isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsAtWorstNodalOfRelativeDimensionOne B S hS f.hom) :=
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
    (@AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne.{u} :
      MorphismProperty Scheme.{u})
    AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site
/-- **Stacks 0DSG.** Eight criteria for a morphism of algebraic spaces over `S` to be
at-worst-nodal of relative dimension one: the condition may be tested after base change to
every scheme or to every affine scheme, on one surjective étale chart of the target, on the
composite with one surjective étale chart of the source, in every or in one surjective
commuting square of étale charts, or over a pair of Zariski coverings. -/
@[stacks 0DSG]
theorem isAtWorstNodalOfRelativeDimensionOne_tfae (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      IsAtWorstNodalOfRelativeDimensionOne B S hS f,
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAtWorstNodalOfRelativeDimensionOne B S hS (Limits.pullback.snd f g),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsAtWorstNodalOfRelativeDimensionOne B S hS (Limits.pullback.snd f g),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          IsAtWorstNodalOfRelativeDimensionOne B S hS (Limits.pullback.snd f g),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          IsAtWorstNodalOfRelativeDimensionOne B S hS (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne
            ((BigFppfOver.toScheme B S hS).map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧
          AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne
            ((BigFppfOver.toScheme B S hS).map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (Limits.pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsAtWorstNodalOfRelativeDimensionOne B S hS
            ((Xopen i j).ι ≫ Limits.pullback.snd f (Yopen i).ι)
    ] :=
  holdsOnEveryEtaleChart_tfae_of_isLocalAtTarget B S hS
    (@AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne.{u} :
      MorphismProperty Scheme.{u})
    AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
    hX hY f

end AlgebraicGeometry.Space

end
