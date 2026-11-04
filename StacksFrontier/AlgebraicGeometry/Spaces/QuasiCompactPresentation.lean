module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Finite scheme covers of finite presentation: the reduction to an étale refinement

A quasi-compact and quasi-separated algebraic space over a scheme `S` is expected to have
a surjective, finite morphism of finite presentation from a scheme, and the covering scheme
is expected to be choosable so that it factors Zariski locally through any prescribed
surjective étale cover of the space. The second assertion contains the first: a space is a
surjective étale cover of itself, so taking the prescribed cover to be the identity of the
space turns the refined assertion into the plain one, the local factorizations being
discarded.

That reduction is what is proved here. The refined assertion itself is taken as an explicit
named hypothesis, so nothing in this file is tagged.

## Main results

* `AlgebraicGeometry.Space.exists_finite_surjective_scheme_cover_of_etale_refinement`
  derives the existence of a surjective finite scheme cover of finite presentation of every
  quasi-compact quasi-separated algebraic space from the refined form of that statement, by
  refining along the identity.

## Implementation notes

The identity of a presheaf on the big fppf site of `S` is surjective because the induced
map on points is the identity, and it is étale because composing a chart with it returns
that chart. Both facts are `AlgebraicGeometry.Space.isSurjective_id` and
`AlgebraicGeometry.Space.isEtale_id` of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeNormalization.lean`, which state them for an
arbitrary presheaf and so apply to the space being covered here; that module is imported
for them alone.

## References

* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 09YC, part (1) from part (2).** Suppose that every quasi-compact
quasi-separated algebraic space over `S` has a surjective, finite morphism of finite
presentation from a scheme which factors Zariski locally through any prescribed surjective
étale cover of the space. Then every quasi-compact quasi-separated algebraic space over `S`
has a surjective, finite morphism of finite presentation from a scheme.

Refine along the identity of the space, which is a surjective étale cover of it, and forget
the local factorizations. -/
theorem exists_finite_surjective_scheme_cover_of_etale_refinement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (H : ∀ X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS U →
      IsQuasiCompactSpace B S hS X → IsAbsolutelyQuasiSeparated B S hS hZ X →
      ∀ p : U ⟶ X, IsSurjective B S hS p → IsEtale B S hS p →
      ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
        IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f ∧
        ∀ y : points B S hS (yoneda.obj Y),
          ∃ W : Subfunctor (yoneda.obj Y),
            IsOpenSubspace B S hS W ∧
            W.toFunctor.IsRepresentable ∧
            y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
            ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
      IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f := by
  obtain ⟨Y, f, hsurj, hfin, hfp, -⟩ := H X X hX hX hqc hqs (𝟙 X)
    (isSurjective_id B S hS X) (isEtale_id B S hS X)
  exact ⟨Y, f, hsurj, hfin, hfp⟩

end AlgebraicGeometry.Space

end
