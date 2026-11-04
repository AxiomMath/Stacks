module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Universally bounded fibres of a morphism to an algebraic space

A morphism from a scheme to a presheaf on the big fppf site of `S` has *universally bounded
fibres* when one integer bounds the degrees of all of its field-valued fibres. The condition
is stable under base change along a relatively representable morphism of presheaves, and in
that situation the base-changed morphism is again represented by a scheme over `S`.

## Main definitions

* `AlgebraicGeometry.Space.HasUniversallyBoundedFibers` expresses a common degree bound on
  the finite scheme obtained by pulling back along each field-valued point.

## Main results

* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_baseChange`: a relatively
  representable base change of a morphism with universally bounded fibres is represented by
  a scheme over `S` whose fibres are again universally bounded. This applies in particular
  to morphisms of algebraic spaces.

## Implementation notes

Field-valued points are objects of the chosen big fppf site whose underlying schemes are
isomorphic to field spectra. A fibre is specified by a cartesian square of presheaves with
representable upper left corner. This square retains its map to the field spectrum, whose
finite locally free rank is the degree of the fibre. Stating the bound as an abbreviation
lets later composition and base-change statements use the existential bound directly.

The base-changed scheme is likewise specified by a cartesian square of presheaves. This
includes its two projections and avoids choosing a particular representative of the
pullback.

## References

* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JN](https://stacks.math.columbia.edu/tag/03JN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A scheme morphism to a presheaf has universally bounded fibres if every field-valued
base change is represented by a finite scheme and all their degrees have one integer bound. -/
@[stacks 03JL]
abbrev HasUniversallyBoundedFibers (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ X) : Prop :=
  ∃ n : ℤ, ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
    ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ∃ (V : BigFppfOver B S hS) (p : V ⟶ T) (i : yoneda.obj V ⟶ yoneda.obj U) (r : ℕ),
          (r : ℤ) ≤ n ∧
            Stacks.Morphisms.IsFiniteLocallyFreeOfRank
              ((BigFppfOver.toScheme B S hS).map p) r ∧
            IsPullback i (yoneda.map p) f ξ

/-- A representable base change of a scheme morphism with universally bounded fibres
is represented by a scheme whose fibres remain universally bounded. -/
@[stacks 03JN]
theorem hasUniversallyBoundedFibers_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Y ⟶ X) (hg : yoneda.relativelyRepresentable g)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X)
    (hf : HasUniversallyBoundedFibers B S hS U f) :
    ∃ (V : BigFppfOver B S hS)
      (i : yoneda.obj V ⟶ yoneda.obj U) (p : yoneda.obj V ⟶ Y),
      IsPullback i p f g ∧ HasUniversallyBoundedFibers B S hS V p := by
  obtain ⟨V, i, p, hp⟩ := hg f
  rcases hf with ⟨n, hf⟩
  refine ⟨V, yoneda.map i, p, hp.flip, n, ?_⟩
  intro k hk T hT ξ
  obtain ⟨W, q, j, r, hbound, ⟨hrank, hq⟩⟩ := hf k T hT (ξ ≫ g)
  refine ⟨W, q, hp.flip.lift j (yoneda.map q ≫ ξ) (by
    simpa [Category.assoc] using hq.w), r, hbound, hrank, ?_⟩
  simpa using hq.of_right' hp.flip

end AlgebraicGeometry.Space

end
