module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine

/-!
# Countably indexed affine formal algebraic spaces (Stacks 0AIJ)

An affine formal algebraic space over a scheme is *countably indexed* when it admits a
presentation by affine schemes indexed by `ℕ`, with thickenings for transition maps.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsCountablyIndexed`: **Stacks 0AIJ**.

## Implementation notes

The sequential condition is one of the equivalent presentations of Stacks 0AII. It is stated as
a predicate on the underlying fppf sheaf; applications to formal algebraic spaces also assume
`AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace`. Being an abbreviation, the
existence of a sequential presentation can be used directly by clients, with no unfolding lemma.

The clause is literally the colimit clause of `IsAffineFormalAlgebraicSpace` (**Stacks 0AI7**,
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine.lean`) specialised to the index category `ℕ`:
the same diagram `D ⋙ inclusion ⋙ sheafifiedYoneda`, the same thickening condition on the
transition maps, and the same `FppfSheaf` ambient category. Only the index changes, from an
arbitrary directed preorder to `ℕ`, so the two should stay spelled alike.

## References

* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIJ.** An fppf sheaf is *countably indexed* when it admits a presentation indexed
by `ℕ` by affine schemes whose transition maps are thickenings. For an affine formal algebraic
space this is the countably indexed property. -/
@[stacks 0AIJ]
abbrev IsCountablyIndexed (X : FppfSheaf B S hS) : Prop :=
  ∃ D : ℕ ⥤ BigAffineFppf B S hS,
    (∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
      Nonempty (X ≅ colimit
        (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

end AlgebraicGeometry.FormalSpace

end
