module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine

/-!
# Presentations of affine formal algebraic spaces by thickenings

An affine formal algebraic space is an fppf sheaf satisfying a set-theoretic condition and
admitting a presentation as the colimit of a directed diagram of affine schemes whose transition
morphisms are thickenings. This file isolates the second condition.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasThickeningPresentation`: an fppf sheaf is the colimit of a
  directed diagram of affine schemes over `S` with thickenings as transition morphisms.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_iff_hasThickeningPresentation`: an
  fppf sheaf is an affine formal algebraic space if and only if it satisfies the set-theoretic
  condition and has a presentation by thickenings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The geometric half of the definition of an affine formal algebraic space: an fppf sheaf is
the colimit of a directed diagram of affine schemes over `S` all of whose transition morphisms
are thickenings. -/
abbrev HasThickeningPresentation (X : FppfSheaf B S hS) : Prop :=
  ∃ (I : Type (u + 1)) (pre : Preorder I),
    letI : Preorder I := pre
    Nonempty I ∧ IsDirected I (· ≤ ·) ∧
      ∃ D : I ⥤ BigAffineFppf B S hS,
        (∀ ⦃i j : I⦄ (f : i ⟶ j),
          Stacks.Thickenings.IsThickening
            ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
          Nonempty (X ≅ colimit
            (D ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

/-- An affine formal algebraic space is exactly an fppf sheaf satisfying the set-theoretic
condition and admitting a presentation by affine thickenings
(`AlgebraicGeometry.FormalSpace.HasThickeningPresentation`): the second conjunct of
`AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace` is that presentation, spelled out. -/
theorem isAffineFormalAlgebraicSpace_iff_hasThickeningPresentation (X : FppfSheaf B S hS) :
    IsAffineFormalAlgebraicSpace B S hS X ↔
      SatisfiesSetTheoreticCondition B S hS X ∧ HasThickeningPresentation B S hS X :=
  Iff.rfl

end AlgebraicGeometry.FormalSpace

end
