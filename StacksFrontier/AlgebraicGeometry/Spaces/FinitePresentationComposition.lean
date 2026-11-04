module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Composition of morphisms of algebraic spaces of finite presentation

A morphism of algebraic spaces is of finite presentation when it is locally of finite
presentation, quasi-compact and quasi-separated (Tag 03XP, part (3)). Each of those three
properties is stable under composition, so finite presentation is too.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_comp`: **Stacks 03XQ**, the case of being of
  finite presentation.

## Implementation notes

This is the second of the two assertions of Tag 03XQ; the first, the case of being locally of
finite presentation, is `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp`.

Since `AlgebraicGeometry.Space.IsFinitePresentation` is an abbreviation for a conjunction, the
proof is the triple of the three composition lemmas for its conjuncts: Tag 03XQ for the local
condition, Tag 03HG for quasi-compactness and Tag 03KQ for quasi-separatedness. The three
algebraicity hypotheses are those needed by the constituents: the local condition needs all
three objects, quasi-compactness the target of the first morphism and the final target, and
quasi-separatedness all three.

## References

* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03XQ**, the case of being of finite presentation: the composite of two morphisms
of algebraic spaces over `S` which are of finite presentation is of finite presentation.

Finite presentation is local finite presentation together with quasi-compactness and
quasi-separatedness, and each of the three is stable under composition. -/
@[stacks 03XQ "finite presentation"]
theorem isFinitePresentation_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsFinitePresentation B S hS f)
    (hg : IsFinitePresentation B S hS g) :
    IsFinitePresentation B S hS (f ≫ g) :=
  ⟨isLocallyOfFinitePresentation_comp B S hS hF hG hH f g hf.1 hg.1,
    isQuasiCompact_comp B S hS hG hH f g hf.2.1 hg.2.1,
    isQuasiSeparated_comp B S hS hF hG f g hf.2.2 hg.2.2⟩

end AlgebraicGeometry.Space

end
