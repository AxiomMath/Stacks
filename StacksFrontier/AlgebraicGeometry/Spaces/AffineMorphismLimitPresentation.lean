module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Algebraic spaces affine over a base, as presheaves over it

This module provides the inclusion of the algebraic spaces affine over an algebraic space `Y`
into the presheaves over the presheaf underlying `Y`, used by the limit presentations of affine
and finite morphisms of algebraic spaces.  Stacks 0870 itself, an affine morphism to a
quasi-compact and quasi-separated algebraic space as a directed limit of morphisms affine and of
finite presentation, is
`AlgebraicGeometry.Space.exists_directed_limit_isFinitePresentation_of_isAffineHom`.

## Main definitions

* `AlgebraicGeometry.Space.affineOverToOver` is the inclusion of the algebraic spaces affine
  over `Y` into the presheaves over the presheaf underlying `Y`.

## References

* [Stacks Project, Tag 0870](https://stacks.math.columbia.edu/tag/0870)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Algebraic spaces affine over `Y`, read as presheaves over the presheaf underlying `Y`. -/
abbrev affineOverToOver (Y : AlgebraicSpaces B S hS) : AffineOver B S hS Y ⥤ Over Y.obj :=
  ObjectProperty.ι _ ⋙ Over.post (ObjectProperty.ι (IsAlgebraicSpace B S hS))

end AlgebraicGeometry.Space

end
