module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms to a target with affine diagonal

A morphism `g : X ⟶ Y` of schemes over `S` whose source is affine over `S` is itself affine as
soon as the diagonal `Y ⟶ Y ×_S Y` is affine, in particular when `Y` is separated over `S`.
Taking `S` terminal gives the absolute forms.

## Main results

* `AlgebraicGeometry.isAffineHom_of_isAffineHom_of_isAffineHom_diagonal`: affine source over `S`
  and affine diagonal of the target over `S` imply the morphism is affine.
* `AlgebraicGeometry.isAffineHom_of_isAffineHom_of_isSeparated`: the same with the target
  separated over `S`.
* `AlgebraicGeometry.isAffineHom_of_isAffine_of_isAffineHom_diagonal` and
  `AlgebraicGeometry.isAffineHom_of_isAffine_of_isSeparated`: the absolute forms, for a morphism
  out of an affine scheme.

## References

* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Affineness of a morphism can be cancelled against an affine diagonal: if `f ≫ g` is affine
and the diagonal of `g` is affine, then `f` is affine. -/
public instance isAffineHom_hasOfPostcompProperty_diagonal :
    MorphismProperty.HasOfPostcompProperty
      (@IsAffineHom : MorphismProperty Scheme.{u})
      (MorphismProperty.diagonal (@IsAffineHom : MorphismProperty Scheme.{u})) :=
  haveI : MorphismProperty.RespectsIso (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  haveI : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.diagonal (@IsAffineHom : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderBaseChange.diagonal
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl

variable {S X Y : Scheme.{u}}

/-- Let `g : X ⟶ Y` be a morphism of schemes over `S`. If `X` is affine over `S` and the diagonal
`Y ⟶ Y ×_S Y` is affine, then `g` is affine. -/
@[stacks 01SG "part (1)"]
public theorem isAffineHom_of_isAffineHom_of_isAffineHom_diagonal (g : X ⟶ Y) {a : X ⟶ S}
    (b : Y ⟶ S) (hab : g ≫ b = a) [IsAffineHom a]
    [IsAffineHom (pullback.diagonal b)] : IsAffineHom g := by
  subst hab
  exact MorphismProperty.of_postcomp (W := (@IsAffineHom : MorphismProperty Scheme.{u}))
    (W' := MorphismProperty.diagonal (@IsAffineHom : MorphismProperty Scheme.{u})) g b
    (MorphismProperty.diagonal_iff.mpr ‹IsAffineHom (pullback.diagonal b)›) ‹_›

/-- Let `g : X ⟶ Y` be a morphism of schemes over `S`. If `X` is affine over `S` and `Y` is
separated over `S`, then `g` is affine. -/
@[stacks 01SG "part (2)"]
public theorem isAffineHom_of_isAffineHom_of_isSeparated (g : X ⟶ Y) {a : X ⟶ S} (b : Y ⟶ S)
    (hab : g ≫ b = a) [IsAffineHom a] [IsSeparated b] : IsAffineHom g :=
  have : IsClosedImmersion (pullback.diagonal b) := IsSeparated.isClosedImmersion_diagonal
  isAffineHom_of_isAffineHom_of_isAffineHom_diagonal g b hab

/-- A morphism from an affine scheme to a scheme with affine
diagonal is affine. -/
@[stacks 01SG "part (3)"]
public theorem isAffineHom_of_isAffine_of_isAffineHom_diagonal (g : X ⟶ Y) [IsAffine X]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] : IsAffineHom g :=
  have : IsAffineHom (terminal.from X) := isAffineHom_of_isAffine _
  isAffineHom_of_isAffineHom_of_isAffineHom_diagonal g (terminal.from Y) (terminal.comp_from g)

/-- A morphism from an affine scheme to a separated scheme is affine. -/
@[stacks 01SG "part (4)"]
public theorem isAffineHom_of_isAffine_of_isSeparated (g : X ⟶ Y) [IsAffine X]
    [Y.IsSeparated] : IsAffineHom g :=
  have : IsSeparated (terminal.from Y) := Scheme.IsSeparated.isSeparated_terminal_from
  have : IsClosedImmersion (pullback.diagonal (terminal.from Y)) :=
    IsSeparated.isClosedImmersion_diagonal
  isAffineHom_of_isAffine_of_isAffineHom_diagonal g

end AlgebraicGeometry

end
