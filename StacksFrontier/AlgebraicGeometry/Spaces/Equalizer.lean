module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent

/-!
# Equalizers of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f, g : X ⟶ Y` be two morphisms
of algebraic spaces over `S`. The equalizer of `f` and `g` exists as a presheaf, the category
of presheaves on the big fppf site of `S` having all limits, and it *is* an algebraic space
over `S`: by `CategoryTheory.Limits.isPullback_equalizer_prod` it is the fibre product of
`(f, g) : X ⟶ Y ⨯ Y` and the diagonal `Y ⟶ Y ⨯ Y`, and a fibre product of algebraic spaces
over a sheaf with representable diagonal is an algebraic space by Stacks 04T9.

The same cartesian square gives the two basic properties of the inclusion
`equalizer.ι f g : equalizer f g ⟶ X`: it is a monomorphism, hence separated, and it is
locally of finite type, being a base change of the diagonal of `Y`.

No new construction is needed for any of this: the general "an equalizer is a fibre product
of the diagonal" square is Mathlib's, and everything below instantiates it.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_equalizer`: the equalizer of two morphisms of
  algebraic spaces over `S` is an algebraic space over `S`.
* `AlgebraicGeometry.Space.isSeparated_equalizer_ι`: the inclusion of the equalizer is a
  separated morphism.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_equalizer_ι`: the inclusion of the
  equalizer is locally of finite type.
* `AlgebraicGeometry.Space.relative_locallyOfFiniteType_equalizer_ι`: the relative form of
  the previous statement, that every represented base change of the inclusion is a morphism
  of schemes locally of finite type.

## What is assumed

Nothing. The equalizer is Mathlib's `CategoryTheory.Limits.equalizer` in the presheaf
category, which has all limits because `Type u` does; the cartesian square identifying it
with a base change of the diagonal is
`CategoryTheory.Limits.isPullback_equalizer_prod`; algebraicity is Stacks 04T9 in the form
`AlgebraicGeometry.isAlgebraicSpace_of_isPullback`, applied with `Y ⨯ Y` as the base, which
is an algebraic space by Stacks 02X0 (`AlgebraicGeometry.isAlgebraicSpace_prod`) and so is a
sheaf with representable diagonal; and local finite typeness of the diagonal of an algebraic
space is Stacks 02X4 in the form
`AlgebraicGeometry.presheaf_locallyOfFiniteType_diag`.

## Implementation notes

`AlgebraicGeometry.Space.IsLocallyOfFiniteType` is the every-étale-chart condition, while
base change is available for the relative (represented-base-change) condition, so
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative` — Stacks 03MJ for a
representable morphism — is used to pass between them. Representability of
`equalizer.ι f g`, which that equivalence needs, comes out of the relative property itself.

## References

* [Stacks Project, Tag 02X0](https://stacks.math.columbia.edu/tag/02X0)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 04T9** for an equalizer: the equalizer of two morphisms of algebraic spaces over
`S` is an algebraic space over `S`.

The equalizer of `f` and `g` is the fibre product of `(f, g) : X ⟶ Y ⨯ Y` and the diagonal
of `Y`, and `Y ⨯ Y` is an algebraic space over `S`, hence a sheaf with representable
diagonal. -/
theorem isAlgebraicSpace_equalizer (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f g : X ⟶ Y) :
    IsAlgebraicSpace B S hS (equalizer f g) :=
  isAlgebraicSpace_of_isPullback hX hY (isAlgebraicSpace_prod B S hS hY hY).isSheaf
    (isAlgebraicSpace_prod B S hS hY hY).diagonal_representable
    (isPullback_equalizer_prod f g)

/-- The inclusion of the equalizer of two morphisms of presheaves on the big fppf site of `S`
is a separated morphism of algebraic spaces over `S`: it is a monomorphism. -/
theorem isSeparated_equalizer_ι (f g : X ⟶ Y) :
    IsSeparated B S hS (equalizer.ι f g) :=
  isSeparated_of_mono (equalizer.ι f g) inferInstance

/-- Every represented base change of the inclusion of the equalizer of two morphisms of
algebraic spaces over `S` is a morphism of schemes which is locally of finite type: the
inclusion is a base change of the diagonal of the target, and Stacks 02X4 applies to the
latter. -/
theorem relative_locallyOfFiniteType_equalizer_ι (hY : IsAlgebraicSpace B S hS Y)
    (f g : X ⟶ Y) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (equalizer.ι f g) :=
  (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
    (isPullback_equalizer_prod f g).flip
    (presheaf_locallyOfFiniteType_diag B S hS Y hY)

/-- The inclusion of the equalizer of two morphisms of algebraic spaces over `S` is locally
of finite type. -/
theorem isLocallyOfFiniteType_equalizer_ι (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f g : X ⟶ Y) :
    IsLocallyOfFiniteType B S hS (equalizer.ι f g) :=
  (holdsOnEveryEtaleChart_iff_relative B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_equalizer B S hS hX hY f g) hX (equalizer.ι f g)
    (relative_locallyOfFiniteType_equalizer_ι B S hS hY f g).rep).2
      (relative_locallyOfFiniteType_equalizer_ι B S hS hY f g)

end AlgebraicGeometry.Space

end
