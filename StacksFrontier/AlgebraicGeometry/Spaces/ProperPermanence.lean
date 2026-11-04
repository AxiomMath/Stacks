module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Composition of finite type and proper morphisms of algebraic spaces

A composition of morphisms of algebraic spaces over a scheme `S` which are of finite type is
of finite type, and a composition of proper morphisms is proper.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_comp'` is the global half of Stacks 03XG: a composition
  of morphisms of finite type is of finite type. The local half is
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_comp'`.
* `AlgebraicGeometry.Space.isProper_comp'` is Stacks 04XY: a composition of proper morphisms is
  proper.

## Implementation notes

Both statements are conjunctwise. Finite type is local finite type together with
quasi-compactness, so `AlgebraicGeometry.Space.isFiniteType_comp'` pairs
`AlgebraicGeometry.Space.isLocallyOfFiniteType_comp'` with
`AlgebraicGeometry.Space.IsQuasiCompact.comp` of Stacks 03HG. Properness is separatedness,
finite type and universal closedness, so `AlgebraicGeometry.Space.isProper_comp'` pairs those
two with `AlgebraicGeometry.Space.isSeparated_comp` and
`AlgebraicGeometry.Space.universallyClosed_comp` of Stacks 03IU.

Algebraicity of the source is needed by neither statement and is assumed by neither. That is
what the primes mark: `AlgebraicGeometry.Space.isFiniteType_comp` and
`AlgebraicGeometry.Space.isProper_comp` are the forms carrying the hypothesis, read off the
every-étale-chart permanence of Stacks 0AML, and each of the two statements here implies the
corresponding one of those.

## References

* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03XG, finite type.** The composite of two morphisms of algebraic spaces over `S`
which are of finite type is of finite type.

Algebraicity of the source is not needed and is not assumed, which is what distinguishes this
from `AlgebraicGeometry.Space.isFiniteType_comp`. -/
@[stacks 03XG "finite type"]
theorem isFiniteType_comp' (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (hf : IsFiniteType B S hS f) (hg : IsFiniteType B S hS g) :
    IsFiniteType B S hS (f ≫ g) :=
  ⟨isLocallyOfFiniteType_comp' B S hS f g hY hZ hf.1 hg.1,
    IsQuasiCompact.comp B S hS hY hZ hf.2 hg.2⟩

/-- **Stacks 04XY.** The composite of two proper morphisms of algebraic spaces over `S` is
proper: each of the three conjuncts of properness is stable under composition.

Algebraicity of the source is not needed and is not assumed, which is what distinguishes this
from `AlgebraicGeometry.Space.isProper_comp`. None of the three conjuncts asks for it:
separatedness is a condition on a relative diagonal, and the quantifiers of
`AlgebraicGeometry.Space.IsQuasiCompact` and `AlgebraicGeometry.Space.UniversallyClosed` reach
only the intermediate and final spaces. -/
@[stacks 04XY]
theorem isProper_comp' (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (hf : IsProper B S hS f) (hg : IsProper B S hS g) :
    IsProper B S hS (f ≫ g) :=
  IsProper.mk' B S hS (isSeparated_comp B S hS f g hf.1 hg.1)
    (isFiniteType_comp' B S hS f g hY hZ hf.2.1 hg.2.1)
    (universallyClosed_comp B S hS hY hZ f g hf.2.2 hg.2.2)

end AlgebraicGeometry.Space

end
