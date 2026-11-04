module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.DoubleMappingCone
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction
public import StacksFrontier.Homology.DoubleExtend

/-!
# The two-term structure of a complex built with `HomologicalComplex.double`

A `NaiveCotangentTwoTerm` is a two-term complex in a triangulated category together with the
distinguished triangle relating it to its two terms. The library builds two-term naive cotangent
complexes `NL(α) = (ℐ/ℐ² ⟶ Ω)` as `HomologicalComplex.double` of the conormal map, in degrees
`-1` and `0`; this file turns such a complex into a `NaiveCotangentTwoTerm` whose underlying
object is that complex, in the derived category of the ambient abelian category.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.ofDouble`: the two-term
  structure, in the derived category, on the image of `HomologicalComplex.double f` with `f` in
  degrees `i₀` and `i₁ = i₀ + 1`.
* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.ofDoubleNegOne`: the case
  `(i₀, i₁) = (-1, 0)`, the degrees in which the naive cotangent complex of a presentation is
  built.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.obstruction_ofDouble_eq_zero_iff`
  and `...NaiveCotangentTwoTerm.conormalExtClass_ofDouble_eq_zero_iff`: the two criteria of
  `NaiveCotangentTwoTerm`, read off on a `double`-built complex.

## Implementation notes

Unlike `AlgebraicGeometry.RingedSpaceThickening.exists_naiveCotangentTwoTerm`, which produces a
two-term structure from `distinguished_cocone_triangle` and therefore pins only the two terms,
this definition pins the underlying object as well: `ofDouble_obj` identifies it with the image
under `DerivedCategory.Q` of the complex `HomologicalComplex.double f` itself. The distinguished
triangle comes from `CochainComplex.doubleTriangleQ_distinguished`, which identifies
`HomologicalComplex.double f` with the mapping cone of the map of single complexes induced
by `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open ComplexShape (upIntRelNegOneZero)

universe w v u

namespace AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X₀ X₁ : C} (f : X₀ ⟶ X₁) {i₀ i₁ : ℤ} (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁)

/-- The two-term structure, in the derived category, of the complex
`HomologicalComplex.double f` with `f : X₀ ⟶ X₁` in degrees `i₀` and `i₁ = i₀ + 1`: its degree
`i₀` term is `X₀`, its degree `i₁` term is `X₁`, its underlying object is the image of the
complex in the derived category, and its distinguished triangle is the one identifying the
complex with the cone on `f`. -/
def ofDouble : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor C i₁) where
  conormal := X₀
  base := X₁
  d := f
  obj := DerivedCategory.Q.obj (double f hi₀₁)
  incl := CochainComplex.doubleInclQ f hi₀₁
  proj := CochainComplex.doubleProjQ f hi₀₁
  distinguished := CochainComplex.doubleTriangleQ_distinguished f hi₀₁

/-- The degree `i₀` term of `ofDouble f hi₀₁` is `X₀`. -/
@[simp]
theorem ofDouble_conormal : (ofDouble f hi₀₁).conormal = X₀ := rfl

/-- The degree `i₁` term of `ofDouble f hi₀₁` is `X₁`. -/
@[simp]
theorem ofDouble_base : (ofDouble f hi₀₁).base = X₁ := rfl

/-- The differential of `ofDouble f hi₀₁` is `f`. -/
@[simp]
theorem ofDouble_d : (ofDouble f hi₀₁).d = f := rfl

/-- The underlying object of `ofDouble f hi₀₁` is the complex
`HomologicalComplex.double f hi₀₁` itself, seen in the derived category. -/
@[simp]
theorem ofDouble_obj :
    (ofDouble f hi₀₁).obj = DerivedCategory.Q.obj (double f hi₀₁) := rfl

/-- The inclusion of the degree `i₁` term into `ofDouble f hi₀₁` is
`CochainComplex.doubleInclQ f hi₀₁`. -/
@[simp]
theorem ofDouble_incl : (ofDouble f hi₀₁).incl = CochainComplex.doubleInclQ f hi₀₁ := rfl

/-- The projection of `ofDouble f hi₀₁` onto the shifted degree `i₀` term is
`CochainComplex.doubleProjQ f hi₀₁`. -/
@[simp]
theorem ofDouble_proj : (ofDouble f hi₀₁).proj = CochainComplex.doubleProjQ f hi₀₁ := rfl

/-- A class in `Ext¹` of a `double`-built two-term complex is the class of a homomorphism out of
the degree `i₀` term exactly when its restriction to the degree `i₁` term vanishes. -/
theorem obstruction_ofDouble_eq_zero_iff (G : C)
    (ξ : DerivedCategory.Q.obj (double f hi₀₁) ⟶
      ((DerivedCategory.singleFunctor C i₁).obj G)⟦(1 : ℤ)⟧) :
    (ofDouble f hi₀₁).obstruction G ξ = 0 ↔
      ∃ g : X₀ ⟶ G, ξ = (ofDouble f hi₀₁).conormalExtClass G g :=
  (ofDouble f hi₀₁).obstruction_eq_zero_iff G ξ

/-- The class in `Ext¹` of a `double`-built two-term complex of a homomorphism `ξ` out of its
degree `i₀` term vanishes exactly when `ξ` factors through the differential. -/
theorem conormalExtClass_ofDouble_eq_zero_iff (G : C) (ξ : X₀ ⟶ G) :
    (ofDouble f hi₀₁).conormalExtClass G ξ = 0 ↔ ∃ θ : X₁ ⟶ G, f ≫ θ = ξ :=
  (ofDouble f hi₀₁).conormalExtClass_eq_zero_iff G ξ

/-- The two-term structure, in the derived category, of the complex
`HomologicalComplex.double f` with `f : X₀ ⟶ X₁` in degrees `-1` and `0`: the degrees in which
the naive cotangent complex `NL(α) = (ℐ/ℐ² ⟶ Ω)` of a presentation is built. -/
def ofDoubleNegOne : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor C 0) :=
  ofDouble f upIntRelNegOneZero

/-- The degree `-1` term of `ofDoubleNegOne f` is `X₀`. -/
@[simp]
theorem ofDoubleNegOne_conormal : (ofDoubleNegOne f).conormal = X₀ := rfl

/-- The degree `0` term of `ofDoubleNegOne f` is `X₁`. -/
@[simp]
theorem ofDoubleNegOne_base : (ofDoubleNegOne f).base = X₁ := rfl

/-- The differential of `ofDoubleNegOne f` is `f`. -/
@[simp]
theorem ofDoubleNegOne_d : (ofDoubleNegOne f).d = f := rfl

/-- The underlying object of `ofDoubleNegOne f` is the complex
`HomologicalComplex.double f upIntRelNegOneZero` itself, seen in the derived category. -/
@[simp]
theorem ofDoubleNegOne_obj :
    (ofDoubleNegOne f).obj = DerivedCategory.Q.obj (double f upIntRelNegOneZero) := rfl

end AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm

end
