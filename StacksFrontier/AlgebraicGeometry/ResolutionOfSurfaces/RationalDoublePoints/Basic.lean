module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Basic.AffineFormsAndDerivations
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Basic.CoefficientsAndColength
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Basic.QuadraticInIdealSquare

/-!
# Quadratic elements in the square of an ideal of a polynomial ring

Over a field, a nonzero polynomial of degree at most two in two variables that belongs to the
square of an ideal of colength greater than one is a scalar multiple of the square of an affine
linear polynomial.

## Main results

* `MvPolynomial.eq_smul_sq_affineLinear_of_mem_ideal_sq` (in
  `Basic/QuadraticInIdealSquare.lean`): the quadratic polynomial is a scalar multiple of the
  square of an affine linear polynomial.
* `MvPolynomial.pderiv_mem_of_mem_pow_two` (in `Basic/AffineFormsAndDerivations.lean`): a
  partial derivative of an element of `I ^ 2` lies in `I`.
* `MvPolynomial.pderiv_zero_quadratic` and `MvPolynomial.pderiv_one_quadratic` (in
  `Basic/CoefficientsAndColength.lean`): the two partial derivatives of a general quadratic in
  two variables.

## Implementation notes

The polynomial ring `κ[x, y]` is represented by `MvPolynomial (Fin 2) κ`, with variables `X 0`
and `X 1`. Colength greater than one is expressed using `Module.rank`, so the statement also
covers ideals whose quotient has infinite dimension.

The characteristic-two case is separated out: there the two partial derivatives no longer
determine the quadratic, and the argument instead translates the variables and uses a
derivation of `κ` over `ZMod 2` to detect non-squares.

## References

* [Stacks Project, Tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD)
-/
