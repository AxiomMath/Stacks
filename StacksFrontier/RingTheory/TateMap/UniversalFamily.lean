module

public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamily
public import StacksFrontier.RingTheory.Different.Formula.LocalizedCompleteIntersection

/-!
# The universal quasi-finite family over a ring of any universe

Example 0FK8 forms the polynomial ring `ℤ[a_{i, E}]` of the coefficients of `n` polynomials in
`n` variables of total degree at most `d`, and the `n` universal polynomials
`f_i = ∑_E a_{i, E} x^E` over it. `AlgebraicGeometry.universalCoefficientRing` and
`AlgebraicGeometry.universalPolynomial` are that ring and those polynomials; they live in
`Type`. Here the same family is read over the coefficient ring `ULift ℤ`, so that it lives in an
arbitrary universe `u` and can be compared with rings of that universe, and its *basic charts*
`A[x_1, …, x_n, 1/k]/(f_1, …, f_n)` are introduced, in the form of Tag 0BWH.

## Main definitions

* `Stacks.TateMap.univBase n d`: the coefficient ring `ℤ[a_{i, E}]`, in universe `u`.
* `Stacks.TateMap.univBaseMap n d`: the comparison `universalCoefficientRing n d → univBase n d`.
* `Stacks.TateMap.univPoly n d`: the universal polynomials over `univBase n d`, the images of
  `AlgebraicGeometry.universalPolynomial n d`.
* `Stacks.TateMap.univChart n d k`: the basic chart
  `univBase[x_1, …, x_n, 1/k]/(f_1, …, f_n)` attached to a polynomial `k`.

## References

* [Stacks Project, Tag 0FK8](https://stacks.math.columbia.edu/tag/0FK8)
* [Stacks Project, Tag 0BWH](https://stacks.math.columbia.edu/tag/0BWH)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.TateMap

open _root_.AlgebraicGeometry

/-- The ring `ℤ[a_{i, E}]` of universal coefficients of Example 0FK8, over `ULift ℤ` so that it
lives in the universe `u`. -/
abbrev univBase (n d : ℕ) : Type u :=
  MvPolynomial (Fin n × MultiIndex n d) (ULift.{u} ℤ)

/-- The comparison of the coefficient ring of Example 0FK8 with its copy in universe `u`: the
identity on the variables `a_{i, E}`. -/
def univBaseMap (n d : ℕ) : universalCoefficientRing n d →+* univBase.{u} n d :=
  MvPolynomial.map (Int.castRingHom (ULift.{u} ℤ))

/-- The universal polynomials `f_i = ∑_E a_{i, E} x^E` over `univBase n d`. -/
def univPoly (n d : ℕ) (i : Fin n) : MvPolynomial (Fin n) (univBase.{u} n d) :=
  MvPolynomial.map (univBaseMap n d) (universalPolynomial n d i)

/-- The basic chart `univBase[x_1, …, x_n, 1/k]/(f_1, …, f_n)` of the universal family attached to
a polynomial `k` in `n` variables over `univBase n d`. -/
abbrev univChart (n d : ℕ) (k : MvPolynomial (Fin n) (univBase.{u} n d)) : Type u :=
  Stacks.Discriminant.localizedCompleteIntersection (univBase.{u} n d) n k (univPoly n d)

end Stacks.TateMap
