module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulOverBase.Acyclic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistMultiplication

/-!
# The Koszul resolution of the structure sheaf of projective space over an arbitrary base

Let `S` be a scheme, `n` a natural number and `a` an integer. The Koszul complex of the
coordinates on the integral model `ℙⁿ_ℤ` pulls back along the projection `ℙⁿ_S ⟶ ℙⁿ_ℤ` to an
**acyclic** complex

`0 ⟶ 𝒪(a) ⟶ 𝒪(a+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ 𝒪(a+n+1) ⟶ 0`

on `ℙⁿ_S` — acyclic over *every* base, because
`Stacks.AlgebraicGeometry.ProjKoszulOverBase.acyclic_pullback_koszulComplex` needs no flatness of
the projection. This file records that complex at the spelling its consumers use: its term in
degree `j` is the direct sum of `binom(n+1, j)` copies of the twist `𝒪(a+j)` of `ℙⁿ_S`, and the
matrix entry of its differential from the summand indexed by a `j`-element set `s` to the summand
indexed by `t` is the Koszul sign of `i` in `s` times multiplication by the coordinate `Tᵢ` when
`t = s ∪ {i}`, and zero otherwise.

The names below are relative to the `Stacks.AlgebraicGeometry.ProjKoszulOverBase` namespace.

## Main definitions

* `koszulOver`: **the Koszul complex of the coordinates on `ℙⁿ_S`.**

## Main results

* `acyclic_koszulOver`: **the complex is acyclic over every base.**
* `isZero_koszulOver_X`: it is concentrated in the degrees `0, …, n+1`.
* `koszulOver_d`: **the differential is the inverse image of the Koszul differential**, whose
  matrix is a signed multiplication by a coordinate on each pair of summands.

## Implementation notes

The terms of the complex are left in the shape the inverse image produces them, namely the
inverse image of a direct sum; a consumer reads them as direct sums of twists of `ℙⁿ_S` by
`CategoryTheory.Functor.mapBiproduct` for whichever additive functor it is applying, the twists
of `ℙⁿ_S` being by definition the inverse images of the twists of the integral model. Introducing
that identification here would fix the functor and force a second comparison at every use.

No `stacks` attribute is attached: the acyclicity is
`Stacks.AlgebraicGeometry.ProjKoszulOverBase.acyclic_pullback_koszulComplex` and the complex is
`Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulComplex`, both of which carry what attribution
there is.

## References

* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjKoszulOverBase

open Stacks.AlgebraicGeometry.ProjKoszulComplex
open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (S : Scheme.{u}) (a : ℤ)

/-- The projection of `ℙⁿ_S` to the integral model, at the spelling
`AlgebraicGeometry.Proj (polyGrading (ULift ℤ) n)` of the target that the Koszul complex lives
on. -/
abbrev toProj : projectiveSpaceOver n S ⟶ AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) n) :=
  projectiveSpaceOver.toIntegralAtUniverse n S

/-- **The Koszul complex of the coordinates on `ℙⁿ_S`**: the termwise inverse image along the
projection to the integral model of the Koszul complex of `ℙⁿ_ℤ`. -/
def koszulOver : CochainComplex (projectiveSpaceOver n S).Modules ℤ :=
  ((Scheme.Modules.pullback (toProj n S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (koszulComplex (ULift.{u} ℤ) n a)

/-- **The Koszul complex of the coordinates on `ℙⁿ_S` is acyclic**, over every base: the inverse
image of the Koszul complex of the integral model stays acyclic along an arbitrary morphism of
schemes. -/
theorem acyclic_koszulOver : (koszulOver n S a).Acyclic :=
  acyclic_pullback_koszulComplex (ULift.{u} ℤ) n (toProj n S) a

/-- **The Koszul complex of `ℙⁿ_S` is concentrated in the degrees `0, …, n+1`.** -/
theorem isZero_koszulOver_X (j : ℤ) (hj : j < 0 ∨ (n : ℤ) + 1 < j) :
    IsZero ((koszulOver n S a).X j) :=
  Functor.map_isZero _ (ExampleGenerator.isZero_koszulComplex_X (ULift.{u} ℤ) n a j hj)

/-- **The differential of the Koszul complex of `ℙⁿ_S`** is the inverse image of the Koszul
differential of the integral model, whose matrix entry from the summand indexed by a set `s` to
the summand indexed by `t` is the Koszul sign of `i` in `s` times multiplication by the
coordinate `Tᵢ`, for the unique `i` with `t = s ∪ {i}`, and zero if there is none. -/
theorem koszulOver_d (j : ℤ) :
    (koszulOver n S a).d j (j + 1) =
      (Scheme.Modules.pullback (toProj n S)).map (koszulDiff (ULift.{u} ℤ) n a j) :=
  congrArg (fun z => (Scheme.Modules.pullback (toProj n S)).map z)
    (koszulComplex_d (ULift.{u} ℤ) n a j)

end Stacks.AlgebraicGeometry.ProjKoszulOverBase

end
