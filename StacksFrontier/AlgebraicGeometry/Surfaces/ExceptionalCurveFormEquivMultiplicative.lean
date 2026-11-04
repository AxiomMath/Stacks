module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveMonomialSymbol
public import StacksFrontier.AlgebraicGeometry.TwistTensor.MulSectionDegreeSection

/-!
# The binary forms are the sections of the twists, multiplicatively

`AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceFormEquiv` identifies the binary forms of
degree `d` over a field `k` with the global sections of `𝒪(d)` on the projective line. This file
records that the identification is multiplicative across degrees: it carries the product of a
form of degree `d` and a form of degree `e` to the product of their sections under Equation 01MO,
the canonical multiplication

`𝒪(d) ⊗ 𝒪(e) ⟶ 𝒪(d + e)`,  `u / 1 ⊗ v / 1 ↦ uv / 1`,

modulo the transport along `(d : ℤ) + (e : ℤ) = ((d + e : ℕ) : ℤ)` that the two spellings of the
degree force.

## The crossing

`Stacks.AlgebraicGeometry.TwistTensor.mulSection_degreeSection` is the statement for an arbitrary
graded ring `𝒮` and the canonical sections
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` of its twists, in an arbitrary pair of
natural-number degrees. `gradedPieceFormEquiv` is
`Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear` on the projective line, made an
isomorphism by `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSectionLinear`.

What crosses between the two is a retyping: the graded ring is
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1`, whose degree-`d` piece is
`MvPolynomial.homogeneousSubmodule (Fin 2) k d` with no cast, its twisted global sections are
`AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceTwistSections k d`, and
`Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear_apply` says the linear map is
`degreeSection` itself. So every identification in sight holds definitionally, and the statement
below is the general one read at those spellings.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceFormEquiv_apply` — the identification of the
  degree-`d` forms with `H⁰(𝐏¹_k, 𝒪(d))` is the canonical section map.
* `AlgebraicGeometry.Scheme.IdealSheafData.mulSection_gradedPieceFormEquiv` — **the
  identification is multiplicative**: the canonical multiplication of twists carries the sections
  of two forms to the section of their product.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.TwistTensor
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable (k : Type u) [Field k]

/-- **The identification of the degree-`d` binary forms with `H⁰(𝐏¹_k, 𝒪(d))` is the canonical
section map**: the section attached to a form `u` is the one whose value at every point is the
fraction `u / 1`. -/
public theorem gradedPieceFormEquiv_apply (d : ℕ)
    (u : MvPolynomial.homogeneousSubmodule (Fin 2) k d) :
    gradedPieceFormEquiv k d u = degreeSection (polyGrading k 1) d u := rfl

/-- **The identification of the binary forms with the sections of the twists on `𝐏¹_k` is
multiplicative across degrees.** Equation 01MO carries the sections attached to a form of degree
`d` and a form of degree `e` to the section attached to their product, a form of degree `d + e`.

The product form is supplied separately together with the equation pinning it down, so that it is
read in the degree `d + e`; the transport is along `(d : ℤ) + (e : ℤ) = ((d + e : ℕ) : ℤ)`, which
is the one a power system of twists carries on its successor comparison. -/
public theorem mulSection_gradedPieceFormEquiv (d e : ℕ)
    (u : MvPolynomial.homogeneousSubmodule (Fin 2) k d)
    (v : MvPolynomial.homogeneousSubmodule (Fin 2) k e)
    (uv : MvPolynomial.homogeneousSubmodule (Fin 2) k (d + e))
    (huv : (uv : MvPolynomial (Fin 2) k)
      = (u : MvPolynomial (Fin 2) k) * (v : MvPolynomial (Fin 2) k)) :
    (eqToHom (congrArg (twist (polyGrading k 1))
          (show (d : ℤ) + (e : ℤ) = ((d + e : ℕ) : ℤ) by push_cast; ring))).val.app
        (op (⊤ : TopologicalSpace.Opens (ProjectiveSpectrum.top (polyGrading k 1))))
        (mulSection (polyGrading k 1) (d : ℤ) (e : ℤ)
          (op (⊤ : TopologicalSpace.Opens (ProjectiveSpectrum.top (polyGrading k 1))))
          (gradedPieceFormEquiv k d u) (gradedPieceFormEquiv k e v)) =
      gradedPieceFormEquiv k (d + e) uv :=
  mulSection_degreeSection (polyGrading k 1) d e u v uv huv

end AlgebraicGeometry.Scheme.IdealSheafData

end
