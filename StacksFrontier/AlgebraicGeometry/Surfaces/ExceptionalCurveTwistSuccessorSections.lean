module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormEquivMultiplicative
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistSuccessor

/-!
# The successor comparison of the twists of `𝐏¹_k` on the sections attached to binary forms

`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistSuccessor.lean` records that the
one-step cross-degree law of the coherent family of twists is stated against the *successor*
comparisons of the two power systems rather than against
`Stacks.Monoidal.PowerSystem.mulIso`, and then names what is left on the `𝐏¹_k` side: the
multiplicativity of the identification of binary forms with `H⁰(𝐏¹_k, 𝒪(d))` is
`AlgebraicGeometry.Scheme.IdealSheafData.mulSection_gradedPieceFormEquiv`, which is stated
against `Stacks.AlgebraicGeometry.TwistTensor.mulSection`, while the one-step law consumes
`AlgebraicGeometry.projectiveLineTwistPowerSystem`'s `succIso`.  The two spellings of the tensor
product are definitionally equal, and that file asks for the crossing to be done "once, under a
name, rather than inside a larger term".

This file is that name.

## The crossing

`AlgebraicGeometry.projectiveLineTwistPowerSystem` has
`succIso n = twistMultiplicationIso 𝒮 cover (n : ℤ) 1 ≪≫ eqToIso …`, and
`Stacks.AlgebraicGeometry.TwistTensor.twistMul` is `twistMultiplicationMap`, the underlying
morphism of that same isomorphism, retyped so that its source is the tensor-bifunctor spelling
`Stacks.AlgebraicGeometry.TwistTensor.twistTensorObj` rather than the monoidal `⊗` of
`Stacks.PullbackSheafTensor.monoidalModules`.  So the section of the successor comparison at a
pure tensor *is* `Stacks.AlgebraicGeometry.TwistTensor.mulSection` followed by the transport
along `(d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ)`, and the statement below is
`mulSection_gradedPieceFormEquiv` read in the bidegree `(d, 1)` with nothing else to do.

Both crossings hold by definitional unfolding alone — the sections of
`twistTensorObj (polyGrading k 1) d 1` over `⊤` are accepted directly as sections of
`projectiveLineTwistPowerSystem`'s `obj d ⊗ gen`, and the transport
`eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf _) _)` of the power system is accepted
as the `eqToHom (congrArg (Stacks.AlgebraicGeometry.TwistTensor.twist _) _)` of
`mulSection_gradedPieceFormEquiv`.  Neither crossing needs a `rw`, which matters because
rewriting across these index spellings fails for want of a type-correct motive.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.projectiveLineTwistPowerSystem_succIso_app_gradedPieceFormEquiv` — **the successor comparison
  of the twists of `𝐏¹_k` carries the sections of a form of degree `d` and a form of degree `1`
  to the section of their product**, a form of degree `d + 1`.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.Monoidal (PowerSystem)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.TwistTensor
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Stacks.PullbackSheafTensor.monoidalModules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable (k : Type u) [Field k]

/-- **The successor comparison of the twists of `𝐏¹_k` is multiplicative on the sections attached
to binary forms.**  Applied to the pure tensor of the section of a form `u` of degree `d` and the
section of a form `v` of degree `1`, it is the section of the product form `uv` of degree
`d + 1`.

This is `AlgebraicGeometry.Scheme.IdealSheafData.mulSection_gradedPieceFormEquiv` in the bidegree
`(d, 1)`, crossed to the spelling the one-step cross-degree law
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.curveTwistIso_tensorHom_comp_succIso` is stated at.  The product form is supplied separately
with the equation pinning it down, so that it is read in the degree `d + 1`. -/
public theorem projectiveLineTwistPowerSystem_succIso_app_gradedPieceFormEquiv (d : ℕ)
    (u : MvPolynomial.homogeneousSubmodule (Fin 2) k d)
    (v : MvPolynomial.homogeneousSubmodule (Fin 2) k 1)
    (uv : MvPolynomial.homogeneousSubmodule (Fin 2) k (d + 1))
    (huv : (uv : MvPolynomial (Fin 2) k)
      = (u : MvPolynomial (Fin 2) k) * (v : MvPolynomial (Fin 2) k)) :
    ((projectiveLineTwistPowerSystem k).succIso d).hom.val.app
        (op (⊤ : TopologicalSpace.Opens (ProjectiveSpectrum.top (polyGrading k 1))))
        ((PresheafOfModules.tensorSheafUnit (twist (polyGrading k 1) (d : ℤ))
            (twist (polyGrading k 1) (1 : ℤ))).app
          (op (⊤ : TopologicalSpace.Opens (ProjectiveSpectrum.top (polyGrading k 1))))
          (gradedPieceFormEquiv k d u ⊗ₜ gradedPieceFormEquiv k 1 v))
      = gradedPieceFormEquiv k (d + 1) uv :=
  mulSection_gradedPieceFormEquiv k d 1 u v uv huv

end AlgebraicGeometry.Scheme.IdealSheafData

end
