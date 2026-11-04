module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Exceptional curves of the first kind

An *exceptional curve of the first kind* on a scheme `X` is an effective Cartier divisor `E ⊆ X`
together with an isomorphism `𝐏¹_k ≅ E` under which the normal sheaf of `E` in `X` pulls back to
`𝒪(-1)`. This is the hypothesis of Stacks 0C2K and of the contraction results that follow it.

The projective line is presented here as `Proj` of the graded polynomial ring `k[T₀, T₁]`, which
is the presentation under which `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`
(Tag 01MN) supplies the twists, so `𝒪(-1)` is available with no further identification.

## Main definitions

* `AlgebraicGeometry.projectiveLineProj` — the projective line over a field, as `Proj k[T₀, T₁]`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` — the property of an
  ideal sheaf, relative to a chosen isomorphism of its subscheme with the projective line.

## Implementation notes

**Two models of the projective line.** `AlgebraicGeometry.projectiveLine` already exists, built
by gluing two copies of `Spec k[X]` along `Spec k[T, T⁻¹]` (Tag 01JE,
`AlgebraicGeometry.projectiveLineGluingData`), and it is defined over any `CommRing k`. The twists
`𝒪(d)` of Tag 01MN are constructed on `Proj` of a graded ring, not on a glued scheme, so the
normal-sheaf condition below cannot be stated against the glued model without an identification of
the two — and no isomorphism between them is proved anywhere in the library. Hence the separate
name `projectiveLineProj` for the `Proj` model. The two are isomorphic.

The isomorphism `e : projectiveLineProj k ≅ D.subscheme` is a *parameter* of the predicate rather
than an existential inside it: the normal-sheaf condition is stated by pulling the normal sheaf
back along `e`, so the predicate cannot be phrased without naming `e`. Consumers that want the
bare property quantify over `k` and `e` themselves. This follows the shape in which the Stacks
proof of 0C2K uses the hypothesis: it fixes the isomorphism and then reads the twists off it.

No `@[stacks]` attribute is attached. Tag 0C2K asserts the structure of the ring of compatible
functions on the thickenings of such a curve, not the definition of the curve, and the Stacks
definition of an exceptional curve of the first kind is carried by a different tag.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- The grading of `k[T₀, T₁]` by total degree, given by its homogeneous submodules. -/
local instance instGradedAlgebraMvPolynomialFinTwo (k : Type u) [Field k] :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 2) k) :=
  MvPolynomial.gradedAlgebra

/-- The projective line over a field, as the `Proj` of the graded polynomial ring `k[T₀, T₁]`.
This is the presentation under which Tag 01MN supplies the twisting sheaves `𝒪(d)`. -/
public abbrev projectiveLineProj (k : Type u) [Field k] : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]

/-- **An exceptional curve of the first kind.** Relative to an isomorphism
`e : 𝐏¹_k ≅ E` of the projective line with the subscheme cut out by `D`, the ideal sheaf `D` is
an exceptional curve of the first kind when it is an effective Cartier divisor and the normal
sheaf of `E` in `X` pulls back along `e` to the twist `𝒪(-1)`. -/
public def IsExceptionalCurveOfFirstKind (e : projectiveLineProj k ≅ D.subscheme) : Prop :=
  Stacks.Divisors.IsEffectiveCartierDivisor D ∧
    Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
        (Stacks.Divisors.normalSheaf D.subschemeι) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))

/-- An exceptional curve of the first kind is an effective Cartier divisor. -/
public theorem IsExceptionalCurveOfFirstKind.isEffectiveCartierDivisor
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e) :
    Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1

/-- The normal-sheaf clause of an exceptional curve of the first kind. -/
public theorem IsExceptionalCurveOfFirstKind.nonempty_normalSheafIso
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e) :
    Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
        (Stacks.Divisors.normalSheaf D.subschemeι) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1)) := hE.2

end Scheme.IdealSheafData

end AlgebraicGeometry
