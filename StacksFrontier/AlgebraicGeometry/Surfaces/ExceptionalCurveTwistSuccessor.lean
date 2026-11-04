module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistFamily
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap

/-!
# The successor comparison of the coherent family of twists, and the one-step cross-degree law

`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistFamily.lean` builds the chosen
coherent family `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.curveTwistIso` of identifications `e^*(𝒪_X(-dE)|_E) ≅ 𝒪_{𝐏¹_k}(d)` and records its cross-degree
law `curveTwistIso_mul` against the multiplication isomorphisms
`Stacks.Monoidal.PowerSystem.mulIso` of the two power systems.  It then says that two things
stand between that law and the `symbol_mul` axiom of
`AlgebraicGeometry.SemistableReduction.MonomialSymbol`, the first being the identification of
`mulIso p q` with the canonical multiplication in the bidegree `(p, q)` —
`Stacks.Divisors.idealTensorMulIso (D ^ p) (D ^ q)` on one side and Equation 01MO on the other —
each an induction on `q` over an associativity of the canonical multiplication.

**That identification is not needed, and this file is the measurement.** The monomials in two
elements of `I₁` are built by multiplying by a *single* generator repeatedly, so the law a
monomial induction consumes relates the degrees `d`, `1` and `d + 1` only, and that law comes
from `Stacks.Monoidal.PowerSystem.tensorHom_compare_comp_succIso` — the defining relation of
`Stacks.Monoidal.PowerSystem.compare` in positive degree — against the systems' *successor*
comparisons, not against `mulIso`.  Those successor comparisons are already the canonical
multiplications, with nothing to identify:
`AlgebraicGeometry.Scheme.IdealSheafData.curvePowerSystem_succIso` below holds by `rfl`, and
`AlgebraicGeometry.projectiveLineTwistPowerSystem_succIso` is Equation 01MO at `(d, 1)` by `rfl`
already.  So no induction on a second degree, no associativity of `idealTensorMul`, and no
associativity of the twist multiplication enters the monomial argument at all.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.curvePowerSystem_succIso` — the successor comparison
  of the system on the curve is the canonical multiplication `Stacks.Divisors.idealTensorMulIso`
  of ideal sheaves, read through the two comparisons of [Stacks, Tag 01CD] along `E ↪ X` and
  along `e`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.curveTwistIso_tensorHom_comp_succIso` — **the one-step cross-degree law**: multiplying by
  the degree-one generator and then comparing in degree `d + 1` is comparing in degrees `d` and
  `1` and then multiplying.

## What remains for `symbol_mul`

Only the *sections* side.  Both halves of it are statements about taking global sections of the
isomorphisms above, and neither is a choice.

The half on `𝐏¹_k` is proved: `Stacks.AlgebraicGeometry.TwistTensor.mulSection_degreeSection`
says that Equation 01MO carries the global sections attached to two homogeneous polynomials to
the one attached to their product, in every pair of natural-number degrees, so in particular at
`(d, 1)`.  What is left on that side is only the crossing of the two spellings of the tensor
product: `AlgebraicGeometry.projectiveLineTwistPowerSystem` presents its successor comparison
with source `obj d ⊗ gen` at the monoidal structure
`Stacks.PullbackSheafTensor.monoidalModules`, while
`Stacks.AlgebraicGeometry.TwistTensor.mulSection` consumes the pure tensor of
`Stacks.AlgebraicGeometry.TwistTensor.twistTensorObj`, the tensor-bifunctor spelling; the two
are definitionally equal and `Stacks.AlgebraicGeometry.TwistTensor.twistMul_eq` is the one place
that is used, so the crossing wants doing once, under a name, rather than inside a larger term.

The half on the curve is proved, in the one-step form `(d, 1)` and nothing wider: that the kernel
inclusion `Stacks.Divisors.thickeningKernelMap` of [Stacks, Tag 0C4T] carries the canonical
multiplication `Stacks.Divisors.idealTensorMul` of ideal sheaves to the ring multiplication of
the functions on the thickening is
`Stacks.Divisors.idealTensorMul_comp_unit_comp_thickeningKernelMap` in
`StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/SumSequenceMultiplication.lean`.  It
rests on the characteristic property `Stacks.Divisors.unit_comp_sumKernelMap` of the kernel
inclusion, which identifies it on the image of the unit of `i^* ⊣ i_*` with "read the section of
`ℐ_{Dᵈ⁺¹}` inside `𝒪_X` and project to `𝒪_{Dᵈ⁺²}`", together with
`Stacks.Divisors.idealTensorMul_comp_idealInclusion`; its value on a local pure tensor is the
product of the two ambient sections, by `Stacks.Divisors.idealTensorToUnit_app_tmul`.  It is an
equality of *morphisms* out of the tensor product, evaluated on sections only afterwards, because
the unit is an epimorphism of sheaves and not a surjection on `Γ(X, -)`.

That last point is also the limit of what it gives: it describes the kernel inclusion on
everything the unit hits, and a graded piece of the formal neighbourhood is met as an *arbitrary*
section of `Γ(X, i_* i^* ℐ_{Dᵈ⁺¹})`.  For such a section the right-hand side is the product of two
lifts to `Γ(𝒪_{Dᵈ⁺²})` which are not canonical, so the statement covering it must carry them as
hypotheses; the module docstring of the file above records why and what its proof would need.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.Monoidal (PowerSystem)

universe u

attribute [local instance] Stacks.PullbackSheafTensor.monoidalModules

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  (e : projectiveLineProj k ≅ D.subscheme) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **The successor comparison of the system on the curve is the canonical multiplication of
ideal sheaves.**  `AlgebraicGeometry.Scheme.IdealSheafData.curvePowerSystem` is
`Stacks.Divisors.negativeTwistPowerSystem` pulled back twice, so its successor comparison in
degree `d` is `Stacks.Divisors.idealTensorMulIso (D ^ d) D` — the kernel lift of multiplication
of sections, not a choice — transported along `Dᵈ · D = Dᵈ⁺¹` and read through the comparisons of
[Stacks, Tag 01CD] along `E ↪ X` and along `e`.

This holds by `rfl`: `Stacks.PullbackSheafTensor.pullbackPowerSystem_succIso` and
`Stacks.Divisors.negativeTwistPowerSystem_succIso` are both definitional.  It is stated so that a
consumer of the one-step law below can see that nothing on this side is left to identify. -/
public theorem curvePowerSystem_succIso (d : ℕ) :
    (curvePowerSystem D k e).succIso d =
      (Stacks.PullbackSheafTensor.sheafTensorComparisonIso e.hom.toLRSHom.toShHom
            ((Stacks.RingedSpace.pullbackFunctor D.subschemeι.toLRSHom.toShHom).obj
              (Stacks.Divisors.negativeTwist (D ^ d)))
            ((Stacks.RingedSpace.pullbackFunctor D.subschemeι.toLRSHom.toShHom).obj
              (Stacks.Divisors.negativeTwist D))).symm ≪≫
        (Stacks.RingedSpace.pullbackFunctor e.hom.toLRSHom.toShHom).mapIso
          ((Stacks.PullbackSheafTensor.sheafTensorComparisonIso
                D.subschemeι.toLRSHom.toShHom (Stacks.Divisors.negativeTwist (D ^ d))
                (Stacks.Divisors.negativeTwist D)).symm ≪≫
            (Stacks.RingedSpace.pullbackFunctor D.subschemeι.toLRSHom.toShHom).mapIso
              (Stacks.Divisors.idealTensorMulIso (D ^ d) D inferInstance ≪≫
                eqToIso (congrArg Stacks.Divisors.negativeTwist (pow_succ D d).symm))) :=
  rfl

namespace IsExceptionalCurveOfFirstKind

variable {D k e}

/-- **The one-step cross-degree law of the coherent family, as an equality of morphisms.**
Tensoring the comparison in degree `d` with the one chosen degree-one isomorphism
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistGenIso` and then
multiplying on `𝐏¹_k` is multiplying on the curve and then comparing in degree `d + 1`.

This is the law a monomial induction consumes, and unlike
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso_mul` it is
stated against the *successor* comparisons, which are already the canonical multiplications:
`AlgebraicGeometry.Scheme.IdealSheafData.curvePowerSystem_succIso` on the left and
`AlgebraicGeometry.projectiveLineTwistPowerSystem_succIso`, Equation 01MO at `(d, 1)`, on the
right.  So the identification of `Stacks.Monoidal.PowerSystem.mulIso` with the canonical
multiplication in a general bidegree is not on the path to `symbol_mul`. -/
public theorem curveTwistIso_tensorHom_comp_succIso (hE : IsExceptionalCurveOfFirstKind D k e)
    (d : ℕ) :
    ((hE.curveTwistIso d).hom ⊗ₘ hE.curveTwistGenIso.hom) ≫
        ((projectiveLineTwistPowerSystem k).succIso d).hom =
      ((curvePowerSystem D k e).succIso d).hom ≫ (hE.curveTwistIso (d + 1)).hom :=
  PowerSystem.tensorHom_compare_comp_succIso (curvePowerSystem D k e)
    (projectiveLineTwistPowerSystem k) hE.curveTwistGenIso d

end IsExceptionalCurveOfFirstKind

end Scheme.IdealSheafData

end AlgebraicGeometry

end
