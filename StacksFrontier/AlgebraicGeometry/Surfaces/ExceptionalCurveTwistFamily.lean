module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackPowerSystem
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists

/-!
# The coherent family of twists an exceptional curve of the first kind cuts out on itself

Let `E ⊆ X` be an exceptional curve of the first kind with ideal sheaf `D`, presented as the
projective line by `e : 𝐏¹_k ≅ E`. This file constructs a family of isomorphisms
`e^*(𝒪_X(-dE)|_E) ≅ 𝒪_{𝐏¹_k}(d)`, one in each degree `d`, compatible with the multiplications on
the two sides.

The family is the comparison `Stacks.Monoidal.PowerSystem.compare` of two power systems on `𝐏¹_k`
along an isomorphism of their generators:

* the ideal sheaves of the powers of `D`, `n ↦ 𝒪_X(-nE)`, whose successor comparison is the
  canonical multiplication `Stacks.Divisors.idealTensorMulIso`, carried to `𝐏¹_k` along `E ↪ X`
  and along `e`;
* the twists of `𝐏¹_k`, `n ↦ 𝒪(n)`, whose successor comparison is the multiplication
  `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso` of [Stacks, Tag 01MO].

## Main definitions

* `Stacks.Divisors.negativeTwistTopIsoUnit`: the ideal sheaf of the empty divisor is the
  structure sheaf.
* `Stacks.Divisors.negativeTwistPowerSystem`: the ideal sheaves of the powers of an effective
  Cartier divisor, as a power system.
* `AlgebraicGeometry.projectiveLineTwistPowerSystem`: the twists of the projective line, as a
  power system.
* `AlgebraicGeometry.Scheme.IdealSheafData.curvePowerSystem`: the first system carried to `𝐏¹_k`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistGenIso`: the
  isomorphism `e^*(𝒪_X(-E)|_E) ≅ 𝒪_{𝐏¹_k}(1)` of the generators.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso`: the
  family `e^*(𝒪_X(-dE)|_E) ≅ 𝒪_{𝐏¹_k}(d)`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso_mul`: the
  compatibility of the family with the multiplications of the two systems.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso_zero` and
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso_succ`: the
  family in degree zero and in a successor degree.
* `IsExceptionalCurveOfFirstKind.curvePowerSystem_mulIso_assoc` (in
  `AlgebraicGeometry.Scheme.IdealSheafData`): the associativity of the multiplications of the
  system on the curve.

## Implementation notes

`Stacks.Divisors.IsEffectiveCartierDivisor D` is taken as an instance binder on every
declaration rather than produced by a `haveI` from `IsExceptionalCurveOfFirstKind`: a `haveI`
inside a `def` body costs about three orders of magnitude more than an instance binder.

The monoidal structure `Stacks.PullbackSheafTensor.monoidalModules` is activated as a local
instance; see its docstring for why it has to be named at the `structureSheafRing` spelling.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.Monoidal (PowerSystem)

universe u

attribute [local instance] Stacks.PullbackSheafTensor.monoidalModules

namespace Stacks.Divisors

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The ideal sheaf of the empty divisor is the structure sheaf**, `𝒪_X(-∅) ≅ 𝒪_X`. -/
public def negativeTwistTopIsoUnit :
    negativeTwist (⊤ : X.IdealSheafData) ≅
      𝟙_ (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  ((Stacks.SheafOfModules.picardClass_eq_iff X.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) _ _
      (isInvertible_negativeTwist_picard (⊤ : X.IdealSheafData))
      (Stacks.SheafOfModules.isInvertible_unit X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace))).1
    (((negativeTwistPicardClass_eq_neg (⊤ : X.IdealSheafData)).trans
        (by rw [picardClass_top, neg_zero])).trans
      (Stacks.SheafOfModules.picardClass_zero X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)).symm)).some

/-- **The ideal sheaves of the powers of an effective Cartier divisor, as a system of tensor
powers.** The `n`-th piece is `ℐ_{Dⁿ} = 𝒪_X(-nD)`, the generator is `ℐ_D`, and the successor
comparison is the canonical multiplication `Stacks.Divisors.idealTensorMulIso`, an isomorphism
because `D` is effective Cartier, followed by the transport along `Dⁿ · D = Dⁿ⁺¹`. -/
public def negativeTwistPowerSystem (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    PowerSystem (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) where
  gen := negativeTwist D
  obj n := negativeTwist (D ^ n)
  objZeroIso :=
    eqToIso (congrArg negativeTwist
      ((pow_zero D).trans AlgebraicGeometry.Scheme.IdealSheafData.one_eq_top)) ≪≫
        negativeTwistTopIsoUnit
  succIso n := idealTensorMulIso (D ^ n) D inferInstance ≪≫
    eqToIso (congrArg negativeTwist (pow_succ D n).symm)

/-- The generator of `Stacks.Divisors.negativeTwistPowerSystem D` is `negativeTwist D`. -/
@[simp]
public theorem negativeTwistPowerSystem_gen (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    (negativeTwistPowerSystem D).gen = negativeTwist D := rfl

/-- The `n`-th piece of `Stacks.Divisors.negativeTwistPowerSystem D` is
`negativeTwist (D ^ n)`. -/
@[simp]
public theorem negativeTwistPowerSystem_obj (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (n : ℕ) : (negativeTwistPowerSystem D).obj n = negativeTwist (D ^ n) := rfl

/-- The successor comparison of `Stacks.Divisors.negativeTwistPowerSystem D` in degree `n` is
`Stacks.Divisors.idealTensorMulIso (D ^ n) D` followed by the transport along
`D ^ n * D = D ^ (n + 1)`. -/
public theorem negativeTwistPowerSystem_succIso (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (n : ℕ) :
    (negativeTwistPowerSystem D).succIso n = idealTensorMulIso (D ^ n) D inferInstance ≪≫
      eqToIso (congrArg negativeTwist (pow_succ D n).symm) := rfl

end Stacks.Divisors

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The twists of the projective line, as a system of tensor powers.** The `n`-th piece is
`𝒪(n)`, the generator is `𝒪(1)`, the zeroth-power identification is
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit` and the successor
comparison is Equation 01MO at `(n, 1)`, an isomorphism by Tag 01MT because `k[T₀, T₁]` is
generated in degree one. -/
public def projectiveLineTwistPowerSystem (k : Type u) [Field k] :
    PowerSystem (SheafOfModules.{u}
      (structureSheafRing (projectiveLineProj k).toRingedSpace)) where
  gen := ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1
  obj n := ProjectiveSpectrum.Proj.twistingSheaf
    (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n : ℤ)
  objZeroIso := Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
    (MvPolynomial.homogeneousSubmodule (Fin 2) k)
  succIso n := Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (Stacks.PicardUFD.degreeOneCover k 1)
      (n : ℤ) 1 ≪≫
    eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin 2) k))
      (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring))

/-- The generator of `AlgebraicGeometry.projectiveLineTwistPowerSystem k` is the twisting sheaf
`𝒪(1)`. -/
@[simp]
public theorem projectiveLineTwistPowerSystem_gen (k : Type u) [Field k] :
    (projectiveLineTwistPowerSystem k).gen =
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1 := rfl

/-- The `n`-th piece of `AlgebraicGeometry.projectiveLineTwistPowerSystem k` is the twisting
sheaf `𝒪(n)`. -/
@[simp]
public theorem projectiveLineTwistPowerSystem_obj (k : Type u) [Field k] (n : ℕ) :
    (projectiveLineTwistPowerSystem k).obj n =
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n : ℤ) := rfl

/-- The successor comparison of `AlgebraicGeometry.projectiveLineTwistPowerSystem k` in degree
`n` is the multiplication `𝒪(n) ⊗ 𝒪(1) ≅ 𝒪(n + 1)` of
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso`, followed by the
transport along `(n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)`. -/
public theorem projectiveLineTwistPowerSystem_succIso (k : Type u) [Field k] (n : ℕ) :
    (projectiveLineTwistPowerSystem k).succIso n =
      Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (Stacks.PicardUFD.degreeOneCover k 1)
          (n : ℤ) 1 ≪≫
        eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k))
          (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)) := rfl

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  (e : projectiveLineProj k ≅ D.subscheme) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **The ideal sheaves of the powers of `D`, restricted to `E` and read on `𝐏¹_k`, as a system
of tensor powers.** This is `Stacks.Divisors.negativeTwistPowerSystem` carried along the inclusion
`E ↪ X` and then along the presentation `e : 𝐏¹_k ≅ E`, by
`Stacks.PullbackSheafTensor.pullbackPowerSystem`; its `d`-th piece is
`e^*(𝒪_X(-dE)|_E)`. -/
public def curvePowerSystem :
    PowerSystem (SheafOfModules.{u}
      (structureSheafRing (projectiveLineProj k).toRingedSpace)) :=
  Stacks.PullbackSheafTensor.pullbackPowerSystem e.hom.toLRSHom.toShHom
    (Stacks.PullbackSheafTensor.pullbackPowerSystem D.subschemeι.toLRSHom.toShHom
      (Stacks.Divisors.negativeTwistPowerSystem D))

/-- The `d`-th piece of `curvePowerSystem D k e` is `e^*(𝒪_X(-dE)|_E)`. -/
@[simp]
public theorem curvePowerSystem_obj (d : ℕ) :
    (curvePowerSystem D k e).obj d =
      (Stacks.RingedSpace.pullbackFunctor e.hom.toLRSHom.toShHom).obj
        ((Stacks.RingedSpace.pullbackFunctor D.subschemeι.toLRSHom.toShHom).obj
          (Stacks.Divisors.negativeTwist (D ^ d))) := rfl

/-- The generator of `curvePowerSystem D k e` is `e^*(𝒪_X(-E)|_E)`. -/
@[simp]
public theorem curvePowerSystem_gen :
    (curvePowerSystem D k e).gen =
      (Stacks.RingedSpace.pullbackFunctor e.hom.toLRSHom.toShHom).obj
        ((Stacks.RingedSpace.pullbackFunctor D.subschemeι.toLRSHom.toShHom).obj
          (Stacks.Divisors.negativeTwist D)) := rfl

namespace IsExceptionalCurveOfFirstKind

variable {D k e}

/-- **The isomorphism `e^*(𝒪_X(-E)|_E) ≅ 𝒪_{𝐏¹_k}(1)` of the generators**, a choice of an
isomorphism given by the defining hypothesis of an exceptional curve of the first kind, dualized
(`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_iso_twistingSheaf`). -/
public def curveTwistGenIso (hE : IsExceptionalCurveOfFirstKind D k e) :
    (curvePowerSystem D k e).gen ≅ (projectiveLineTwistPowerSystem k).gen :=
  hE.nonempty_pullback_negativeTwist_iso_twistingSheaf.some

/-- **The coherent family `e^*(𝒪_X(-dE)|_E) ≅ 𝒪_{𝐏¹_k}(d)`**: the comparison of
`curvePowerSystem D k e` with `AlgebraicGeometry.projectiveLineTwistPowerSystem k` along
`curveTwistGenIso`. -/
public def curveTwistIso (hE : IsExceptionalCurveOfFirstKind D k e) (d : ℕ) :
    (curvePowerSystem D k e).obj d ≅ (projectiveLineTwistPowerSystem k).obj d :=
  PowerSystem.compare (curvePowerSystem D k e) (projectiveLineTwistPowerSystem k)
    hE.curveTwistGenIso d

/-- The family in degree zero: the two zeroth-power identifications with `𝒪_{𝐏¹_k}`. -/
public theorem curveTwistIso_zero (hE : IsExceptionalCurveOfFirstKind D k e) :
    hE.curveTwistIso 0 = (curvePowerSystem D k e).objZeroIso ≪≫
      (projectiveLineTwistPowerSystem k).objZeroIso.symm :=
  PowerSystem.compare_zero _ _ _

/-- **The family in a successor degree**: one more copy of the isomorphism of the generators,
carried across the successor comparisons of the two systems. -/
public theorem curveTwistIso_succ (hE : IsExceptionalCurveOfFirstKind D k e) (d : ℕ) :
    hE.curveTwistIso (d + 1) =
      ((curvePowerSystem D k e).succIso d).symm ≪≫
        tensorIso (hE.curveTwistIso d) hE.curveTwistGenIso ≪≫
          (projectiveLineTwistPowerSystem k).succIso d :=
  PowerSystem.compare_succ _ _ _ d

/-- **The cross-degree compatibility of the family, as an equality of morphisms.**

Multiplying in degrees `p` and `q` on `𝐏¹_k` and then comparing is comparing in each degree and
then multiplying: the family is a map of graded objects for the two multiplications
`Stacks.Monoidal.PowerSystem.mulIso` assembled from the canonical successor comparisons. -/
public theorem curveTwistIso_mul (hE : IsExceptionalCurveOfFirstKind D k e) (p q : ℕ) :
    ((hE.curveTwistIso p).hom ⊗ₘ (hE.curveTwistIso q).hom) ≫
        ((projectiveLineTwistPowerSystem k).mulIso p q).hom =
      ((curvePowerSystem D k e).mulIso p q).hom ≫ (hE.curveTwistIso (p + q)).hom :=
  PowerSystem.compare_mul (curvePowerSystem D k e) (projectiveLineTwistPowerSystem k)
    hE.curveTwistGenIso p q

/-- **The multiplications of the two systems are associative**, as equalities of morphisms out
of a twice-iterated tensor product. -/
public theorem curvePowerSystem_mulIso_assoc (p q r : ℕ) :
    (((curvePowerSystem D k e).mulIso p q).hom ▷ (curvePowerSystem D k e).obj r) ≫
        ((curvePowerSystem D k e).mulIso (p + q) r).hom =
      (α_ _ _ _).hom ≫ ((curvePowerSystem D k e).obj p ◁
          ((curvePowerSystem D k e).mulIso q r).hom) ≫
        ((curvePowerSystem D k e).mulIso p (q + r)).hom ≫
          eqToHom (congrArg (curvePowerSystem D k e).obj (Nat.add_assoc p q r).symm) :=
  PowerSystem.mulIso_assoc _ p q r

end IsExceptionalCurveOfFirstKind

end Scheme.IdealSheafData

end AlgebraicGeometry

end
