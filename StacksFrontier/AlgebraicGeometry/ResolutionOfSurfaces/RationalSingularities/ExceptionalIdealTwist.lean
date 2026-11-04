module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowers
import StacksCore.Tactic.StacksAttribute

/-!
# The powers of the exceptional ideal sheaf are the twists of the blowup

Let `(A, 𝔪)` be a local ring, let `X` be the blowup of `Spec(A)` in `𝔪`, let `ℐ` be the ideal
sheaf of the exceptional divisor and let `𝒪_X(n)` be the `n`-th power of the twisting sheaf.
Part (3) of [Stacks, Tag 02OS] identifies the two in every degree: `ℐⁿ ≅ 𝒪_X(n)`.

`StacksFrontier/AlgebraicGeometry/Blowup/TwistOneExceptionalIdeal.lean` proves the degree-one case
for an arbitrary scheme and an arbitrary quasi-coherent sheaf of ideals, and
`AlgebraicGeometry.BlowUpDualizing.exceptionalIdealModuleIsoTwistSheaf` reads it in this
chapter's spelling. This file raises it to every nonnegative degree.

## Main definitions

* `AlgebraicGeometry.BlowUpDualizing.twistSheafAddIso`, `.twistSheafZeroIso` and
  `.twistSheafCongr`: `𝒪_X(a) ⊗ 𝒪_X(b) ≅ 𝒪_X(a + b)`, `𝒪_X(0) ≅ 𝒪_X` and reindexing, the
  analogues on `X` of the laws `BlowUpDualizing.lean` records on the exceptional curve.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.exceptionalIdealPowIsoTwistSheaf`: **`ℐⁿ ≅ 𝒪_X(n)` for
  every `n ≥ 0`**, part (3) of [Stacks, Tag 02OS] in every nonnegative degree.

## Implementation notes

The induction on `n` is on the *ideal* side, not the twist side. Its step is
`Stacks.Divisors.idealTensorMulIso`, the statement that for an effective Cartier divisor `J` the
multiplication map `ℐ_I ⊗ ℐ_J ⟶ ℐ_{I·J}` is an isomorphism; the exceptional divisor is an
effective Cartier divisor by `Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`, with no
hypothesis on `A`. The base case is `AlgebraicGeometry.idealSheafOfModulesPowZeroIso`, that the
zeroth power of a sheaf of ideals is the structure sheaf.

The alternative route — raise `exceptionalIdealModuleIsoTwistSheaf` to the `n`-th tensor power
and compare with `Stacks.Divisors.negativeTwistTensorPowerIso`, which already says
`ℐ_D^{⊗ n} ≅ ℐ_{nD}` — does not typecheck: that isomorphism is stated for
`Stacks.SheafOfModules.TensorPower.tensorPower`, while this chapter's `tensorPowModule` is built
on `AlgebraicGeometry.SheafOfModules.tensorPow`, and the two tensor powers are distinct
definitions with no comparison in the tree. Going through `idealTensorMulIso` avoids the tensor
*power* entirely: only the tensor *product* `Stacks.RelativeVeryAmple.tensorModules` occurs, and
`Stacks.Divisors.idealTensorProd` is that product on the nose.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]


/-- **`ℐ_E ≅ 𝒪_X(1)`**: the ideal sheaf of the exceptional divisor is the first twist. This is
part (3) of [Stacks, Tag 02OS] (`AlgebraicGeometry.twistOneIsoExceptionalIdealModule`, which
has no hypothesis), read through the identification `twistSheafOneIso` of `𝒪_X(1)` with the
twisting sheaf `AlgebraicGeometry.blowUpTwist` of the blowup. -/
def exceptionalIdealModuleIsoTwistSheaf : exceptionalIdealModule A ≅ twistSheaf A 1 :=
  (twistOneIsoExceptionalIdealModule (centre A)).symm ≪≫ (twistSheafOneIso A).symm

/-- `𝒪_X(a) ⊗ 𝒪_X(b) ≅ 𝒪_X(a + b)`, the addition law for the twists of the blowup. -/
def twistSheafAddIso (a b : ℤ) :
    Stacks.RelativeVeryAmple.tensorModules (blowUpScheme A) (twistSheaf A a) (twistSheaf A b) ≅ twistSheaf A (a + b) :=
  tensorPowModuleAddIso (blowUpScheme A) (twistNegOne A) (-a) (-b) ≪≫
    tensorPowModuleCongr (blowUpScheme A) (twistNegOne A)
      (show -a + -b = -(a + b) by ring)

/-- Reindexing of `𝒪_X(n)` along an equality of degrees. -/
def twistSheafCongr {a b : ℤ} (h : a = b) : twistSheaf A a ≅ twistSheaf A b :=
  tensorPowModuleCongr (blowUpScheme A) (twistNegOne A) (by rw [h])

/-- `𝒪_X(0) ≅ 𝒪_X`. -/
def twistSheafZeroIso : twistSheaf A 0 ≅ unitModule (blowUpScheme A) :=
  tensorPowModuleCongr (blowUpScheme A) (twistNegOne A) (show -(0 : ℤ) = 0 by ring) ≪≫
    tensorPowModuleZeroIso (blowUpScheme A) (twistNegOne A)

/-- **[Stacks, Tag 02OS] part (3) in every nonnegative degree: `ℐⁿ ≅ 𝒪_X(n)`.** The `n`-th power
of the ideal sheaf of the exceptional divisor of the blowup of `Spec(A)` in the maximal ideal is
the `n`-th power of the twisting sheaf.

By induction on `n`. The zeroth power of a sheaf of ideals is the structure sheaf, which is
`𝒪_X(0)`. For the step, the exceptional divisor is an effective Cartier divisor, so
`Stacks.Divisors.idealTensorMulIso` makes `ℐⁿ ⊗ ℐ` the ideal sheaf of `ℐⁿ·ℐ = ℐⁿ⁺¹`; the
inductive hypothesis and the degree-one case `exceptionalIdealModuleIsoTwistSheaf` rewrite the
two factors as `𝒪_X(n)` and `𝒪_X(1)`, and the addition law closes the step.

[Stacks, Tag 02OS] (not registered here: this is not the whole statement of the tag): part (3) in
every nonnegative degree, for the blowup of a local ring in its maximal ideal: the n-th power of
the ideal sheaf of the exceptional divisor is O_X(n)
-/
def exceptionalIdealPowIsoTwistSheaf : (n : ℕ) →
    Stacks.Divisors.idealSheafOfModules (exceptionalIdeal (centre A) ^ n) ≅
      twistSheaf A (n : ℤ)
  | 0 =>
      idealSheafOfModulesPowZeroIso (exceptionalIdeal (centre A)) ≪≫
        (twistSheafZeroIso A).symm ≪≫
        twistSheafCongr A (show (0 : ℤ) = ((0 : ℕ) : ℤ) by push_cast)
  | n + 1 =>
      have hpow : Stacks.Divisors.idealSheafOfModules
            (exceptionalIdeal (centre A) ^ (n + 1)) ≅
          Stacks.Divisors.idealSheafOfModules
            (exceptionalIdeal (centre A) ^ n * exceptionalIdeal (centre A)) :=
        eqToIso (congrArg Stacks.Divisors.idealSheafOfModules
          (pow_succ (exceptionalIdeal (centre A)) n))
      have hmul : Stacks.RelativeVeryAmple.tensorModules (blowUpScheme A)
            (Stacks.Divisors.idealSheafOfModules (exceptionalIdeal (centre A) ^ n))
            (Stacks.Divisors.idealSheafOfModules (exceptionalIdeal (centre A))) ≅
          Stacks.Divisors.idealSheafOfModules
            (exceptionalIdeal (centre A) ^ n * exceptionalIdeal (centre A)) :=
        Stacks.Divisors.idealTensorMulIso (exceptionalIdeal (centre A) ^ n)
          (exceptionalIdeal (centre A)) inferInstance
      have hfac : Stacks.RelativeVeryAmple.tensorModules (blowUpScheme A)
            (Stacks.Divisors.idealSheafOfModules (exceptionalIdeal (centre A) ^ n))
            (Stacks.Divisors.idealSheafOfModules (exceptionalIdeal (centre A))) ≅
          Stacks.RelativeVeryAmple.tensorModules (blowUpScheme A) (twistSheaf A (n : ℤ)) (twistSheaf A 1) :=
        tensorModulesMapIso (blowUpScheme A) (exceptionalIdealPowIsoTwistSheaf n)
          (exceptionalIdealModuleIsoTwistSheaf A)
      hpow ≪≫ hmul.symm ≪≫ hfac ≪≫ twistSheafAddIso A (n : ℤ) 1 ≪≫
        twistSheafCongr A (show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

end AlgebraicGeometry.BlowUpDualizing

end
