module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Twist

/-!
# Twisting twice on `ℙⁿ_T` is twisting by the sum

For a scheme `T`, integers `a, b` and a module `ℱ` on `ℙⁿ_T`, the iterated twist `(ℱ(a))(b)` is
isomorphic to `ℱ(a + b)`, and `ℱ(0)` is isomorphic to `ℱ`. In particular `(ℱ(m))(-m) ≅ ℱ`, so
properties stable under twisting are reflected by it.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.twistTwistIso T a b ℱ`: `(ℱ(a))(b) ≅ ℱ(a + b)`.
* `AlgebraicGeometry.ProjectiveQuot.twistZeroIso T ℱ`: `ℱ(0) ≅ ℱ`.
* `AlgebraicGeometry.ProjectiveQuot.twistNegTwistIso T m ℱ`: `(ℱ(m))(-m) ≅ ℱ`.

## Implementation notes

The twist `ℱ(d)` is the tensor product `Stacks.RelativeVeryAmple.tensorModules` of `ℱ` with the
pulled-back twisting sheaf `𝒪(d)` (definitionally). The regrouping
`(ℱ ⊗ 𝒪(a)) ⊗ 𝒪(b) ≅ ℱ ⊗ (𝒪(a) ⊗ 𝒪(b))` is the associator of
`Stacks.SheafInternalHom.schemeMonoidalCategory`, reached across
`Stacks.AmplePullbackPart1.tensorIsoTensorModules`, and `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` is
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso`, valid in all integer degrees.
This is the construction of `Stacks.ProjectiveSpace.projectiveTwistAddIso`, carried out over an
arbitrary base. No `@[stacks]` attribute: these are bookkeeping isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace AlgebraicGeometry.ProjectiveQuot

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

variable {n : ℕ}

/-- **`(ℱ(a))(b) ≅ ℱ(a + b)` on `ℙⁿ_T`**, for every base scheme `T` and all integers `a, b`. -/
def twistTwistIso (T : Scheme.{u}) (a b : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    twist b (twist a F) ≅ twist (a + b) F :=
  (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n T)
        (twist a F) (twistOver n T b)).symm ≪≫
    ((Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n T) F
        (twistOver n T a)).symm ⊗ᵢ Iso.refl (twistOver n T b)) ≪≫
    α_ F (twistOver n T a) (twistOver n T b) ≪≫
    whiskerLeftIso F
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n T)
          (twistOver n T a) (twistOver n T b) ≪≫
        twistOverMulIso n T a b) ≪≫
    Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n T) F
      (twistOver n T (a + b))

/-- **`ℱ(0) ≅ ℱ` on `ℙⁿ_T`**, for every base scheme `T`: `𝒪(0)` is the structure sheaf
(`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit`) and the structure sheaf is the
tensor unit (`Stacks.Ample.unitModuleIsoTensorUnit`). -/
def twistZeroIso (T : Scheme.{u}) (F : (projectiveSpaceOver n T).Modules) :
    twist 0 F ≅ F :=
  (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n T) F
        (twistOver n T 0)).symm ≪≫
    whiskerLeftIso F (twistZeroIsoUnit n T ≪≫
      (Stacks.Ample.unitModuleIsoTensorUnit (projectiveSpaceOver n T) :
        _ ≅ 𝟙_ (projectiveSpaceOver n T).Modules)) ≪≫ ρ_ F

/-- **`(ℱ(m))(-m) ≅ ℱ` on `ℙⁿ_T`**: twisting by `-m` undoes twisting by `m`. -/
def twistNegTwistIso (T : Scheme.{u}) (m : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    twist (-m) (twist m F) ≅ F :=
  twistTwistIso T m (-m) F ≪≫ eqToIso (congrArg (fun d => twist d F) (add_neg_cancel m)) ≪≫
    twistZeroIso T F

/-- **`(ℱ(-m))(m) ≅ ℱ` on `ℙⁿ_T`**: twisting by `m` undoes twisting by `-m`. -/
def twistTwistNegIso (T : Scheme.{u}) (m : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    twist m (twist (-m) F) ≅ F :=
  twistTwistIso T (-m) m F ≪≫ eqToIso (congrArg (fun d => twist d F) (neg_add_cancel m)) ≪≫
    twistZeroIso T F

end AlgebraicGeometry.ProjectiveQuot

end
