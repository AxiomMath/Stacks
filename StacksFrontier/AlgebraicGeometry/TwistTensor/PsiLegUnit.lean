module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiPullbackLeg

/-!
# The adjoint transpose of the homogeneous-section map preserves the unit

For a twist datum `D` over the relative `Proj` of `𝒜` with structure morphism `π`, the adjoint
transpose `π^*𝒜_0 ⟶ 𝒪(0)` of the homogeneous-section map carries the image of the algebra unit over
an open `U` of the base to the unit of the glued graded algebra over `π⁻¹U`.

## Main results

* `RelativeProjTwists.TwistData.psiTransposeNat_zero_unit`: the adjoint transpose of the
  homogeneous-section map carries the algebra unit to the glued algebra's unit, on sections over
  the inverse image of an open of the base.
* `RelativeProjTwists.TwistData.psiTranspose_zero_unit`: the same for the integer-indexed
  `psiTranspose`, in degree zero.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

namespace TwistData

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A)

/-! ### The transpose carries the unit to the unit -/

/-- The adjoint transpose of the homogeneous-section map carries the algebra unit to the glued
algebra's unit: on the inverse image of an open `U` of the base, the transpose `π^*𝒜_0 ⟶ 𝒪(0)`
sends the image under the adjunction's unit of the algebra unit over `U` to the unit of the glued
graded algebra over `π⁻¹U`. -/
public theorem psiTransposeNat_zero_unit (U : S.Opens) :
    (D.psiTransposeNat 0).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
          (A.piece ((0 : ℕ) : ℤ))).val.app (op U) (A.one U))
      = D.algebra.one.eval (op ((relativeProj A).toBase ⁻¹ᵁ U)) :=
  (D.psi_val_app 0 U (A.one U)).symm.trans (D.ψ_one U)

/-- The integer-indexed transpose `psiTranspose` carries the algebra unit to the glued algebra's
unit in degree zero. -/
public theorem psiTranspose_zero_unit (U : S.Opens) :
    (D.psiTranspose ((0 : ℕ) : ℤ)).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
          (A.piece ((0 : ℕ) : ℤ))).val.app (op U) (A.one U))
      = D.algebra.one.eval (op ((relativeProj A).toBase ⁻¹ᵁ U)) :=
  D.psiTransposeNat_zero_unit U

end TwistData

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
