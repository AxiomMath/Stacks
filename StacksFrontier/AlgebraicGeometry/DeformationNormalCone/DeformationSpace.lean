module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ExtendedRees

/-!
# The deformation to the normal cone

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, cutting out `Z ⊆ X`. The
*deformation space* of `Z ⊆ X` is the relative spectrum over `X` of the extended Rees algebra
`𝒪_X[t⁻¹, ℐt] = ⨁_{k ∈ ℤ} ℐ^{max(k,0)}`:

  `D(ℐ) = Spec_X(⨁_{k ∈ ℤ} ℐ^{max(k,0)}) ⟶ X`.

The global section `t⁻¹`, the section `1` of the degree `-1` piece, is the parameter of the
family: away from `t⁻¹ = 0` it is `X × 𝔾_m`, and the fibre `t⁻¹ = 0` is the normal cone `C_ZX`.

## Main definitions

* `Stacks.Deformation.extReesAlgebraSheaf`: the extended Rees algebra as a quasi-coherent sheaf
  of commutative `𝒪_X`-algebras.
* `Stacks.Deformation.deformationSpace` and `Stacks.Deformation.deformationSpaceToBase`: the
  deformation space and its projection to `X`.

## Main results

* `Stacks.Deformation.isQuasicoherent_extReesAlgebraSheaf`: the extended Rees algebra is
  quasi-coherent. Its underlying module is the coproduct of the homogeneous pieces over all of
  `ℤ`, each of which is quasi-coherent.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
    (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- **`Stacks.RelativeSpec.gradedAlgebraSheaf` of a `ℤ`-graded algebra is quasi-coherent as soon
as its homogeneous pieces are**: its underlying module is the sheafification of the direct sum of
all the pieces, which is their coproduct, and a coproduct of quasi-coherent modules on a scheme is
quasi-coherent. -/
theorem isQuasicoherent_gradedAlgebraSheaf_of_pieces
    (hqc : ∀ n : ℤ, (A.piece n).IsQuasicoherent) :
    AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Stacks.sheafifyDirectSumIso (fun n : ℤ => A.piece n)).symm ≪≫
      gradedDirectSumIsoUnderlyingModule X A hc)
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
      (Discrete.functor fun n : ℤ => A.piece n) fun n => hqc n.as)

end Stacks.RelativeSpec

namespace Stacks.Deformation

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The extended Rees algebra `𝒪_X[t⁻¹, ℐt]`, as a sheaf of commutative `𝒪_X`-algebras.** -/
def extReesAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  Stacks.RelativeSpec.gradedAlgebraSheaf X (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I)

/-- The extended Rees algebra is quasi-coherent. -/
instance isQuasicoherent_extReesAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (extReesAlgebraSheaf I) :=
  Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf_of_pieces X _ _
    (extReesPiece_isQuasicoherent I)

/-- **The deformation space `D(ℐ) = Spec_X(𝒪_X[t⁻¹, ℐt])`** of the closed subscheme cut out by
`ℐ`. -/
def deformationSpace : Scheme.{u} :=
  Stacks.AffineAlgebraEquivalence.relativeSpec (extReesAlgebraSheaf I)

/-- The projection `D(ℐ) ⟶ X` of the deformation space. -/
def deformationSpaceToBase : deformationSpace I ⟶ X :=
  Stacks.AffineAlgebraEquivalence.relativeSpecToBase (extReesAlgebraSheaf I)

end Stacks.Deformation

end
