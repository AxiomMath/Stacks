module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules on a scheme form an abelian category

For a scheme `X`, the full subcategory of `𝒪_X`-modules cut out by quasi-coherence is an
abelian subcategory of all `𝒪_X`-modules: it contains a zero object and is closed under
kernels, cokernels and finite products.

## Main results

* `AlgebraicGeometry.isQuasicoherent_binaryProduct`: a binary product of quasi-coherent modules is
  quasi-coherent.
* `AlgebraicGeometry.quasicoherentModules_abelian`: the category of quasi-coherent modules on a
  scheme is abelian.
* `AlgebraicGeometry.quasicoherentModules_abelian_toPreadditive`: its additive structure is the
  one the full subcategory inherits.

## Implementation notes

`QCoh(𝒪_X)` is the full subcategory cut out by Mathlib's object property
`SheafOfModules.isQuasicoherent X.ringCatSheaf`.

## References

* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry Scheme.Modules

namespace AlgebraicGeometry

/-- A binary product of quasi-coherent modules is quasi-coherent. -/
lemma isQuasicoherent_binaryProduct (X : Scheme.{u})
    {M N : SheafOfModules X.ringCatSheaf} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨯ N).IsQuasicoherent := by
  let P : ObjectProperty (SheafOfModules X.ringCatSheaf) :=
    SheafOfModules.isQuasicoherent X.ringCatSheaf
  have : P.IsClosedUnderColimitsOfShape (Discrete WalkingPair) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift.{u, 0} (α := WalkingPair)))
  have : HasBinaryBiproduct M N := HasBinaryBiproduct.of_hasBinaryCoproduct M N
  exact P.prop_of_iso (biprod.isoProd M N)
    (P.prop_of_iso (biprod.isoCoprod M N).symm (P.prop_coprod M N ‹_› ‹_›))

/-- The category of quasi-coherent modules on a scheme is abelian. -/
@[stacks 077P "grothendieck_qcoh"]
noncomputable instance quasicoherentModules_abelian (X : Scheme.{u}) :
    Abelian (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := by
  let P : ObjectProperty (SheafOfModules X.ringCatSheaf) :=
    SheafOfModules.isQuasicoherent X.ringCatSheaf
  let U : SheafOfModules X.ringCatSheaf := SheafOfModules.unit X.ringCatSheaf
  have hU : U.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have : P.ContainsZero :=
    ⟨⟨kernel (𝟙 U), isZero_kernel_of_mono (𝟙 U),
      @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel X U U (𝟙 U) hU hU⟩⟩
  have : P.IsClosedUnderKernels := {
    kernels_le := by
      rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
      exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
        (@Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel X _ _ f hX hY)
  }
  have : P.IsClosedUnderCokernels := {
    cokernels_le := by
      rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
      exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
        (@Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel X _ _ f hX hY)
  }
  have : P.IsClosedUnderBinaryProducts := by
    refine ⟨?_⟩
    rintro Z ⟨p⟩
    let A := p.diag.obj ⟨WalkingPair.left⟩
    let B := p.diag.obj ⟨WalkingPair.right⟩
    have hprod : P (A ⨯ B) := @isQuasicoherent_binaryProduct X A B
      (p.prop_diag_obj ⟨WalkingPair.left⟩) (p.prop_diag_obj ⟨WalkingPair.right⟩)
    have e : Z ≅ A ⨯ B :=
      p.isLimit.conePointUniqueUpToIso (limit.isLimit p.diag) ≪≫
        HasLimit.isoOfNatIso (Limits.diagramIsoPair p.diag)
    exact P.prop_of_iso e.symm hprod
  have : P.IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  infer_instance

/-- The abelian structure uses the usual addition of morphisms of sheaves of modules. -/
@[simp]
theorem quasicoherentModules_abelian_toPreadditive (X : Scheme.{u}) :
    (quasicoherentModules_abelian X).toPreadditive =
      Preadditive.fullSubcategory (SheafOfModules.isQuasicoherent X.ringCatSheaf) := rfl

end AlgebraicGeometry

end
