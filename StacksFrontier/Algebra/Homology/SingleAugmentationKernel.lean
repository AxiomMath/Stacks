module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The augmentation of a resolution is the kernel of the first differential

Let `K` be a cochain complex concentrated in degrees `≥ 0` and `ι : X[0] ⟶ K` a
quasi-isomorphism. Then the degree-zero component `X ⟶ K⁰` of `ι` is a kernel of
`d⁰ : K⁰ ⟶ K¹` (`CochainComplex.isLimitKernelForkOfSingleQuasiIso`): `X ≅ H⁰(X[0]) ≅ H⁰(K)`, and
`H⁰(K)` is the kernel of `d⁰` since `K⁻¹ = 0`. In particular a morphism into `K⁰` killed by `d⁰`
factors uniquely through `X`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- The degree-zero component of a morphism from a single complex in degree `0` composes to zero
with `d⁰`. -/
lemma singleObjXSelf_inv_f_d (K : CochainComplex C ℤ) (X : C)
    (ι : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X ⟶ K) :
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ ι.f 0) ≫ K.d 0 1 = 0 := by
  rw [Category.assoc, ι.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]

/-- **The augmentation of a resolution in degrees `≥ 0` is the kernel of `d⁰`.** -/
def isLimitKernelForkOfSingleQuasiIso (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] (X : C)
    (ι : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X ⟶ K) [QuasiIso ι] :
    IsLimit (KernelFork.ofι _ (singleObjXSelf_inv_f_d K X ι)) := by
  have hK : K.d (-1) 0 = 0 := (K.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _
  have hS : ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).d (-1) 0 = 0 := by simp
  haveI := K.isIso_homologyπ (-1) 0 (by simp) hK
  haveI := ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).isIso_homologyπ (-1) 0
    (by simp) hS
  haveI : IsIso (HomologicalComplex.cyclesMap ι 0) := by
    have h := HomologicalComplex.homologyπ_naturality ι 0
    have : HomologicalComplex.cyclesMap ι 0 = HomologicalComplex.homologyπ _ 0 ≫
        HomologicalComplex.homologyMap ι 0 ≫ inv (K.homologyπ 0) := by
      rw [reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  let c : X ≅ K.cycles 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 X).symm ≪≫
      asIso (HomologicalComplex.cyclesMap ι 0)
  have hc : c.hom ≫ K.iCycles 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ ι.f 0 := by
    simp [c]
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) ?_
  exact Fork.ext c.symm (by simp [← hc])

end CochainComplex

end
