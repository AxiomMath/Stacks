module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.KoszulCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.PieceZero

/-!
# The top higher direct image of `𝒪(-n-1)` on a projective bundle

Let `E` be finite locally free of constant rank `n + 1 ≥ 2` on a scheme `S` and `π : 𝐏(E) ⟶ S`
its projective bundle. Dimension shifting along the Koszul filtration of the tautological
surjection gives `π_* 𝒪 ≅ Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E`, and so, `⋀ⁿ⁺¹ E` being invertible,

`Rⁿ π_* 𝒪(-n-1) ≅ SheafHom(Sym⁰(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isoDualSheaf_of_tensor_iso_unit`: an
  object whose tensor product with an invertible module is the structure sheaf is the dual of
  that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open MonoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Dual

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory

variable {X : Scheme.{u}}

/-- **An object whose tensor product with an invertible module is the structure sheaf is the
dual of that module**: `R ⊗ N ≅ 𝒪` gives `R ≅ SheafHom(N, 𝒪)`. -/
public def isoDualSheaf_of_tensor_iso_unit (N R : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : (Stacks.ProjectionFormula.tensorRightInvertible X N).obj R ≅ SheafOfModules.unit _) :
    R ≅ Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 N :=
  haveI := Stacks.SheafOfModules.Invertible.isIso_evaluation X.presheaf X.ringCatSheaf.2 N
  (Stacks.ProjectionFormula.tensorRightInvertible X N).preimageIso
    (e ≪≫ (asIso (Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.2 N)).symm)

end Dual

section Trace

open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))

/-- `⋀⁰ K ⊗ 𝒪(0) ≅ 𝒪(0)`. -/
public def koszulTermZeroIso :
    koszulTerm E hqc D 0 ≅ D.algebra.piece ((0 : ℕ) : ℤ) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩)).mapIso
      (Iso.prod (kernelAlgebras E hqc D).exteriorPieceZeroIsoUnit
        (eqToIso (congrArg D.algebra.piece (by simp)))) ≪≫
    Stacks.SheafOfModules.tensorSheafLeftUnitor (bundle E hqc).sheaf.obj
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (bundle E hqc))
        (bundle E hqc).sheaf).property (D.algebra.piece ((0 : ℕ) : ℤ))

variable {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
include hn hfree

/-- `π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ 𝒪_S`. -/
public def koszulBottomIso :
    ((bundlePushforward E hqc).rightDerived 0).obj (koszulTerm E hqc D 0) ≅
      SheafOfModules.unit S.ringCatSheaf :=
  ((bundlePushforward E hqc).rightDerived 0).mapIso (koszulTermZeroIso E hqc D) ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqc) 0).app _ ≪≫
    zeroIso E hqc D (n := n) (by omega) hfree 0 ≪≫ Stacks.SymGraded.pieceZeroIso E

/-- **`Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E ≅ 𝒪_S`**, the trace of the Koszul filtration. -/
public def topTraceIso :
    (Stacks.ProjectionFormula.tensorRightInvertible S
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
        (((bundlePushforward E hqc).rightDerived n).obj (negTwist E hqc D (n + 1))) ≅
      SheafOfModules.unit S.ringCatSheaf :=
  (koszulTopIso E hqc D hn hfree).symm ≪≫ koszulBottomIso E hqc D hn hfree

omit [E.IsQuasicoherent] hn in
/-- The determinant `⋀ⁿ⁺¹ E` is invertible. -/
public theorem isInvertible_det :
    Stacks.SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) :=
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (n + 1)).mp hfree
  Scheme.Modules.isInvertible_exteriorPower_self E (n + 1)

/-- **`Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨`**, in the indexing by injective resolutions. -/
public def topTwistIsoDualDet :
    ((bundlePushforward E hqc).rightDerived n).obj (negTwist E hqc D (n + 1)) ≅
      Stacks.SheafOfModules.dualSheaf S.presheaf S.ringCatSheaf.2
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) :=
  haveI := isInvertible_det E hfree
  isoDualSheaf_of_tensor_iso_unit _ _ (topTraceIso E hqc D hn hfree)

end Trace

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
