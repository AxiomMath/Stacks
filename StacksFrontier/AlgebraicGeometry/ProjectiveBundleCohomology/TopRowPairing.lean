module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.LocalPairing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.SymPowerLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocallyStrictlyPerfectGradedDual
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DirectImageDelta

/-!
# The top row of the higher direct images of the twists on a projective bundle

For `E` finite locally free of constant rank `n + 1` on `S`, `n ≥ 1`, and `d ≤ -n - 2`,
`k = -n - 1 - d`, the multiplication pairing identifies

`Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^k(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section General

variable {X : Scheme.{u}}

/-- `SheafHom(A, L) ≅ L ⊗ A^∨` for `A` finite locally free. -/
def sheafHomIsoTensorDual (A L : X.Modules)
    [hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] :
    Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace A L ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A) :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (R := structureSheafRing X.toRingedSpace) A := hA
  haveI := Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_localSummand X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) A L
    (Stacks.SheafOfModules.OnSpace.isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand
      X.toRingedSpace A
      (Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
        X.toRingedSpace A))
  (asIso (Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) A L)).symm

/-- `SheafHom(G ⊗ N, 𝒪) ≅ N^∨ ⊗ G^∨` for `G` finite locally free. -/
def dualTensorIso (G N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf G) :=
  Stacks.SheafOfModules.internalHomTensorIso X.toRingedSpace G N _ ≪≫
    sheafHomIsoTensorDual G (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)

end General

section Bundle

open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualFunctor)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {n : ℕ} (hn : 1 ≤ n)
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))

omit [E.IsQuasicoherent] in
include hfree in
/-- For `E` finite locally free of rank `n + 1`, the degree `k` piece `Sym^k(E)` of the
symmetric algebra of `E` is finite locally free. -/
theorem isFiniteLocallyFree_piece (k : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)) :=
  have := isFiniteLocallyFree_of_rank E hfree
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_symmetricAlgebra_piece E k

end Bundle


section ProjectionFormula

open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualFunctor)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))

include hfree in
/-- The projection formula for the twisted dual of `Sym^k(E)`. -/
def higherDirectImageTensorDualIso (k : ℕ) (L : (bundle E hqc).Modules) :
    ((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      (n : ℤ)).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj L).obj
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
          (n : ℤ)).obj L)).obj
        (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))) :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _
      (isFiniteLocallyFree_piece E hqc hfree k)
  Stacks.ProjectionFormula.higherDirectImageProjectionFormulaFiniteLocallyFreeIso _ _ L (n : ℤ)

include hfree in
/-- The projection formula for the twisted dual of `Sym^k(E)`, in the indexing of
`Functor.rightDerived`. -/
def higherDirectImageTensorDualIsoNat (k : ℕ) (L : (bundle E hqc).Modules) :
    ((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerived
      n).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj L).obj
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerived
          n).obj L)).obj
        (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))) :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _
      (isFiniteLocallyFree_piece E hqc hfree k)
  projectionFormulaDeltaApp (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase
    (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))) L n

end ProjectionFormula

section Main

open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualFunctor)

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {n : ℕ} (hn : 1 ≤ n)
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))

include hn hfree in
/-- **`Rⁿ π_* SheafHom(π^* Sym^k(E), 𝒪(-n-1)) ≅ SheafHom(Sym^k(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`**, by the
projection formula and `Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨`. -/
def higherDirectImageSheafHomIso (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -(n : ℤ) - 1) :
    ((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      (n : ℤ)).obj (Stacks.SheafOfModules.sheafHomSpace (bundle E hqc).toRingedSpace
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
        (D.algebra.piece (-(n : ℤ) - 1))) ≅
      topRowTarget E hqc n d :=
  haveI hG := isFiniteLocallyFree_piece E hqc hfree k
  ((Scheme.Modules.pushforward
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      (n : ℤ)).mapIso
      (sheafHomIsoTensorDual _ _ ≪≫ Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl _)
        (Stacks.FundamentalGroup.pullbackDualSheafIso _ _ hG).symm) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso _ n).app _).symm ≪≫
    higherDirectImageTensorDualIsoNat E hqc hfree k _ ≪≫
    Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
      (((bundlePushforward E hqc).rightDerived n).mapIso
          (eqToIso (congrArg D.algebra.piece (by push_cast; ring))) ≪≫
        topTwistIsoDualDet E hqc D hn hfree) (Iso.refl _) ≪≫
    (dualTensorIso _ _).symm ≪≫
    ((dualFunctor S).mapIso ((Stacks.ProjectionFormula.tensorRightInvertible S
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
        (eqToIso (congrArg (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece
          (show (k : ℤ) = -(n : ℤ) - 1 - d by omega)))).op).symm

include hn hfree in
/-- **The row `q = n`**: `Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` for every
integer `d`. For `d ≤ -n - 1` it is the multiplication pairing
`𝒪(d) ⟶ SheafHom(π^* Sym^{-n-1-d}(E), 𝒪(-n-1))` on `Rⁿ π_*` followed by
`higherDirectImageSheafHomIso`; for `d ≥ -n` both sides vanish. -/
def topRowIso (d : ℤ) :
    ((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).obj (D.algebra.piece d) ≅
      topRowTarget E hqc n d :=
  if h : d ≤ -(n : ℤ) - 1 then
    haveI := isIso_rightDerivedPlus_twistPairingCurry E hqc D hn hfree (-(n : ℤ) - 1 - d).toNat
      d (-(n : ℤ) - 1) (by omega) (by omega)
    asIso (((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).map
        (twistPairingCurry E hqc D (-(n : ℤ) - 1 - d).toNat d (-(n : ℤ) - 1) (by omega))) ≪≫
      higherDirectImageSheafHomIso E hqc D hn hfree _ d (by omega)
  else
    (isZero_topRow_of_le E hqc D hn hfree (d := d) (by omega)).1.iso
      (isZero_topRow_of_le E hqc D hn hfree (d := d) (by omega)).2

end Main

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology
