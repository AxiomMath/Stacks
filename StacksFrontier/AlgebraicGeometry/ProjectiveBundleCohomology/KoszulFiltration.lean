module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerWedgeQuotientIso
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul filtration on a projective bundle

Let `π : 𝐏(E) ⟶ S` be the projective bundle of a quasi-coherent `𝒪_S`-module `E`, with twists
given by a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, and let
`0 → K → π^* E → 𝒪(1) → 0` be the kernel sequence of the tautological surjection. For every
`p` the exterior powers fit into the short exact sequence

`0 → ⋀ᵖ⁺¹ K → ⋀ᵖ⁺¹ π^* E → ⋀ᵖ K ⊗ 𝒪(1) → 0`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.tautologicalKernel`: `K`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.koszulQuotient`: the third arrow.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.shortExact_koszul`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.SheafOfModules.TopWedge Stacks.SheafOfModules.WedgeQuotient

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))

/-- The projective bundle `𝐏(E)`. -/
public abbrev bundle : Scheme.{u} :=
  (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme

/-- The pullback `π^* E` of `E` to the projective bundle. -/
public abbrev bundlePullback : (bundle E hqc).Modules :=
  (Scheme.Modules.pullback
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj E

/-- **The kernel `K` of the tautological surjection `π^* E ⟶ 𝒪(1)`.** -/
@[sga "5 VII 8.4.1", sga "6 VII 1.8" "partial"]
public abbrev tautologicalKernel : (bundle E hqc).Modules :=
  kernel (tautologicalMap E hqc D)

/-- The exterior algebra of `K`. -/
public abbrev kernelAlgebras :=
  _root_.SheafOfModules.algebras (Opens.grothendieckTopology (bundle E hqc))
    (Osharp := (bundle E hqc).sheaf) (tautologicalKernel E hqc D)

/-- The exterior algebra of `π^* E`. -/
public abbrev pullbackAlgebras :=
  _root_.SheafOfModules.algebras (Opens.grothendieckTopology (bundle E hqc))
    (Osharp := (bundle E hqc).sheaf) (bundlePullback E hqc)

omit [E.IsQuasicoherent] in
/-- The kernel sequence of the tautological surjection is exact. -/
public theorem exact_tautological :
    (ShortComplex.mk (kernel.ι (tautologicalMap E hqc D)) (tautologicalMap E hqc D)
      (kernel.condition _)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- The stalks of `𝒪(1)` on the projective bundle are free of rank one. -/
public theorem nonempty_basis_stalk_twistOne (x : bundle E hqc) :
    Nonempty (Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk (bundle E hqc).presheaf x)
      ↑(TopCat.Presheaf.stalk (D.algebra.piece ((1 : ℕ) : ℤ)).val.presheaf x)) :=
  nonempty_basis_stalk_piece D (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra
    E hqc) ((1 : ℕ) : ℤ) x

/-- The kernel sequence `0 → K → π^* E → 𝒪(1) → 0` of the tautological surjection. -/
@[sga "5 VII 8.4.1" "partial", sga "5 VII 9.1" "Construction (9.1.0)"]
public def tautologicalSequence : ShortComplex (bundle E hqc).Modules :=
  ShortComplex.mk (kernel.ι (tautologicalMap E hqc D)) (tautologicalMap E hqc D)
    (kernel.condition _)

omit [E.IsQuasicoherent] in
/-- The inclusion `K ⟶ π^* E` of the kernel is a monomorphism. -/
public theorem mono_tautologicalSequence_f : Mono (tautologicalSequence E hqc D).f :=
  Limits.mono_of_isLimit_fork (limit.isLimit _)

/-- **The comparison `⋀ᵖ K ⊗ 𝒪(1) ≅ ⋀ᵖ⁺¹ π^* E / ⋀ᵖ⁺¹ K`.** -/
public def koszulQuotientIso (p : ℕ) :=
  @wedgeQuotientIso _ _ _ _ _ (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
    (tautologicalSequence E hqc D).f (tautologicalSequence E hqc D).g
    (tautologicalSequence E hqc D).zero (exact_tautological E hqc D)
    (mono_tautologicalSequence_f E hqc D) (epi_tautologicalMap E hqc D)
    (fun x => nonempty_basis_stalk_twistOne E hqc D x) p

/-- **The Koszul filtration of the projective bundle**:
`0 → ⋀ᵖ⁺¹ K → ⋀ᵖ⁺¹ π^* E → ⋀ᵖ K ⊗ 𝒪(1) → 0`. -/
public def koszulSequence (p : ℕ) : ShortComplex (bundle E hqc).Modules :=
  ShortComplex.mk (extPowMap (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
      (tautologicalSequence E hqc D).f (p + 1))
    (cokernel.π (extPowMap (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
      (tautologicalSequence E hqc D).f (p + 1)) ≫ (koszulQuotientIso E hqc D p).inv)
    ((cokernel.condition_assoc _ _).trans zero_comp)

/-- **The Koszul filtration is short exact.** -/
public theorem shortExact_koszul (p : ℕ) : (koszulSequence E hqc D p).ShortExact :=
  @shortExact_wedgeQuotient _ _ _ _ _ (kernelAlgebras E hqc D) (pullbackAlgebras E hqc)
    (tautologicalSequence E hqc D).f (tautologicalSequence E hqc D).g
    (tautologicalSequence E hqc D).zero (exact_tautological E hqc D)
    (mono_tautologicalSequence_f E hqc D) (epi_tautologicalMap E hqc D)
    (fun x => nonempty_basis_stalk_twistOne E hqc D x) p

section Monoidal

example (F G H : (bundle E hqc).Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj F).obj G)).obj H ≅
    ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj F).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj G).obj H) :=
  Stacks.SheafOfModules.tensorSheafAssociator (bundle E hqc).sheaf.obj
    (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (bundle E hqc))
      (bundle E hqc).sheaf).property F G H

example (F G : (bundle E hqc).Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj F).obj G ≅
    ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj G).obj F :=
  Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap (bundle E hqc).toRingedSpace F G

end Monoidal

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
