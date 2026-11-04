module

public import StacksFrontier.AlgebraicGeometry.AffineCover.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingCechComputesDerivedSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The alternating Čech complex of a cover with affine intersections, at quasi-coherent
coefficients

Let `Y` be a scheme, let `V : I → Y.Opens` be a finite open covering of `Y` all of whose finite
intersections are affine, and let `K^•` be an arbitrary complex of quasi-coherent
`𝒪_Y`-modules. Then the comparison map

`Tot(Č_alt^•(V, K^•)) ⟶ RΓ(Y, K^•)`

of Tag 08C1 is an isomorphism in `D(Ab)`.

## Main results

* `Stacks.Cech.isQuasicoherent_homology`: a homology object of a complex of quasi-coherent
  modules on a scheme is quasi-coherent.
* `Stacks.Cech.isIso_alternatingCechToDerivedComparison_of_isAffineOpen`: the comparison map of
  Tag 08C1 is an isomorphism for such a covering and such a complex.

## References

* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Cech

noncomputable section

variable (Y : Scheme.{u})

/-- The cokernel of a morphism of quasi-coherent `𝒪_Y`-modules is quasi-coherent. -/
theorem isQuasicoherent_cokernel_of_isQuasicoherent
    {M N : SheafOfModules.{u} Y.ringCatSheaf} (φ : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (cokernel φ).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_cokernel φ hM hN

/-- The kernel of a morphism of quasi-coherent `𝒪_Y`-modules is quasi-coherent. -/
theorem isQuasicoherent_kernel_of_isQuasicoherent
    {M N : SheafOfModules.{u} Y.ringCatSheaf} (φ : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (kernel φ).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_kernel φ hM hN

/-- A homology object of a complex of quasi-coherent modules is quasi-coherent. -/
theorem isQuasicoherent_homology
    (K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℤ)
    (hK : ∀ q : ℤ, (K.X q).IsQuasicoherent) (q : ℤ) :
    (K.homology q).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (K.sc q).homologyIsoCokernelLift.symm <|
    isQuasicoherent_cokernel_of_isQuasicoherent Y
      (kernel.lift (K.sc q).g (K.sc q).f (K.sc q).zero) (hK _)
      (isQuasicoherent_kernel_of_isQuasicoherent Y (K.sc q).g (hK _) (hK _))

/-- **The alternating Čech complex of a covering with affine intersections computes derived
global sections of a complex of quasi-coherent modules.** Let `Y` be a scheme, let `V` be a
finite open covering of `Y` whose finite intersections are all affine, and let `K^•` be a
complex of quasi-coherent `𝒪_Y`-modules. Then the comparison map
`Tot(Č_alt^•(V, K^•)) ⟶ RΓ(Y, K^•)` of Tag 08C1 is an isomorphism in `D(Ab)`.

This is Tag 08C2 on the basis of affine opens of `Y`, whose three acyclicity hypotheses are
Serre vanishing (Tag 01XB) for the terms, the cokernels of the differentials and the homology
objects of `K^•`, all of which are quasi-coherent. -/
@[ega "III 1.4.2" "special case"]
theorem isIso_alternatingCechToDerivedComparison_of_isAffineOpen
    {I : Type u} [Finite I] (V : I → Y.Opens) (hV : (⊤ : Y.Opens) = iSup V)
    (hVaff : ∀ (p : ℕ) (s : Fin (p + 1) → I), IsAffineOpen (⨅ k, V (s k)))
    (K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℤ)
    (hK : ∀ q : ℤ, (K.X q).IsQuasicoherent) :
    IsIso ((alternatingCechToDerivedComparison _ Y.ringCatSheaf V hV).app K) := by
  have key (M : SheafOfModules.{u} Y.ringCatSheaf) (_ : M.IsQuasicoherent) (W : Y.Opens)
      (hW : W ∈ Y.affineOpens) (p : ℕ) (hp : 0 < p) :
      IsZero (((SheafOfModules.evaluation Y.ringCatSheaf (op W)).rightDerived p).obj M) :=
    Stacks.Cohomology.CechAffineCover.isZero_rightDerived_evaluation_of_isAffineOpen
      Y M W hW p hp
  exact isIso_alternatingCechToDerivedComparison_of_acyclicBasis _ Y.ringCatSheaf V hV K
    Y.affineOpens Y.isBasis_affineOpens hVaff (fun W hW q ↦ key _ (hK q) W hW)
    (fun W hW q ↦ key _ (isQuasicoherent_cokernel_of_isQuasicoherent Y _ (hK _) (hK _)) W hW)
    (fun W hW q ↦ key _ (isQuasicoherent_homology Y K hK q) W hW)

end

end Stacks.Cech

end
