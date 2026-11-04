module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.Conormal.DegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelLocallyFree
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of the conormal sheaf of an immersion of smooth schemes

Let `S` be a scheme, `p : X ⟶ S` smooth of relative dimension `n` and `ι : Z ⟶ X` an immersion
with `ι ≫ p` smooth of relative dimension `m`. By Tag 06AA the conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ ι^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is short exact, and `Ω_{X/S}`, `Ω_{Z/S}` are finite
locally free of ranks `n` and `m` (Tag 02G1), so `𝒞_{Z/X}` is finite locally free of rank
`n - m`.

## Main results

* `Stacks.ConormalSequenceRight.isFiniteLocallyFree_conormalSheaf_of_smooth`: `𝒞_{Z/X}` is finite
  locally free.
* `Stacks.ConormalSequenceRight.isFiniteLocallyFreeOfRank_conormalSheaf`: `𝒞_{Z/X}` is finite
  locally free of rank `n - m`.
* `Stacks.ConormalSequenceRight.isFiniteLocallyFreeOfRank_conormalSheafDegreeOne`: the same for
  `𝒞_{Z/X}` taken as the degree-one piece of the conormal algebra.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.ConormalSequenceRight

variable {Z X S : Scheme.{u}} (ι : Z ⟶ X) [IsImmersion ι] (p : X ⟶ S) [Smooth p]
  [Smooth (ι ≫ p)] {n m : ℕ}

/-- The kernel of `ι^*Ω_{X/S} ⟶ Ω_{Z/S}` is isomorphic to the conormal sheaf of `ι`. -/
private def kernelConormalSheafIso :
    kernel (conormalShortComplex ι p).g ≅ Stacks.Conormal.conormalSheaf ι :=
  have hS := conormalShortComplex_shortExact ι p inferInstance
  have := hS.mono_f
  (hS.exact.fIsKernel.conePointUniqueUpToIso (kernelIsKernel _)).symm ≪≫
    Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge ι

include p in
/-- **The conormal sheaf of an immersion of smooth schemes is finite locally free**: it is the
kernel of the surjection `ι^*Ω_{X/S} ⟶ Ω_{Z/S}` of finite locally free modules (Tag 06AA). -/
@[sga "3 VIB 1.6" "more general", sga "6 X 7.1" "special case"]
theorem isFiniteLocallyFree_conormalSheaf_of_smooth :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheaf ι) := by
  have hS := conormalShortComplex_shortExact ι p inferInstance
  set T := conormalShortComplex ι p
  have : Epi T.g := hS.epi_g
  have := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials p
  have hker := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi T.g
    inferInstance (Stacks.Chow.isFiniteLocallyFree_pullback ι _ inferInstance)
    (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (ι ≫ p))
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
    (kernelConormalSheafIso ι p) (h := hker)

/-- **The conormal sheaf of an immersion of smooth schemes is finite locally free of rank
`n - m`**, for `X` smooth of relative dimension `n` and `Z` smooth of relative dimension `m`
over `S`: it is the kernel of the surjection `ι^*Ω_{X/S} ⟶ Ω_{Z/S}` (Tag 06AA). -/
theorem isFiniteLocallyFreeOfRank_conormalSheaf (hX : RelativeDimension p n)
    (hZ : RelativeDimension (ι ≫ p) m) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheaf ι) (n - m) := by
  have hS := conormalShortComplex_shortExact ι p inferInstance
  set T := conormalShortComplex ι p
  have : Epi T.g := hS.epi_g
  have := Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension p hX
  have hker := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi T.g
    inferInstance n m (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ n)
    (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension _ hZ)
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (kernelConormalSheafIso ι p) hker

/-- **The conormal sheaf, as the degree-one piece of the conormal algebra, is finite locally
free of rank `n - m`** in the situation of `isFiniteLocallyFreeOfRank_conormalSheaf`. -/
theorem isFiniteLocallyFreeOfRank_conormalSheafDegreeOne (hX : RelativeDimension p n)
    (hZ : RelativeDimension (ι ≫ p) m) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne ι) (n - m) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (Stacks.Conormal.conormalDegreeOneIso ι) (isFiniteLocallyFreeOfRank_conormalSheaf ι p hX hZ)

end Stacks.ConormalSequenceRight

end
