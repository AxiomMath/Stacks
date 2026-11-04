module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.AlgebraicGeometry.IdealSheafRestrict.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Kernels and homology of quasi-coherent modules on a scheme

On an affine scheme the kernel of a morphism of quasi-coherent modules is quasi-coherent, which
is the kernel half of [Stacks, Tag 01IC]; on an arbitrary scheme the cokernel of such a morphism
is quasi-coherent, by `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`.
This file proves the kernel statement on an arbitrary scheme, and deduces that every homology
module of a complex of quasi-coherent modules is quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.QuasicoherentLimits.isQuasicoherent_kernel`: the kernel of a
  morphism of quasi-coherent modules on a scheme is quasi-coherent.
* `Stacks.AlgebraicGeometry.QuasicoherentLimits.isQuasicoherent_homology`: the homology of a
  complex of quasi-coherent modules on a scheme is quasi-coherent in every degree.

## References

* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.QuasicoherentLimits

/-- The restriction to an affine open of the kernel of a morphism of quasi-coherent modules is
quasi-coherent. -/
theorem isQuasicoherent_restrict_kernel {X : Scheme.{u}} {M N : X.Modules}
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) (f : M ⟶ N) (V : X.affineOpens) :
    ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj (kernel f)).IsQuasicoherent := by
  have := hM
  have := hN
  have : IsAffine (V : X.Opens).toScheme := V.2
  have := Stacks.IdealSheafRestrict.preservesFiniteLimits_restrictFunctor (V : X.Opens).ι
  have h : (kernel ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).map f)).IsQuasicoherent :=
    Stacks.AffineTilde.isQuasicoherent_kernel _
  have e : (Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj (kernel f) ≅
      kernel ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).map f) :=
    PreservesKernel.iso _ f
  exact (SheafOfModules.isQuasicoherent ((V : X.Opens).toScheme).ringCatSheaf).prop_of_iso
    e.symm h

/-- The kernel of a morphism of quasi-coherent modules on a scheme is quasi-coherent. -/
instance isQuasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules} [hM : M.IsQuasicoherent]
    [hN : N.IsQuasicoherent] (f : M ⟶ N) : (kernel f).IsQuasicoherent :=
  QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _
    (isQuasicoherent_restrict_kernel hM hN f)

/-- Every homology module of a complex of quasi-coherent modules on a scheme is
quasi-coherent. -/
theorem isQuasicoherent_homology {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, (K.X n).IsQuasicoherent) (q : ℤ) : (K.homology q).IsQuasicoherent := by
  have : ((K.sc q).X₁).IsQuasicoherent := hK _
  have : (kernel (K.sc q).g).IsQuasicoherent := isQuasicoherent_kernel (hM := hK _) (hN := hK _) _
  have hcok : (cokernel (kernel.lift (K.sc q).g (K.sc q).f (K.sc q).zero)).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (K.sc q).homologyIsoCokernelLift.symm hcok

end Stacks.AlgebraicGeometry.QuasicoherentLimits

end
