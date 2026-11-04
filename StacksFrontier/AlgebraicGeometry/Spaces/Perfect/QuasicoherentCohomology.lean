module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.PerfectToPseudoCoherentGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional

/-!
# The cohomology sheaves of a perfect object on an algebraic space are quasi-coherent

Each cohomology sheaf of a perfect object of `D(𝒪_F)`, for `F` an algebraic space, is a
quasi-coherent `𝒪_F`-module.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPerfect`: the cohomology sheaves
  of a perfect object are quasi-coherent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Each cohomology sheaf of a perfect object of `D(𝒪_F)` is a quasi-coherent `𝒪_F`-module. -/
theorem isQuasicoherentOnSite_homology_of_isPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (i : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPerfect E) :
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj
      E).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional B S hS F hF E (i - 1) i
    (AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_general
      (smallEtaleRingedSite B S hS F hF) hE (i - 1)) (by lia)

end AlgebraicGeometry.Space

end
