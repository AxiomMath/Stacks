module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentKernelHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingCechComputesDerivedSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A covering with affine intersections computes the derived sections of a quasi-coherent complex

Let `Y` be a scheme and let `U : I → Y.Opens` be a finite open covering of `Y` all of whose
finite intersections `U_{i_0 … i_p}` are affine opens. Let `F^•` be a complex of quasi-coherent
`𝒪_Y`-modules, unbounded in both directions. Then the comparison map

`Tot(Č_alt^•(U, F^•)) ⟶ RΓ(Y, F^•)`

of [Stacks, Tag 08C1] is an isomorphism in `D(Ab)`.

## Main results

* `Stacks.Cohomology.AlternatingCech.isIso_alternatingCechToDerivedComparison_of_isAffineOpen`:
  the comparison map `Tot(Č_alt^•(U, F^•)) ⟶ RΓ(Y, F^•)` is an isomorphism.

## References

* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.Cohomology.AlternatingCech

attribute [local instance] HasDerivedCategory.standard

/-- **A finite covering whose finite intersections are affine computes the derived sections of a
complex of quasi-coherent modules.** For a scheme `Y`, a finite open covering `U` of `Y` whose
finite intersections are all affine opens, and a complex `F^•` of quasi-coherent
`𝒪_Y`-modules, the comparison map `Tot(Č_alt^•(U, F^•)) ⟶ RΓ(Y, F^•)` of [Stacks, Tag 08C1] is
an isomorphism in the derived category of abelian groups. -/
@[ega "III 1.4.2" "special case"]
theorem isIso_alternatingCechToDerivedComparison_of_isAffineOpen (Y : Scheme.{u}) {I : Type u}
    [Finite I] (U : I → Y.Opens) (hU : (⊤ : Y.Opens) = iSup U)
    (haff : ∀ (p : ℕ) (s : Fin (p + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (F : CochainComplex Y.Modules ℤ) (hF : ∀ n, (F.X n).IsQuasicoherent) :
    IsIso ((Stacks.Cech.alternatingCechToDerivedComparison
      (TopCat.of Y) Y.ringCatSheaf U hU).app F) := by
  refine Stacks.Cech.isIso_alternatingCechToDerivedComparison_of_acyclicBasis
    (TopCat.of Y) Y.ringCatSheaf U hU F Y.affineOpens Y.isBasis_affineOpens
    (fun p s ↦ haff p s) (fun W hW q p hp ↦ ?_) (fun W hW q p hp ↦ ?_) (fun W hW q p hp ↦ ?_)
  · have := hF q
    exact (CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      Y.ringCatSheaf W p (F.X q)).2
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen Y (F.X q) W hW p hp)
  · have := hF (q - 1)
    have := hF q
    have : (cokernel (F.d (q - 1) q)).IsQuasicoherent := inferInstance
    exact (CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      Y.ringCatSheaf W p (cokernel (F.d (q - 1) q))).2
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen Y
        (cokernel (F.d (q - 1) q)) W hW p hp)
  · have := AlgebraicGeometry.QuasicoherentLimits.isQuasicoherent_homology F hF q
    exact (CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      Y.ringCatSheaf W p (F.homology q)).2
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen Y (F.homology q) W hW p hp)

end Stacks.Cohomology.AlternatingCech

end
