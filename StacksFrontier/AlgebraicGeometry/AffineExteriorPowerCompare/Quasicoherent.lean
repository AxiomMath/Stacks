module

public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.AffineCase
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison

/-!
# Exterior powers of a quasi-coherent module on an affine scheme, on global sections

`Stacks.AffineExteriorPower.exteriorPowerΓIso` states the exterior-power assertion of Tag 01I8
for an associated sheaf `M̃` on `Spec R`. **This file states it for an arbitrary quasi-coherent
module** `F` on `Spec R`:

`Γ(Spec R, ⋀ⁿ F) ≅ ⋀ⁿ_R Γ(Spec R, F)`.

The two statements have the same content: a quasi-coherent module on an affine scheme is the
associated sheaf of its global sections.

## Main results

* `Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso`: **the comparison
  `Γ(Spec R, ⋀ⁿ F) ≅ ⋀ⁿ_R Γ(Spec R, F)` for `F` quasi-coherent on `Spec R`.**

## Implementation notes

The exterior algebra of `F` is a hypothesis rather than a chosen term, in the weakest form that
states it: a graded algebra `E` on `Spec R` together with a degree-one generator `gen : F ⟶ E₁`
satisfying `SheafOfModules.GradedAlgebra.IsExteriorAlgebra`. Section 17.21 pins the exterior
algebra only up to canonical isomorphism, so quantifying over every such `E` is strictly
stronger than fixing one, and it subsumes the bundled form: a
`SheafOfModules.TensorExteriorSymmetricAlgebras` supplies `E`, `gen` and the hypothesis through
its `exterior`, `exteriorGenerator` and `exterior_isExteriorAlgebra` fields.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffineBaseChangeLocality (tildeΓIso)

universe u

namespace Stacks.AffineExteriorPower

variable {R : CommRingCat.{u}} (F : (Spec R).Modules) [F.IsQuasicoherent]

/-- **The exterior-power assertion of Tag 01I8 for a quasi-coherent module on an affine
scheme.** If `E` is an exterior algebra of a quasi-coherent module `F` on `Spec R`, with
degree-one generator `gen`, then the global sections of its degree-`n` piece — the `n`-th
exterior power of `F` — are the `n`-th exterior power of the global sections of `F`. -/
def quasicoherentExteriorPowerΓIso
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen) (n : ℕ) :
    moduleSpecΓFunctor.obj (E.piece (n : ℤ)) ≅
      ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)) :=
  (moduleSpecΓFunctor.mapIso
      (AlgebraicGeometry.tildeExteriorPowerIso R (moduleSpecΓFunctor.obj F) n ≪≫
        SheafOfModules.GradedAlgebra.IsUniversal.pieceIso
          (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isUniversal
            (specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra)
          (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isUniversal
            (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso hE
              (tildeΓIso F).hom (tildeΓIso F).isIso_hom)) (n : ℤ))).symm ≪≫
    (tilde.toTildeΓNatIso.app
      (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))).symm

/-- The quasi-coherent form specialises to the bundled form: for a bundle of tensor, exterior
and symmetric algebras on `F`, the hypothesis of
`Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso` is its
`exterior_isExteriorAlgebra` field. -/
def bundledExteriorPowerΓIso
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) F) (n : ℕ) :
    moduleSpecΓFunctor.obj (A.exteriorPower n) ≅
      ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)) :=
  quasicoherentExteriorPowerΓIso F A.exterior_isExteriorAlgebra n

end Stacks.AffineExteriorPower

end
