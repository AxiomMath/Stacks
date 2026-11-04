module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeExteriorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras

/-!
# Exterior powers of an associated sheaf on an affine scheme

Let `R` be a commutative ring, `M` an `R`-module and `A` an exterior algebra of `M̃` on `Spec R`
(`SheafOfModules.TensorExteriorSymmetricAlgebras`). The associated sheaf of `⋀ⁿ_R M` is the
`n`-th exterior power of `M̃`, and on global sections this reads `Γ(Spec R, ⋀ⁿ(M̃)) ≅ ⋀ⁿ_R M`.

## Main definitions

* `Stacks.AffineExteriorPower.tildeExteriorPowerIso`: the affine exterior-power comparison
  `(⋀ⁿ_R M)~ ≅ ⋀ⁿ(M̃)`.
* `Stacks.AffineExteriorPower.exteriorPowerΓIso`: the same comparison on global sections,
  `Γ(Spec R, ⋀ⁿ(M̃)) ≅ ⋀ⁿ_R M`.

## Implementation notes

`tildeExteriorPowerIso` is `AlgebraicGeometry.tildeExteriorPowerIso`, the comparison of `(⋀ⁿ_R M)~`
with the exterior power of the bundle `AlgebraicGeometry.specTildeAlgebras`, followed by the
canonical comparison `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso` of two
bundles over the same sheaf of modules. `exteriorPowerΓIso` composes it with
`AlgebraicGeometry.tilde.toTildeΓNatIso`, the isomorphism `𝟭 ≅ (-)~ ⋙ Γ(Spec R, -)`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AffineExteriorPower

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
  (A : SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥(Spec R)) (tilde M))

/-- **The affine exterior-power comparison.** The associated sheaf of the `n`-th exterior power
of `M` is the `n`-th exterior power of `M̃`. -/
@[stacks 01I8 "exterior_power"]
def tildeExteriorPowerIso (n : ℕ) :
    (tilde (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) : SheafOfModules.{u} (Spec R).ringCatSheaf) ≅
      A.exteriorPower n :=
  AlgebraicGeometry.tildeExteriorPowerIso R M n ≪≫
    SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso
      (specTildeAlgebras R M) A (n : ℤ)

/-- The forward map of `tildeExteriorPowerIso` is the forward map of
`AlgebraicGeometry.tildeExteriorPowerIso` followed by that of the canonical comparison
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso` of exterior powers. -/
theorem tildeExteriorPowerIso_hom (n : ℕ) :
    (tildeExteriorPowerIso M A n).hom =
      (AlgebraicGeometry.tildeExteriorPowerIso R M n).hom ≫
        (SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso
          (specTildeAlgebras R M) A (n : ℤ)).hom :=
  rfl

/-- The transpose under the affine adjunction of a morphism `h : Ñ ⟶ F` sends `y : N` to the
value of `h` on the global section of `Ñ` determined by `y`. -/
theorem tildeHomEquiv_apply (N : ModuleCat.{u} R) (F : (Spec R).Modules) (h : tilde N ⟶ F)
    (y : N) :
    (((tilde.adjunction (R := R)).homEquiv N F) h).hom y =
      h.val.app (specGlobalOpen R) ((tilde.toOpen N ⊤).hom y) :=
  rfl

/-- **The affine exterior-power comparison on global sections.** For a quasi-coherent module
`M̃` on the affine scheme `Spec R`, the global sections of the `n`-th exterior power of `M̃` are
the `n`-th exterior power of the global sections of `M̃`, namely `⋀ⁿ_R M`. -/
def exteriorPowerΓIso (n : ℕ) :
    moduleSpecΓFunctor.obj (A.exteriorPower n) ≅ ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M) :=
  (moduleSpecΓFunctor.mapIso (tildeExteriorPowerIso M A n)).symm ≪≫
    (tilde.toTildeΓNatIso.app (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M))).symm

/-- The inverse of `exteriorPowerΓIso` is the unit `⋀ⁿ_R M ⟶ Γ(Spec R, (⋀ⁿ_R M)~)` of the affine
adjunction followed by the global sections of the forward map of `tildeExteriorPowerIso`. -/
theorem exteriorPowerΓIso_inv (n : ℕ) :
    (exteriorPowerΓIso M A n).inv =
      (tilde.toTildeΓNatIso.app (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M))).hom ≫
        moduleSpecΓFunctor.map (tildeExteriorPowerIso M A n).hom :=
  rfl

end Stacks.AffineExteriorPower

end
