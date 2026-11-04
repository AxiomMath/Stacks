module

public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.LocalProduct

/-!
# The product of two local sections of iterated tensor powers

Let `L` be an invertible module on a scheme `Y`. This file defines the product of a section of
`L ^⊗ n` and a section of `L ^⊗ m` over an arbitrary open `W` of `Y`, a section of `L ^⊗ (n + m)`
over `W`: it is the multiplication `Stacks.TensorPowerDivision.localMul` of the Laurent algebra of
the `ℤ`-indexed tensor powers, conjugated by the comparison
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` of those powers with the iterated
tensor powers `Stacks.TensorPowers.natTensorPow`.

## Main definitions

* `Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections`: the product
  `Γ(L ^⊗ n, W) × Γ(L ^⊗ m, W) ⟶ Γ(L ^⊗ (n + m), W)` over an open `W`.

## Main results

* `Stacks.AlgebraicGeometry.NatTensorPowLocalMul.map_localMulSections`: the product commutes with
  restriction to a smaller open.
* `Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections_top`: over `⊤` the product is
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare hStruct)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)

universe u

namespace Stacks.AlgebraicGeometry.NatTensorPowLocalMul

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- The product of a section of `L ^⊗ n` over `W` with a section of `L ^⊗ m` over `W`, a section
of `L ^⊗ (n + m)` over `W`: the product `Stacks.TensorPowerDivision.localMul` of the images of the
two sections under `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`, carried back along
`powCompare`. -/
public def localMulSections {n m : ℕ} {W : Y.Opens} (y : Γ(natTensorPow L n, W))
    (z : Γ(natTensorPow L m, W)) : Γ(natTensorPow L (n + m), W) :=
  (powCompare L (n + m)).inv.app W
    (Stacks.TensorPowerDivision.localMul L ((powCompare L n).hom.app W y)
      ((powCompare L m).hom.app W z))

/-- Restriction commutes with the comparison `(powCompare L n).hom` from the iterated tensor power
`L ^⊗ n` to the `ℤ`-indexed tensor power of degree `n`. -/
public theorem map_powCompare_hom (n : ℕ) {W W' : Y.Opens} (i : W' ⟶ W)
    (y : Γ(natTensorPow L n, W)) :
    (Stacks.AmpleProjectiveImmersion.tensorPowerModule Y L (n : ℤ)).presheaf.map i.op
        ((powCompare L n).hom.app W y)
      = (powCompare L n).hom.app W' ((natTensorPow L n).presheaf.map i.op y) :=
  (congrFun (congrArg (fun g => g.hom) ((powCompare L n).hom.val.naturality i.op)) y).symm

/-- Restriction commutes with the comparison `(powCompare L n).inv` from the `ℤ`-indexed tensor
power of degree `n` to the iterated tensor power `L ^⊗ n`. -/
public theorem map_powCompare_inv (n : ℕ) {W W' : Y.Opens} (i : W' ⟶ W)
    (y : Γ(Stacks.AmpleProjectiveImmersion.tensorPowerModule Y L (n : ℤ), W)) :
    (natTensorPow L n).presheaf.map i.op ((powCompare L n).inv.app W y)
      = (powCompare L n).inv.app W'
        ((Stacks.AmpleProjectiveImmersion.tensorPowerModule Y L (n : ℤ)).presheaf.map i.op y) :=
  (congrFun (congrArg (fun g => g.hom) ((powCompare L n).inv.val.naturality i.op)) y).symm

/-- The restriction of the product `localMulSections L y z` to a smaller open is the product of
the restrictions of `y` and `z`. -/
public theorem map_localMulSections {n m : ℕ} {W W' : Y.Opens} (i : W' ⟶ W)
    (y : Γ(natTensorPow L n, W)) (z : Γ(natTensorPow L m, W)) :
    (natTensorPow L (n + m)).presheaf.map i.op (localMulSections L y z)
      = localMulSections L ((natTensorPow L n).presheaf.map i.op y)
          ((natTensorPow L m).presheaf.map i.op z) := by
  rw [localMulSections, localMulSections, map_powCompare_inv, ← map_powCompare_hom,
    ← map_powCompare_hom]
  exact congrArg _ (Stacks.TensorPowerDivision.map_localMul (n := (n : ℤ)) (m := (m : ℤ)) L i _ _)

/-- Over `⊤` the product `localMulSections` is the product of global sections
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`. -/
public theorem localMulSections_top {n m : ℕ} (y : Γ(natTensorPow L n, (⊤ : Y.Opens)))
    (z : Γ(natTensorPow L m, (⊤ : Y.Opens))) :
    localMulSections L y z = mulSections L y z := by
  have h : Stacks.TensorPowerDivision.localMul L ((powCompare L n).hom.app ⊤ y)
        ((powCompare L m).hom.app ⊤ z)
      = (powCompare L (n + m)).hom.app ⊤ (mulSections L y z) :=
    Stacks.AlgebraicGeometry.CoherentMulSections.mulBilinear_mulSections L n m y z
  rw [localMulSections, h,
    Stacks.AlgebraicGeometry.CoherentMulSections.powCompare_inv_app_hom_app]

end Stacks.AlgebraicGeometry.NatTensorPowLocalMul

end
