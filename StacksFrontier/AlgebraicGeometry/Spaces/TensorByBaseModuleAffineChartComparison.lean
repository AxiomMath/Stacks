module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.TensorByBaseModuleAffineChartGluing

/-!
# Gluing the canonical comparison into `𝓕 ⊗_R M` over the affine charts

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `𝓕` be an
`𝒪_X`-module on the small étale site, let `R` be a commutative ring and let `α : R → 𝒪_X(U₀)` be
a ring homomorphism into the sections over a *terminal* étale chart.
`Stacks.TensorByBaseModule.tensorByBaseModule` then produces the `𝒪_X`-module `𝓕 ⊗_R M` for
every `R`-module `M`.

This file puts together the two halves of the last step of the second part of
[Stacks Project, Tag 073K]: the canonical comparison
`Stacks.TensorByBaseModule.comparison` out of the presheaf `U ↦ 𝓕(U) ⊗_R M`, built from a
family `σ : M → (𝓕 ⟶ G)` of `𝒪_X`-module morphisms, and the gluing of
`AlgebraicGeometry.Space.tensorByBaseModuleIsoOfBijectiveOnAffineCharts` over the affine charts.
What is left to the consumer is exactly the chart-wise statement: the comparison
`x ⊗ (a ⊗ m) ↦ a • (σ m)_W x` is bijective over every affine chart `W`.

## Main results

* `AlgebraicGeometry.Space.tensorByBaseModuleIsoOfComparisonOnAffineCharts`: **a family
  `σ : M → (𝓕 ⟶ G)` whose comparison is bijective over every affine chart exhibits `G` as
  `𝓕 ⊗_R M`.**

## Implementation notes

*Why the compatibility of `σ` with scalars is stated through
`Stacks.TensorByBaseModule.presheafMultOfHom` here and through `•` in the general file.*  The
`𝒪_X`-modules of this development are indexed by
`AlgebraicGeometry.Space.smallEtaleRingSheaf`, which is
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪_X`; the ring of sections of that presheaf
of rings over a chart is the ring of sections of `𝒪_X` only after unfolding
`CategoryTheory.sheafCompose`, which instance search does not do, so the action of a section of
`𝒪_X` on a section of a module is not found by instance search at that spelling.  Multiplication
by the image of a scalar is a morphism of presheaves of modules built once and for all in
`Stacks.TensorByBaseModule.presheafMultOfHom`, and reading the hypothesis through it avoids the
synthesis; `Stacks.TensorByBaseModule.presheafMultOfHom_app_apply` identifies the two statements.

No declaration here carries a `stacks` tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite Limits TensorProduct
open Stacks.TensorByBaseModule

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) {U₀ : SmallEtale B S hS X.1} (hU₀ : IsTerminal U₀)
  (R : Type u) [CommRing R] (𝓕 : Modules.{u, u} B S hS X.1 X.2)
  (α : R →+* (structureSheaf B S hS X.1 X.2).val.obj (op U₀))
  (M : ModuleCat.{u} R) (G : Modules.{u, u} B S hS X.1 X.2)
  (σ : M → (𝓕.val ⟶ (PresheafOfModules.restrictScalars
      (𝟙 (smallEtaleRingSheaf B S hS X.1 X.2).obj)).obj
    ((SheafOfModules.forget (smallEtaleRingSheaf B S hS X.1 X.2)).obj G)))
  (hadd : ∀ (m₁ m₂ : M) (W : (SmallEtale B S hS X.1)ᵒᵖ) (x : 𝓕.val.obj W),
    ((σ (m₁ + m₂)).app W).hom x = ((σ m₁).app W).hom x + ((σ m₂).app W).hom x)
  (hsmul : ∀ (r : R) (m : M) (W : (SmallEtale B S hS X.1)ᵒᵖ) (x : 𝓕.val.obj W),
    ((σ (r • m)).app W).hom x
      = ((presheafMultOfHom R (structureSheaf B S hS X.1 X.2).val
            (coefficientMap R hU₀ (O := (structureSheaf B S hS X.1 X.2).val) α) r
            ((PresheafOfModules.restrictScalars
                (𝟙 (smallEtaleRingSheaf B S hS X.1 X.2).obj)).obj
              ((SheafOfModules.forget (smallEtaleRingSheaf B S hS X.1 X.2)).obj G))).app W).hom
          (((σ m).app W).hom x))

include hadd hsmul

/-- **Gluing the canonical comparison over the affine charts.**  On the small étale site of an
algebraic space carrying a terminal chart, a family `σ : M → (𝓕 ⟶ G)` of `𝒪_X`-module morphisms,
additive in `M` and carrying `r • m` to `α(r)` times `σ m`, whose comparison
`x ⊗ (a ⊗ m) ↦ a • (σ m)_W x` is bijective on the sections over every *affine* chart `W`,
exhibits `G` as `𝓕 ⊗_R M`. -/
noncomputable def tensorByBaseModuleIsoOfComparisonOnAffineCharts
    (hbij : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Function.Bijective (comparisonApp R (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) 𝓕
          (coefficientMap R hU₀ (O := (structureSheaf B S hS X.1 X.2).val) α)
          M _ σ hadd hsmul (op W)).hom) :
    (tensorByBaseModule R hU₀ (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) 𝓕 α).obj M ≅ G :=
  tensorByBaseModuleIsoOfBijectiveOnAffineCharts B S hS X hU₀ R 𝓕 α M G
    (comparison R (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) 𝓕
      (coefficientMap R hU₀ (O := (structureSheaf B S hS X.1 X.2).val) α) M _ σ hadd hsmul)
    hbij


/-- **Gluing over the affine charts, with the chart-wise obligation in closed form.**  Same as
`AlgebraicGeometry.Space.tensorByBaseModuleIsoOfComparisonOnAffineCharts`, with the bijectivity
asked of the map `𝓕(W) ⊗_R M → G(W)`, `x ⊗ m ↦ (σ m)_W x`, which is the comparison after the
base change has been cancelled.  This is the statement that [Stacks Project, Tag 03DX] part (2)
supplies at an affine chart. -/
noncomputable def tensorByBaseModuleIsoOfCancelledBijectiveOnAffineCharts
    (hbij : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Function.Bijective (comparisonCancelled R (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) 𝓕
          (coefficientMap R hU₀ (O := (structureSheaf B S hS X.1 X.2).val) α)
          M _ σ hadd hsmul (op W))) :
    (tensorByBaseModule R hU₀ (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) 𝓕 α).obj M ≅ G :=
  tensorByBaseModuleIsoOfComparisonOnAffineCharts B S hS X hU₀ R 𝓕 α M G σ hadd hsmul
    fun W hW => (bijective_comparisonApp_iff R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) 𝓕
      (coefficientMap R hU₀ (O := (structureSheaf B S hS X.1 X.2).val) α)
      M _ σ hadd hsmul (op W)).mpr (hbij W hW)

end AlgebraicGeometry.Space

end
