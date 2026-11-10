module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineChartVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.HigherBaseChangeDegreeZero
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The Kummer coboundary of a direct image

Let `j : U₀ ⟶ U` be a morphism of schemes and `N` an integer invertible on `U`. The Kummer
sequence `0 ⟶ μ_N ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` on `U₀` is short exact, so the `δ`-functor of the higher direct
images `R^q j_*` gives a connecting morphism of abelian sheaves on `U`
`∂ : j_* 𝐆_m ⟶ R¹ j_* μ_N` (`Stacks.EtaleCohomology.Purity.kummerDirectImageδ`). Its value on a
unit `t` on (an étale `U`-scheme over) `U₀` is the local Kummer class of `t`.

The units of `U` itself die under `∂`
(`Stacks.EtaleCohomology.Purity.multiplicativeDirectImageComparison_comp_kummerDirectImageδ`): the
`N`-th power map of `𝐆_m` on `U` is an epimorphism, and `∂` kills the `N`-th powers of `j_* 𝐆_m`.
Hence the class `∂ t` of a local equation `t` of a divisor does not depend on the choice of `t` up
to a unit; this is how the fundamental class of the divisor in `R¹ j_* μ_N` is glued from local
equations.

## Implementation notes

The source `j_* 𝐆_m` is identified with `R⁰ j_* 𝐆_m` by the degree-zero unit
`Stacks.RightDerivedPlus.rightDerivedZeroUnit` followed by the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the two indexings of the right derived functors. This
is the normalisation in which the base change maps in degree zero are the underived base change
maps (`Stacks.EtaleCohomology.map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero`), so that
`∂` is transported by base change through `Stacks.EtaleCohomology.higherBaseChangeMapAb_comp_δ`.

## Main definitions

* `Stacks.EtaleCohomology.Purity.kummerDirectImageδ`.

## Main results

* `Stacks.EtaleCohomology.Purity.map_powMap_comp_kummerDirectImageδ`.
* `Stacks.EtaleCohomology.Purity.multiplicativeDirectImageComparison_comp_kummerDirectImageδ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

/-- If `f ≫ a = a' ≫ g` and `g ≫ b = 0` then `f ≫ a ≫ b = 0`. -/
theorem comp_comp_eq_zero_of_comp_eq {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {W X Y Y' Z : C} (f : W ⟶ X) (a : X ⟶ Y) (a' : W ⟶ Y') (g : Y' ⟶ Y) (b : Y ⟶ Z)
    (h₁ : f ≫ a = a' ≫ g) (h₂ : g ≫ b = 0) : f ≫ a ≫ b = 0 := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, comp_zero]

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U)
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] {N : ℕ}

/-- **The Kummer coboundary `∂ : j_* 𝐆_m ⟶ R¹ j_* μ_N`** of the Kummer sequence on `U₀`, from the
`δ`-functor of the higher direct images along `j`, with `j_* 𝐆_m` identified with `R⁰ j_* 𝐆_m`
by the degree-zero unit `Stacks.RightDerivedPlus.rightDerivedZeroUnit` and the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the indexings (the normalisation of
`Stacks.EtaleCohomology.map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero`). -/
@[irreducible]
def kummerDirectImageδ (hN0 : N ≠ 0) (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) :
    (smallEtalePushforwardAb j).obj (multiplicativeSheaf.{u, 0} U₀) ⟶
      ((smallEtalePushforwardAb j).rightDerived 1).obj (rootsOfUnitySheaf.{u, 0} U₀ N) :=
  (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb j)
      (multiplicativeSheaf.{u, 0} U₀) ≫
    (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.app
      (multiplicativeSheaf.{u, 0} U₀)) ≫
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (smallEtalePushforwardAb j)).δ (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0

/-- The definition of `Stacks.EtaleCohomology.Purity.kummerDirectImageδ`. -/
theorem kummerDirectImageδ_eq (hN0 : N ≠ 0) (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) :
    kummerDirectImageδ j hN0 hN =
      (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb j)
          (multiplicativeSheaf.{u, 0} U₀) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.app
          (multiplicativeSheaf.{u, 0} U₀)) ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb j)).δ (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0 := by
  unfold kummerDirectImageδ
  rfl

/-- **`∂` kills the `N`-th powers.** -/
theorem map_powMap_comp_kummerDirectImageδ (hN0 : N ≠ 0) (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) :
    (smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N) ≫ kummerDirectImageδ j hN0 hN = 0 := by
  have h := (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb j)).map_g_δ (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0
  have h' : ((smallEtalePushforwardAb j).rightDerived 0).map (powMap.{u, 0} U₀ N) ≫
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb j)).δ (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0 = 0 := h
  have hn : (smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N) ≫
      (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb j)
          (multiplicativeSheaf.{u, 0} U₀) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.app
          (multiplicativeSheaf.{u, 0} U₀)) =
      (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb j)
          (multiplicativeSheaf.{u, 0} U₀) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.app
          (multiplicativeSheaf.{u, 0} U₀)) ≫
        ((smallEtalePushforwardAb j).rightDerived 0).map (powMap.{u, 0} U₀ N) := by
    rw [reassoc_of% (Stacks.DerivedFunctor.rightDerivedZeroUnit_naturality
      (smallEtalePushforwardAb j) (powMap.{u, 0} U₀ N)), Category.assoc]
    exact congrArg (_ ≫ ·)
      ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.naturality
        (powMap.{u, 0} U₀ N))
  rw [kummerDirectImageδ_eq]
  exact comp_comp_eq_zero_of_comp_eq _ _ _ _ _ hn h'

/-- **The units of `U` die under `∂`.** The restriction `𝐆_m ⟶ j_* 𝐆_m` followed by the Kummer
coboundary `∂ : j_* 𝐆_m ⟶ R¹ j_* μ_N` is zero, for `N` invertible on `U`: the `N`-th power map
of `𝐆_m` on `U` is an epimorphism, and it is carried by the restriction to the `N`-th power map of
`j_* 𝐆_m`, which `∂` kills. -/
theorem multiplicativeDirectImageComparison_comp_kummerDirectImageδ (hN0 : N ≠ 0)
    (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤))) :
    multiplicativeDirectImageComparison.{u, 0} j ≫ kummerDirectImageδ j hN0 hN = 0 := by
  have := epi_powMap.{u, 0} U hN0 hNU
  rw [← cancel_epi (powMap.{u, 0} U N), comp_zero]
  let ρ : multiplicativeSheaf.{u, 0} U ⟶
      (smallEtalePushforwardAb j).obj (multiplicativeSheaf.{u, 0} U₀) :=
    multiplicativeDirectImageComparison.{u, 0} j
  have h1 : powMap.{u, 0} U N ≫ ρ = N • ρ := by
    rw [powMap, Preadditive.nsmul_comp, Category.id_comp]
  have h2 : ρ ≫ (smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N) = N • ρ := by
    rw [powMap, Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.comp_nsmul,
      Category.comp_id]
  change powMap.{u, 0} U N ≫ ρ ≫ kummerDirectImageδ j hN0 hN = 0
  rw [← Category.assoc, h1, ← h2, Category.assoc, map_powMap_comp_kummerDirectImageδ j hN0 hN,
    comp_zero]

end Stacks.EtaleCohomology.Purity

end
