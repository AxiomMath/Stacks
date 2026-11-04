module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionCompleted
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionIso
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleChangeOfCentre

/-!
# Stacks 0FEC: the composition of the classes of a pair of closed immersions

Let `(S, δ)` be as in Situation 02QL, let `Z ⊆ Y ⊆ X` be closed immersions `i : Z ⟶ Y`,
`j : Y ⟶ X` of schemes locally of finite type over `S`, and let `𝒩`, `𝒩'`, `𝒩''` be virtual
normal sheaves for `Z ⊆ X`, `Z ⊆ Y`, `Y ⊆ X` fitting in the commutative diagram of Stacks 0FEC
(`Stacks.Chow.ConormalCompatibleVirtualNormalBundles`). Then

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`   in `A^*(Z ⟶ X)^∧`.

The proof is the source's. By Stacks 02UC and the blowup of Stacks 02OS it suffices to treat an
integral `X` and the two cases `Y = X` (`Stacks.Chow.compositionIsoCase`) and `Y` an effective
Cartier divisor (`Stacks.Chow.compositionCartierCase`, below); this reduction is
`Stacks.Chow.virtualNormalGysinClass_eq_compositeVirtualNormalGysinClass_of_cases`, and its lift
to virtual normal sheaves of arbitrary rank is
`Stacks.Chow.completedVirtualNormalGysinClass_eq_completedBivariantCompositeOfInvertible_of_cases`.
The Cartier case is the cone argument of the source
(`Stacks.Chow.compositionFormulaAt_fundamentalChowClass_of_normalConeMap`), run on the morphism
`Ψ : N₁ ⟶ C_YX` of `Stacks.Chow.normalConeCompMap`, which restricts to the change of centre on
`C_ZX` and whose inverse image of the zero section is `N'`.

## Main results

* `Stacks.Chow.compositionCartierCase` — the case `Y` an effective Cartier divisor.
* `Stacks.Chow.completedVirtualNormalGysinClass_comp` — **Stacks 0FEC**.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

attribute [-instance] AlgebraicGeometry.IsImmersion.comp

universe u

namespace Stacks.Chow

/-- **The case `Y` an effective Cartier divisor of the proof of Stacks 0FEC**, on the fundamental
class of an integral `X`: the cone argument of the source, with `Ψ : N₁ ⟶ C_YX` the morphism of
`Stacks.Chow.normalConeCompMap` for the reduced datum `𝒩₁, 𝒩', 𝒞_{Y/X}^∨`. -/
theorem compositionCartierCase (C : ChowSituation.{u}) : CompositionCartierCase C := by
  intro Z Y X sZ _ sY _ sX _ i j _ _ hi hj D p q _ _ _ hY k
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hreg : IsRegularImmersion j :=
    (isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor j hY).isRegularImmersion
  -- the morphism `Ψ : N₁ ⟶ C_YX` and its properties (G1, G2)
  have hΨ₀ : normalConeCompMap j hreg i (D.excessKernelBundle hreg)
      (D.excessReductionDualLeft hreg) ≫ Stacks.Conormal.normalConeToBase j =
      (D.excessKernelBundle hreg).projection ≫ i :=
    normalConeCompMap_toBase j hreg i (D.excessKernelBundle hreg) (D.excessReductionDualLeft hreg)
  have ha : D.excessReductionDualLeft hreg ≫ (D.excessKernelBundle hreg).surjection =
      (Scheme.Modules.pullback i).map (regularNormalSurjection j hreg) ≫
        Stacks.Immersion.immersionConormalSheafMap (i ≫ j) j i (𝟙 X)
          (Stacks.Immersion.toShHom_square (Category.comp_id _)) :=
    (D.excessReduction hreg).leftSquare
  have hab : IsShortExactSequenceOfModules (D.excessReductionDualLeft hreg) (D.excessRight hreg) :=
    (D.excessReduction hreg).shortExact
  have hΨ : (D.excessKernelBundle hreg).normalConeEmbedding ≫ normalConeCompMap j hreg i
      (D.excessKernelBundle hreg) (D.excessReductionDualLeft hreg) =
      normalConeChangeOfCentreMap (i ≫ j) j (Scheme.Hom.le_ker_comp i j) :=
    normalConeEmbedding_comp_normalConeCompMap j hreg i (D.excessKernelBundle hreg)
      (D.excessReductionDualLeft hreg) ha (Scheme.Hom.le_ker_comp i j)
  have hν : IsPullback (Scheme.Modules.vectorBundleMap Z
      (F := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (D.excessKernelBundle hreg).bundle)
      (G := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf D.bundleZY.bundle)
      (D.excessRight hreg)).left (D.bundleZY.projection ≫ i)
      (normalConeCompMap j hreg i (D.excessKernelBundle hreg) (D.excessReductionDualLeft hreg))
      (normalConeZeroSection j) :=
    isPullback_normalConeCompMap_normalConeZeroSection j hreg i (D.excessKernelBundle hreg)
      (D.excessReductionDualLeft hreg) (D.excessRight hreg) hab
  exact compositionFormulaAt_fundamentalChowClass_of_normalConeMap C sZ sY sX hi hj D p q hY hreg
    _ hΨ₀ hΨ hν k

variable {C : ChowSituation.{u}} {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {i : Z ⟶ Y} {j : Y ⟶ X} [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ)
  (hj : j ≫ sX = sY) (D : ConormalCompatibleVirtualNormalBundles i j)

/-- **Stacks 0FEC.** Let `(S, δ)` be as in Situation 02QL, let `i : Z ⟶ Y` and `j : Y ⟶ X` be
closed immersions of schemes locally of finite type over `S`, and let `𝒩`, `𝒩'`, `𝒩''` be
virtual normal sheaves for `Z ⊆ X`, `Z ⊆ Y` and `Y ⊆ X` with a short exact sequence
`(𝒩'')^∨|_Z ⟶ 𝒩^∨ ⟶ (𝒩')^∨` whose two squares against the conormal sequence
`𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` commute (`Stacks.Chow.ConormalCompatibleVirtualNormalBundles`).
Then

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`   in `A^*(Z ⟶ X)^∧`,

for the classes of Stacks 0FBK (`Stacks.Chow.completedVirtualNormalGysinClass`) and the
composition of Stacks 0FE0. -/
@[stacks 0FEC]
theorem completedVirtualNormalGysinClass_comp :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    completedVirtualNormalGysinClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj)
        D.bundleZX =
      completedBivariantCompositeOfInvertible C sZ sY sX i j hi hj
        (completedVirtualNormalGysinClass C sZ sY i hi D.bundleZY)
        (completedVirtualNormalGysinClass C sY sX j hj D.bundleYX) :=
  completedVirtualNormalGysinClass_eq_completedBivariantCompositeOfInvertible_of_cases
    sZ sY sX hi hj D (compositionIsoCase C) (compositionCartierCase C)

end Stacks.Chow

end
