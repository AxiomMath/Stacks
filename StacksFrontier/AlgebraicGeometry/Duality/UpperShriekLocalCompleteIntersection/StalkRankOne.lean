module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.FundamentalClassConstantRank

/-!
# The stalks of `ω_{X/Y}` are free of rank one at constant ranks

In the situation of `Stacks.Duality.ClosedOpenProperFactorization.upperShriekHomologyIso`
(`f = i ≫ U.ι ≫ g` with `i` a Koszul-regular closed immersion whose conormal sheaf has rank `c`
and `g` proper and smooth of relative dimension `d`), the only nonzero cohomology sheaf
`H^{-(d-c)}(f^!𝒪_Y) ≅ ∧^c 𝒩 ⊗ (i ≫ U.ι)^* ∧^d Ω_{P/Y}` has every stalk free of rank one: both
factors are top exterior powers of finite locally free modules (the first one of a dual), whose
stalks are free of rank one (`Stacks.Duality.nonempty_stalk_exteriorPower_dual_linearEquiv`,
`Stacks.Duality.nonempty_stalk_exteriorPower_self_linearEquiv`), and the stalk of a tensor
product is the tensor product of the stalks. This is the invertibility of `ω_{X/Y}` used in the
proof of [Stacks, Tag 0EA3] (`ω_{X'/Y} = 𝒪_{X'}(E)`).

## Main results

* `Stacks.Duality.ClosedOpenProperFactorization.nonempty_stalk_upperShriekHomology_linearEquiv`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

namespace Stacks.Duality.ClosedOpenProperFactorization

attribute [local implicit_reducible] structureSheafRing AlgebraicGeometry.SheafedSpace.sheaf

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {P : Scheme.{u}} (U : P.Opens) (i : X.left ⟶ U.toScheme) (g : P ⟶ Y.left)
  [IsClosedImmersion i] [IsProper g] (hf : i ≫ U.ι ≫ g = f.left)
  (j : CompactificationOf (Over.mk f.left)) (d c : ℕ) [SmoothOfRelativeDimension d g]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion i)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf i) c]

include hf hi in
/-- **The stalks of `H^{-(d-c)}(f^!𝒪_Y)` are free of rank one** over the local rings of `X`. -/
theorem nonempty_stalk_upperShriekHomology_linearEquiv (x : X.left) :
    letI : Module (X.left.presheaf.stalk x)
        (ToType ((upperShriekHomology f j (-((d : ℤ) - c))).presheaf.stalk x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.left.presheaf) (upperShriekHomology f j (-((d : ℤ) - c))).val x
    Nonempty (ToType ((upperShriekHomology f j (-((d : ℤ) - c))).presheaf.stalk x) ≃ₗ[
      X.left.presheaf.stalk x] X.left.presheaf.stalk x) := by
  have hΩ := isFiniteLocallyFreeOfRank_pullback_relativeDifferentials U i g d
  have hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology
        ↥X.left.toLocallyRingedSpace.toRingedSpace.carrier)
        X.left.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalModules U i) c := ‹_›
  let A₁ := _root_.SheafOfModules.ringedSpaceAlgebras X.left.toLocallyRingedSpace.toRingedSpace
    (conormalModules U i)
  let A₀ := _root_.SheafOfModules.ringedSpaceAlgebras X.left.toLocallyRingedSpace.toRingedSpace
    ((Scheme.Modules.pullback (i ≫ U.ι)).obj (Scheme.Hom.relativeDifferentials g))
  let A₁d := _root_.SheafOfModules.ringedSpaceAlgebras X.left.toLocallyRingedSpace.toRingedSpace
    (dualMod (conormalModules U i))
  obtain ⟨eD⟩ := @nonempty_stalk_exteriorPower_dual_linearEquiv _ _ _ A₁d A₁ c hC x
  obtain ⟨eM⟩ := @nonempty_stalk_exteriorPower_self_linearEquiv _ _ _ A₀ d hΩ x
  let := (A₁d.exteriorPower c).val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  let := (A₀.exteriorPower d).val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  let eT := (PresheafOfModules.tensorSheafStalkEquiv _ (A₁d.exteriorPower c)
      (A₀.exteriorPower d) x).trans ((TensorProduct.congr eD eM).trans (TensorProduct.lid _ _))
  let eH := (upperShriekHomologyIso f U i g hf j d c hi).symm
  let e₁ := AlgebraicGeometry.schemeStalkLinearEquiv
    (tensorExteriorPowerPullbackIso U i g d c ≪≫ eH) x
  exact ⟨e₁.symm.trans eT⟩

end Stacks.Duality.ClosedOpenProperFactorization

end
