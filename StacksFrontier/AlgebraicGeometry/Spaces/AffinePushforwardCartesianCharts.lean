module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineCover

/-!
# The direct image along an affine morphism of algebraic spaces is cartesian on affine charts

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` of a big fppf site
`B`. For a morphism `k : V ⟶ U` of affine étale scheme charts of `Y`, the square of rings of
global functions of the base-changed charts `V ×_Y X ⟶ U ×_Y X` over `V ⟶ U` is a pushout. As a
consequence, the direct image along `f` of a module cartesian on affine charts is cartesian on
affine charts, and the direct image of the structure sheaf of `X` is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.isPushout_appTop_smallBaseChange_map`: the square of rings of global
  functions of a base change of affine charts along an affine morphism is a pushout.
* `AlgebraicGeometry.Space.sectionsBaseChange_eq_restrictionBaseChange`: the chartwise base
  change comparison of a module is the base change comparison of its underlying presheaf of
  modules.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_modulePushforward`: the direct image along
  an affine morphism of a module cartesian on affine charts is cartesian on affine charts.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_pushforwardStructureModule` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_pushforwardStructureModule`: the direct image of
  the structure sheaf along an affine morphism is cartesian on affine charts and quasi-coherent.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The pushout square of rings of a base change of affine charts -/

/-- **The square of rings of global functions of a base change of affine charts along an affine
morphism is a pushout.** This holds for a morphism `k : V ⟶ U` of affine étale scheme charts of
`Y` and an affine representable `f : X ⟶ Y`. -/
theorem isPushout_appTop_smallBaseChange_map (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    {V U : SmallEtale B S hS Y.1} (k : V ⟶ U)
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) :
    IsPushout ((BigFppfOver.toScheme B S hS).map (hf.snd U.1.hom)).appTop
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map k)).appTop
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map ((smallBaseChange B S hS f hf).map k))).appTop
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback U.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS f hf haff U hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback V.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS f hf haff V hV
  exact isPushout_appTop_of_isPullback (isPullback_smallBaseChange_map B S hS f hf k)

/-! ### The two spellings of the base change comparison -/

/-- **The chartwise base change comparison of an `𝒪_F`-module is the base change comparison of
its underlying presheaf of modules.** -/
theorem sectionsBaseChange_eq_restrictionBaseChange
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (k : V ⟶ U) :
    letI := chartAlgebra (hF := hF) k
    ∀ z, sectionsBaseChange M k z =
      Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
        (R := structurePresheaf B S hS F) M.val k.op z := by
  let := chartAlgebra (hF := hF) k
  let := chartSectionsModule M k
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
    exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add _ x y).symm
  | tmul b x =>
    refine (chartBaseChange_tmul M k b x).trans ?_
    exact (Stacks.PresheafOfModules.restrictionBaseChange_tmul M.val k.op b x).symm

/-- The chartwise base change comparison is bijective exactly when the base change comparison of
the underlying presheaf of modules is. -/
theorem bijective_sectionsBaseChange_iff_restrictionBaseChange
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (k : V ⟶ U) :
    Function.Bijective (sectionsBaseChange M k) ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
        (R := structurePresheaf B S hS F) M.val k.op) := by
  let := chartAlgebra (hF := hF) k
  rw [funext (sectionsBaseChange_eq_restrictionBaseChange B S hS hF M k)]
  exact Iff.rfl

/-! ### The direct image is cartesian on affine charts -/

/-- **The direct image of Stacks 03LU along an affine morphism of a module cartesian on affine
charts is cartesian on affine charts.** -/
theorem isCartesianOnAffineCharts_modulePushforward (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : IsCartesianOnAffineCharts G) :
    IsCartesianOnAffineCharts ((modulePushforward B S hS f).obj G) :=
  have hf := relativelyRepresentable_of_isAffineHom B S hS f haff
  IsCartesianOnAffineCharts.of_iso
    ((modulePushforwardChartIso B S hS f hf).app G).symm
    (isCartesianOnAffineCharts_smallBaseChangeModulePushforward B S hS f hf G haff hG)

/-! ### The structure sheaf of the source -/

/-- **The direct image of the structure sheaf along an affine morphism of algebraic spaces is
cartesian on affine charts.** -/
theorem isCartesianOnAffineCharts_pushforwardStructureModule (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) :
    IsCartesianOnAffineCharts (pushforwardStructureModule B S hS f) :=
  isCartesianOnAffineCharts_modulePushforward B S hS f haff _
    (isCartesianOnAffineCharts_unit (hF := X.2))

/-- **The direct image of the structure sheaf along an affine morphism of algebraic spaces is
quasi-coherent.** -/
theorem isQuasicoherentOnSite_pushforwardStructureModule (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) :
    (pushforwardStructureModule B S hS f).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_pushforwardStructureModule B S hS f haff)

end AlgebraicGeometry.Space

end
