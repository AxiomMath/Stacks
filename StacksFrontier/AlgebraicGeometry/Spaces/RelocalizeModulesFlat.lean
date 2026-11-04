module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeChartRestriction

/-!
# Flatness of modules across the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic spaces
over `T`. The lower-shriek extensions `Λ X`, `Λ Y` are algebraic spaces over `S` with the same
étale charts, and `Λ f` has the same commuting squares of charts as `f`. Flatness over the target
(Stacks 05VV) is a condition on those squares and on the restrictions of a module to the source
charts, so it is invariant under the equivalence `Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})`.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.relocalize` and
  `AlgebraicGeometry.Space.ChartDiagram.derelocalize`: the commuting squares of étale charts of `f`
  and of `Λ f` correspond, with the same vertical morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_relocalizeModulesEquivalence_functor_iff` and
  `AlgebraicGeometry.Space.isFlatOver_relocalizeModulesEquivalence_inverse_iff`: flatness over the
  target is preserved and reflected by the equivalence of module categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B T hT X) (hY : IsAlgebraicSpace B T hT Y) (f : X ⟶ Y)


/-- The chart of `Λ Y` attached to the chart `A ≫ f` of `Y` is the chart of `Λ X` attached to `A`
followed by `Λ f`. -/
theorem relocalizeChart_hom_comp_map (A : CostructuredArrow yoneda X) :
    ((OverShriek.relocalizeChart g X).obj A).hom ≫ (OverShriek.relocalizePresheafFunctor g).map f =
      ((OverShriek.relocalizeChart g Y).obj ((CostructuredArrow.map f).obj A)).hom :=
  yonedaEquiv.injective <| (yonedaEquiv_comp _ _).trans <|
    (congrArg _ (Equiv.apply_symm_apply _ _)).trans (Equiv.apply_symm_apply _ _).symm

/-- The chart of `Y` attached to the chart `A ≫ Λ f` of `Λ Y` is the chart of `X` attached to `A`
followed by `f`. -/
theorem relocalizeChartInv_hom_comp
    (A : CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor g).obj X)) :
    ((OverShriek.relocalizeChartInv g X).obj A).hom ≫ f =
      ((OverShriek.relocalizeChartInv g Y).obj
        ((CostructuredArrow.map ((OverShriek.relocalizePresheafFunctor g).map f)).obj A)).hom :=
  yonedaEquiv.injective <| (yonedaEquiv_comp _ _).trans <|
    (congrArg _ (Equiv.apply_symm_apply _ _)).trans (Equiv.apply_symm_apply _ _).symm

/-- **A commuting square of étale charts of `f` is one of `Λ f`**: the charts are relocalized and
the vertical morphism of schemes is unchanged. -/
def ChartDiagram.relocalize (d : ChartDiagram B T hT X Y f) :
    ChartDiagram B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      ((OverShriek.relocalizePresheafFunctor g).obj Y)
      ((OverShriek.relocalizePresheafFunctor g).map f) where
  U := (SmallEtale.relocalize B hT hS g X hX).functor.obj d.U
  V := (SmallEtale.relocalize B hT hS g Y hY).functor.obj d.V
  g := (Over.map g).map d.g
  comm := (relocalizeChart_hom_comp_map B hT hS g f d.U.obj).trans
    (OverShriek.relocalizeChart_w g Y
      (CostructuredArrow.homMk d.g d.comm.symm :
        (CostructuredArrow.map f).obj d.U.obj ⟶ d.V.obj)).symm

/-- **A commuting square of étale charts of `Λ f` is one of `f`**: the charts are read back over
`T` and the vertical morphism of schemes is unchanged. -/
def ChartDiagram.derelocalize
    (d : ChartDiagram B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      ((OverShriek.relocalizePresheafFunctor g).obj Y)
      ((OverShriek.relocalizePresheafFunctor g).map f)) :
    ChartDiagram B T hT X Y f where
  U := (SmallEtale.relocalize B hT hS g X hX).inverse.obj d.U
  V := (SmallEtale.relocalize B hT hS g Y hY).inverse.obj d.V
  g := ((OverShriek.relocalizeChartInv g Y).map
      (CostructuredArrow.homMk d.g d.comm.symm :
        (CostructuredArrow.map ((OverShriek.relocalizePresheafFunctor g).map f)).obj d.U.obj ⟶
          d.V.obj)).left
  comm := (relocalizeChartInv_hom_comp B hT hS g f d.U.obj).trans
    (CostructuredArrow.w ((OverShriek.relocalizeChartInv g Y).map
      (CostructuredArrow.homMk d.g d.comm.symm :
        (CostructuredArrow.map ((OverShriek.relocalizePresheafFunctor g).map f)).obj d.U.obj ⟶
          d.V.obj))).symm

include hY in
/-- Flatness over `Λ Y` of an `𝒪_{Λ X}`-module gives flatness over `Y` of the corresponding
`𝒪_X`-module. -/
theorem isFlatOver_relocalizeModulesEquivalence_inverse
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX))
    (h : IsFlatOver B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
      ((OverShriek.relocalizePresheafFunctor g).map f) M) :
    IsFlatOver B T hT hX f ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M) :=
  fun d x => (flatOverAt_iff_of_iso ((BigFppfOver.toScheme B T hT).map d.g)
    (restrictToChartRelocalizeInverseIso B hT hS g hX d.U M) x).2
      (h (ChartDiagram.relocalize B hT hS g hX hY f d) x)

include hY in
/-- Flatness over `Y` of an `𝒪_X`-module gives flatness over `Λ Y` of the corresponding
`𝒪_{Λ X}`-module. -/
theorem isFlatOver_relocalizeModulesEquivalence_functor (F : Modules.{u, u} B T hT X hX)
    (h : IsFlatOver B T hT hX f F) :
    IsFlatOver B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
      ((OverShriek.relocalizePresheafFunctor g).map f)
      ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F) :=
  fun d x => (flatOverAt_iff_of_iso ((BigFppfOver.toScheme B S hS).map d.g)
    (restrictToChartRelocalizeFunctorIso B hT hS g hX d.U F) x).2
      (h (ChartDiagram.derelocalize B hT hS g hX hY f d) x)

include hY in
/-- **Flatness is invariant under relocalization.** An `𝒪_X`-module is flat over `Y` along `f`
exactly when the corresponding `𝒪_{Λ X}`-module is flat over `Λ Y` along `Λ f`. -/
theorem isFlatOver_relocalizeModulesEquivalence_functor_iff (F : Modules.{u, u} B T hT X hX) :
    IsFlatOver B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        ((OverShriek.relocalizePresheafFunctor g).map f)
        ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F) ↔
      IsFlatOver B T hT hX f F :=
  ⟨fun h => IsFlatOver.of_iso B T hT hX
      ((relocalizeModulesEquivalence B hT hS g X hX).unitIso.app F).symm
      (isFlatOver_relocalizeModulesEquivalence_inverse B hT hS g hX hY f _ h),
    isFlatOver_relocalizeModulesEquivalence_functor B hT hS g hX hY f F⟩

include hY in
/-- **Flatness is invariant under relocalization**, read from `Λ X`. -/
theorem isFlatOver_relocalizeModulesEquivalence_inverse_iff
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    IsFlatOver B T hT hX f ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M) ↔
      IsFlatOver B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        ((OverShriek.relocalizePresheafFunctor g).map f) M :=
  ⟨fun h => IsFlatOver.of_iso B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
      ((relocalizeModulesEquivalence B hT hS g X hX).counitIso.app M)
      (isFlatOver_relocalizeModulesEquivalence_functor B hT hS g hX hY f _ h),
    isFlatOver_relocalizeModulesEquivalence_inverse B hT hS g hX hY f M⟩

end AlgebraicGeometry.Space

end
