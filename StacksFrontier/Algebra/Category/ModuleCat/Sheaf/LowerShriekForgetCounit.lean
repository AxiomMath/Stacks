module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget
import StacksCore.Tactic.StacksAttribute

/-!
# The lower-shriek forget comparison on counits

Let `F : C ⥤ D` be a continuous functor of sites and `φ : S ⟶ f_* R` a morphism of sheaves of
rings making the situation a morphism of ringed sites. The comparison
`Stacks.SheafOfModules.lowerShriekForgetComparison` is determined by its adjoint transpose, the
forgotten unit of the module lower-shriek adjunction. This file proves the corresponding
statement for the counits:

`cmp_{f_*N} ≫ forget(ε^{mod}_N) = ε^{Ab}_{forget N}`.

The identity makes sense because forgetting the module structure commutes with the direct image
on the nose: both are restriction of sections along `F`.

## Main results

* `Stacks.SheafOfModules.lowerShriekForgetComparison_app_comp_counit`: the comparison carries the
  forgotten counit of the module lower-shriek adjunction to the counit of the abelian one.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public section

open CategoryTheory

universe u w u₁ u₂ v₁ v₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : Functor C D) [F.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (phi : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(_root_.SheafOfModules.pushforward.{w} phi).IsRightAdjoint]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The lower-shriek forget comparison carries the forgotten counit of the module lower-shriek
adjunction to the counit of the abelian one: both sides are maps from the abelian lower shriek of
the direct image of `N` to the abelian sheaf underlying `N`, the left one going through the module
lower shriek of the direct image. -/
@[stacks 0798 "the comparison on counits"]
theorem lowerShriekForgetComparison_app_comp_counit (N : _root_.SheafOfModules.{w} R) :
    (lowerShriekForgetComparison F phi).app
          ((_root_.SheafOfModules.pushforward.{w} phi).obj N) ≫
        (_root_.SheafOfModules.toSheaf.{w} R).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).counit.app N) =
      (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).counit.app
        ((_root_.SheafOfModules.toSheaf.{w} R).obj N) := by
  apply ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv _ _).injective
  have htri : (_root_.SheafOfModules.toSheaf.{w} S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).unit.app
          ((_root_.SheafOfModules.pushforward.{w} phi).obj N)) ≫
      (_root_.SheafOfModules.toSheaf.{w} S).map
        ((_root_.SheafOfModules.pushforward.{w} phi).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).counit.app N)) =
      𝟙 _ := by
    rw [← Functor.map_comp,
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).right_triangle_components]
    exact CategoryTheory.Functor.map_id _ _
  have hcmp : (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
        ((_root_.SheafOfModules.toSheaf.{w} S).obj
          ((_root_.SheafOfModules.pushforward.{w} phi).obj N))
        ((_root_.SheafOfModules.pullback.{w} phi ⋙
            _root_.SheafOfModules.toSheaf.{w} R).obj
          ((_root_.SheafOfModules.pushforward.{w} phi).obj N))
        ((lowerShriekForgetComparison F phi).app
          ((_root_.SheafOfModules.pushforward.{w} phi).obj N)) =
      (_root_.SheafOfModules.toSheaf.{w} S).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).unit.app
          ((_root_.SheafOfModules.pushforward.{w} phi).obj N)) :=
    lowerShriekForgetComparison_homEquiv F phi _
  have hL : (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
        ((_root_.SheafOfModules.toSheaf.{w} S).obj
          ((_root_.SheafOfModules.pushforward.{w} phi).obj N))
        ((_root_.SheafOfModules.toSheaf.{w} R).obj N)
        ((lowerShriekForgetComparison F phi).app
            ((_root_.SheafOfModules.pushforward.{w} phi).obj N) ≫
          (_root_.SheafOfModules.toSheaf.{w} R).map
            ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).counit.app N)) =
      𝟙 _ := by
    rw [Adjunction.homEquiv_naturality_right]
    exact (congrArg (fun k => k ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((_root_.SheafOfModules.toSheaf.{w} R).map
          ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} phi).counit.app N)))
      hcmp).trans htri
  have hR : (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv
        ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
          ((_root_.SheafOfModules.toSheaf.{w} R).obj N))
        ((_root_.SheafOfModules.toSheaf.{w} R).obj N)
        ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).counit.app
          ((_root_.SheafOfModules.toSheaf.{w} R).obj N)) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).right_triangle_components _
  exact hL.trans hR.symm

end Stacks.SheafOfModules

end
