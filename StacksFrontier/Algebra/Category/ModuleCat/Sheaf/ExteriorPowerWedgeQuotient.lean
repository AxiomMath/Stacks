module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso

/-!
# The exterior powers of an extension by an invertible quotient

Let `0 → E' → E → E'' → 0` be a short exact sequence of sheaves of modules on a ringed space.
For every `r` the wedge product `⋀ʳ E' ⊗ E ⟶ ⋀ʳ⁺¹ E`, `ω ⊗ e ↦ ω ∧ e`, followed by the quotient
of `⋀ʳ⁺¹ E` by the image of `⋀ʳ⁺¹ E'`, kills `⋀ʳ E' ⊗ E'`, so it descends to

`⋀ʳ E' ⊗ E'' ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'`.

When `E''` is invertible and `E'`, `E` are finite locally free this is an isomorphism, which gives
the short exact sequence `0 → ⋀ʳ⁺¹ E' → ⋀ʳ⁺¹ E → ⋀ʳ E' ⊗ E'' → 0` used to compute the cohomology
of projective bundles.

## Main definitions

* `Stacks.SheafOfModules.WedgeQuotient.wedgeQuotientMap`: the map `⋀ʳ E' ⊗ E ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'`.
* `Stacks.SheafOfModules.WedgeQuotient.wedgeQuotient`: its descent
  `⋀ʳ E' ⊗ E'' ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'`.

## Main results

* `Stacks.SheafOfModules.WedgeQuotient.tensorLeftMap_comp_wedgeQuotient`: the defining equation.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits CategoryTheory.Sheaf
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.WedgeQuotient

open Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (f : E' ⟶ E)

/-- The degree-`r` exterior power of `f`. -/
noncomputable abbrev extPowMap (r : ℕ) : A'.exteriorPower r ⟶ A.exteriorPower r :=
  (extHom A' A f).app (r : ℤ)

/-- **The wedge-and-project map `⋀ʳ E' ⊗ E ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'`.** -/
noncomputable def wedgeQuotientMap (r : ℕ) :
    ((Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
        (A'.exteriorPower r)).obj E ⟶
      cokernel (extPowMap A' A f (r + 1)) :=
  ((Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r)).map
      A.exteriorGenerator ≫ wedgeHom A' A f r 1 ≫
    cokernel.π (extPowMap A' A f (r + 1))

/-- Tensoring on the left with `F` and applying it to a pure tensor. -/
private theorem tensorSheafRight_map_unit {F G G' : _root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (φ : G ⟶ G') (V : (Opens ↥X)ᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    (((Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj F).map φ).val.app V
        ((PresheafOfModules.tensorSheafUnit F G).app V (x ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit F G').app V (x ⊗ₜ φ.val.app V y) := by
  have mapUnit :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp _ _
      (𝟙 F) φ V x y
  have hid : ((Tensor.sheafTensor.{_, _, _, u, u} Osharp).map (𝟙 F)).app G = 𝟙 _ :=
    NatTrans.congr_app ((Tensor.sheafTensor.{_, _, _, u, u} Osharp).map_id _) _
  rw [hid, Category.id_comp] at mapUnit
  exact mapUnit

/-- The wedge-and-project map on a pure tensor. -/
theorem wedgeQuotientMap_unit (r : ℕ) (V : (Opens ↥X)ᵒᵖ) (ω : (A'.exteriorPower r).val.obj V)
    (e : E.val.obj V) :
    (wedgeQuotientMap A' A f r).val.app V
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r) E).app V (ω ⊗ₜ e)) =
      (cokernel.π (extPowMap A' A f (r + 1))).val.app V
        ((A.exterior.mul (r : ℤ) 1).app V (((extHom A' A f).app (r : ℤ)).val.app V ω)
          (A.exteriorGenerator.val.app V e)) := by
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply
    (((Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r)).map A.exteriorGenerator)
    (wedgeHom A' A f r 1 ≫ cokernel.π (extPowMap A' A f (r + 1))) V _) ?_
  have mapUnit := tensorSheafRight_map_unit (F := A'.exteriorPower r) A.exteriorGenerator V ω e
  refine Eq.trans (congrArg (fun y => (wedgeHom A' A f r 1 ≫
      cokernel.π (extPowMap A' A f (r + 1))).val.app V y) mapUnit) ?_
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply (wedgeHom A' A f r 1)
    (cokernel.π (extPowMap A' A f (r + 1))) V _) ?_
  exact congrArg _ (wedgeHom_unit A' A f r 1 V ω _)

/-- **The wedge-and-project map kills `⋀ʳ E' ⊗ E'`.** -/
theorem tensorLeftMap_comp_wedgeQuotientMap (r : ℕ) :
    ((Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r)).map f ≫
      wedgeQuotientMap A' A f r = 0 := by
  refine PresheafOfModules.tensorSheaf_hom_ext (J := Opens.grothendieckTopology ↥X)
    (Osharp := Osharp) fun V ω a => ?_
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ V _) ?_
  have mapUnit := tensorSheafRight_map_unit (F := A'.exteriorPower r) f V ω a
  refine Eq.trans (congrArg (fun y => (wedgeQuotientMap A' A f r).val.app V y) mapUnit) ?_
  refine Eq.trans (wedgeQuotientMap_unit A' A f r V ω (f.val.app V a)) ?_
  rw [← extHom_app_one A' A f V a, ← (extHom A' A f).map_mul]
  have h := congrArg (fun φ => φ.val.app V
      ((A'.exterior.mul (r : ℤ) 1).app V ω (A'.exteriorGenerator.val.app V a)))
    (cokernel.condition (extPowMap A' A f (r + 1)))
  exact h.trans rfl

variable (g : E ⟶ E'') (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).Exact) [Epi g]

/-- `⋀ʳ E' ⊗ E''` is the cokernel of `⋀ʳ E' ⊗ E' ⟶ ⋀ʳ E' ⊗ E`, the tensor product being right
exact. -/
noncomputable def tensorCokernelIsColimit (r : ℕ) :
    IsColimit (@CokernelCofork.map _ _ _ _ _ _ _ _ _ (CokernelCofork.ofπ g hfg)
      (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
          _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
        (Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r))
      (Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafRight
        (Opens.grothendieckTopology ↥X) Osharp (A'.exteriorPower r))) := by
  letI : (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
          _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
        (Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
          (A'.exteriorPower r)).PreservesZeroMorphisms :=
    Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafRight
      (Opens.grothendieckTopology ↥X) Osharp (A'.exteriorPower r)
  letI : ∀ {P Q : _root_.SheafOfModules.{u}
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (h h' : P ⟶ Q),
      PreservesColimit (parallelPair h h')
      (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
          _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
        (Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r)) := fun h h' =>
    Stacks.SheafOfModules.TensorLocalProperties.preservesColimit_parallelPair_tensorSheafRight
      (Opens.grothendieckTopology ↥X) Osharp (A'.exteriorPower r) h h'
  exact CokernelCofork.mapIsColimit _ hS.gIsCokernel
    (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
          _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
        (Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r))

/-- **The comparison `⋀ʳ E' ⊗ E'' ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'`**: the descent of the wedge-and-project
map along `⋀ʳ E' ⊗ E ⟶ ⋀ʳ E' ⊗ E''`. -/
noncomputable def wedgeQuotient (r : ℕ) :
    ((Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
        (A'.exteriorPower r)).obj E'' ⟶
      cokernel (extPowMap A' A f (r + 1)) :=
  (tensorCokernelIsColimit A' f g hfg hS r).desc
    (CokernelCofork.ofπ (wedgeQuotientMap A' A f r) (tensorLeftMap_comp_wedgeQuotientMap A' A f r))

/-- **The defining equation of the comparison.** -/
theorem tensorLeftMap_comp_wedgeQuotient (r : ℕ) :
    ((Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj (A'.exteriorPower r)).map g ≫
      wedgeQuotient A' A f g hfg hS r = wedgeQuotientMap A' A f r :=
  Cofork.IsColimit.π_desc (tensorCokernelIsColimit A' f g hfg hS r)

end Stacks.SheafOfModules.WedgeQuotient

end
