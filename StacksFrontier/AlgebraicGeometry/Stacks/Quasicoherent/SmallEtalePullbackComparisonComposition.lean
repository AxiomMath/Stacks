module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleBaseChangeConjugate
public import StacksFrontier.CategoryTheory.Adjunction.CompTranspose

/-!
# The pullback comparison map of Stacks 06WC is functorial in the arrow

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, let `φ : x ⟶ y` and `ψ : y ⟶ z` be
arrows of `𝒳` lying over morphisms of schemes `a : U ⟶ V` and `b : V ⟶ W`, and let `F` be a
presheaf of modules over the structure sheaf of **Stacks 06TV**. This file proves that the pullback
comparison map

`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}`

of Stacks 06WC is functorial in the arrow, as in **Stacks 075D (1)**. No hypothesis on the arrows
is used; in particular `c_φ` is not assumed invertible.

## Main results

* `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_comp`: the composition law for the
  direct-image comparison of Stacks 06WC, as an equality of morphisms of presheaves of modules.
* `AlgebraicGeometry.Stack.restrictModulePullbackComparison_comp`: the pullback along `a_{small}^♯`
  of the comparison below `ψ`, followed by the comparison below `φ`, is the composition law
  `AlgebraicGeometry.Stack.smallEtalePullbackComparisonCompIso` for the pullbacks followed by the
  comparison below `ψ ∘ φ`.

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v v₁

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)

/-- **The composition law of Stacks 075D (1) for the direct-image comparison of Stacks 06WC, as an
equality of morphisms of presheaves of modules.** The comparison below `ψ`, followed by the direct
image along `b_{small}^♯` of the comparison below `φ`, followed by the identifications
`PresheafOfModules.pushforwardComp` and
`AlgebraicGeometry.Stack.smallEtalePushforwardComparisonCompIso` of the pushforwards, is the
comparison below `ψ ∘ φ`. -/
public theorem restrictModulePushforwardComparison_comp :
    (restrictModulePushforwardComparison B E h S hS p hp ψ τ hτ F ≫
          (PresheafOfModules.pushforward.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map
            (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F)) ≫
        ((PresheafOfModules.pushforwardComp.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
              (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom ≫
            (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv).app
          (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F) =
      restrictModulePushforwardComparison B E h S hS p hp (φ ≫ ψ) τ hτ F := by
  refine PresheafOfModules.hom_ext fun W => ?_
  refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun n => ?_)
  change (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).map
      ((NatIso.op (smallEtaleBaseChangeCompIso B E h S hS p φ ψ).symm).hom.app W)
      ((restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).op.obj W)
        ((restrictModulePushforwardComparison B E h S hS p hp ψ τ hτ F).app W n)) = _
  rw [restrictModulePushforwardComparison_app_comp B E h S hS p hp τ hτ φ ψ F W n]
  have hid : (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf.map
        ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).hom.app W.unop).op ≫
      (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf.map
        ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).inv.app W.unop).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id,
      CategoryTheory.Functor.map_id]
  exact ConcreteCategory.congr_hom hid
    ((restrictModulePushforwardComparison B E h S hS p hp (φ ≫ ψ) τ hτ F).app W n)

/-- **The comparison map `c_φ` of Stacks 06WC is functorial in the arrow.** For arrows `φ : x ⟶ y`
and `ψ : y ⟶ z` of `𝒳` lying over morphisms of schemes `a : U ⟶ V` and `b : V ⟶ W`, the pullback
along `a_{small}^♯` of the comparison map below `ψ`, followed by the comparison map below `φ`, is
the composition law `AlgebraicGeometry.Stack.smallEtalePullbackComparisonCompIso` for the pullbacks
followed by the comparison map below `ψ ∘ φ`. -/
@[stacks 075D "part (1), for the pullback comparison map of a presheaf of modules"]
public theorem restrictModulePullbackComparison_comp :
    (PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).map
        (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F) ≫
      restrictModulePullbackComparison B E h S hS p hp φ τ hτ F =
    (smallEtalePullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).hom.app
        (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F) ≫
      restrictModulePullbackComparison B E h S hS p hp (φ ≫ ψ) τ hτ F := by
  have hconj : (smallEtalePullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv =
      (conjugateEquiv
          ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).comp
            (PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)))
          (PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ))).symm
        ((PresheafOfModules.pushforwardComp.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom ≫
          (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv) :=
    ((Equiv.symm_apply_eq _).mpr
      (conjugateEquiv_smallEtalePullbackComparisonCompIso_inv
        B E h S hS p hp τ hτ φ ψ).symm).symm
  have hleft := Stacks.CategoryTheory.homEquiv_conjugate
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).comp
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)))
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ))
    ((PresheafOfModules.pushforwardComp.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom ≫
      (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv)
    ((PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).map
        (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F) ≫
      restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)
  rw [← hconj] at hleft
  have hmid := Stacks.CategoryTheory.homEquiv_comp_map_comp
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ))
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ))
    (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F)
    (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)
  rw [restrictModulePullbackComparison_adjunct,
    restrictModulePullbackComparison_adjunct] at hmid
  have hkey : (smallEtalePullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv.app
        (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F) ≫
      ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).map
          (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F) ≫
        restrictModulePullbackComparison B E h S hS p hp φ τ hτ F) =
      restrictModulePullbackComparison B E h S hS p hp (φ ≫ ψ) τ hτ F := by
    refine ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ)).homEquiv _ _).injective ?_
    exact hleft.trans ((congrArg (fun t => t ≫ _) hmid).trans
      ((restrictModulePushforwardComparison_comp B E h S hS p hp τ hτ φ ψ F).trans
        (restrictModulePullbackComparison_adjunct
          B E h S hS p hp (φ ≫ ψ) τ hτ F).symm))
  exact (Iso.inv_comp_eq (Iso.app
    (smallEtalePullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ)
    (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F))).mp hkey

end AlgebraicGeometry.Stack

end
