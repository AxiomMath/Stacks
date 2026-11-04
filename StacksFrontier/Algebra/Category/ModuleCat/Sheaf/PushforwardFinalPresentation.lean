module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationIsIso

/-!
# Lifting a global presentation along a final restriction

Let `F : C ⥤ D` be a continuous and cocontinuous functor of small sites which is final, and let
`φ : S ⟶ F^s R` be an isomorphism of sheaves of rings, so that restriction
`F^* : Mod(R) ⥤ Mod(S)` carries the structure sheaf to the structure sheaf. If the restriction
`F^*N` of a module `N` admits a global presentation, then so does a module `P` with a map
`c : P ⟶ N` whose restriction is invertible: take `P = F_!F^*N` and `c` the counit. This is the
step "pulling back the presentation" of the converse direction of Stacks 0D7M.

## Main results

* `Stacks.SheafOfModules.isIso_pullbackPushforwardAdjunction_unit_app_of_hasGlobalPresentation`:
  the unit `M ⟶ F^*F_!M` is invertible at every module with a global presentation.
* `Stacks.SheafOfModules.exists_hasGlobalPresentation_isIso_pushforward_map`: the lifted
  presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D)
  [F.IsContinuous J K] [F.IsCocontinuous J K] [F.Final]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

omit [F.IsCocontinuous J K] [F.Final] in
/-- Restriction of sheaves of modules along a continuous functor of small sites has a left
adjoint, the sheafified presheaf pullback. -/
theorem isRightAdjoint_pushforward_of_small :
    (_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint := by
  let φ' : S.obj ⟶ F.op ⋙ R.obj := φ.hom
  have : (PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint :=
    (inferInstance : (PresheafOfModules.pushforward.{u} φ').IsRightAdjoint)
  infer_instance

attribute [local instance] isRightAdjoint_pushforward_of_small

/-- **The unit of `F_! ⊣ F^*` is invertible on modules with a global presentation.** At the
structure sheaf it is the comparison `S ⟶ F^*R` followed by the inverse of `F_!S ≅ R`, both
invertible; both sides preserve colimits, so the mechanism of
`Stacks.SheafOfModules.isIso_app_of_hasGlobalPresentation` applies. -/
theorem isIso_pullbackPushforwardAdjunction_unit_app_of_hasGlobalPresentation
    [IsIso φ] {M : _root_.SheafOfModules.{u} S} (hM : M.HasGlobalPresentation) :
    IsIso ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app M) := by
  have h₁ : PreservesColimitsOfSize.{u, u} (_root_.SheafOfModules.pushforward.{u} φ) :=
    pushforward_preservesColimits F φ
  have hunit : IsIso ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app
      (_root_.SheafOfModules.unit S)) := by
    have hφ := isIso_unitToPushforwardObjUnit φ
    have e : (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit.app
          (_root_.SheafOfModules.unit S) ≫
        (_root_.SheafOfModules.pushforward.{u} φ).map
          (_root_.SheafOfModules.pullbackObjUnitToUnit φ) =
        _root_.SheafOfModules.unitToPushforwardObjUnit φ := by
      exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans
        (_root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ)
    rw [← e] at hφ
    exact IsIso.of_isIso_comp_right _
      ((_root_.SheafOfModules.pushforward.{u} φ).map
        (_root_.SheafOfModules.pullbackObjUnitToUnit φ))
  exact isIso_app_of_hasGlobalPresentation
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ).unit hunit hM

/-- **A global presentation lifts along a final restriction.** If the restriction `F^*N` of a
sheaf of `R`-modules admits a global presentation, there is a module `P` with a global
presentation and a map `c : P ⟶ N` whose restriction `F^*c` is invertible; namely `F_!F^*N` and
the counit. -/
theorem exists_hasGlobalPresentation_isIso_pushforward_map
    [IsIso φ] {N : _root_.SheafOfModules.{u} R}
    (hN : ((_root_.SheafOfModules.pushforward.{u} φ).obj N).HasGlobalPresentation) :
    ∃ (P : _root_.SheafOfModules.{u} R) (c : P ⟶ N), P.HasGlobalPresentation ∧
      IsIso ((_root_.SheafOfModules.pushforward.{u} φ).map c) := by
  let adj := _root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ
  have hη := isIso_pullbackPushforwardAdjunction_unit_app_of_hasGlobalPresentation F φ hN
  refine ⟨(_root_.SheafOfModules.pullback.{u} φ).obj
      ((_root_.SheafOfModules.pushforward.{u} φ).obj N), adj.counit.app N, ?_, ?_⟩
  · have hL : PreservesColimitsOfSize.{u, u} (_root_.SheafOfModules.pullback.{u} φ) :=
      adj.leftAdjoint_preservesColimits
    have hpUU : IsIso (_root_.SheafOfModules.pullbackObjUnitToUnit φ) := inferInstance
    exact GlobalPresentationTransport.hasGlobalPresentation_of_functor
      (F₀ := _root_.SheafOfModules.pullback.{u} φ) (F := _root_.SheafOfModules.pullback.{u} φ)
      _ hL inferInstance
      ((_root_.SheafOfModules.pullback.{u} φ).mapIso
          (uliftForPresentationIsoSelf.{u, u, u, u} (_root_.SheafOfModules.unit S)).symm ≪≫
        asIso (_root_.SheafOfModules.pullbackObjUnitToUnit φ) ≪≫
        uliftForPresentationIsoSelf.{u, u, u, u} (_root_.SheafOfModules.unit R))
      ((_root_.SheafOfModules.pullback.{u} φ).mapIso
          (uliftForPresentationIsoSelf.{u, u, u, u} _).symm ≪≫
        uliftForPresentationIsoSelf.{u, u, u, u} _) hN
  · have h := adj.right_triangle_components N
    have : IsIso ((_root_.SheafOfModules.pushforward.{u} φ).map (adj.counit.app N)) := by
      have e : (_root_.SheafOfModules.pushforward.{u} φ).map (adj.counit.app N) =
          inv (adj.unit.app ((_root_.SheafOfModules.pushforward.{u} φ).obj N)) := by
        rw [← cancel_epi (adj.unit.app ((_root_.SheafOfModules.pushforward.{u} φ).obj N)),
          IsIso.hom_inv_id]
        exact h
      rw [e]
      infer_instance
    exact this

end Stacks.SheafOfModules

end
