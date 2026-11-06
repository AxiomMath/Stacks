module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelDerivedHomology
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelInvariantsForget
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedHomologyDelta
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.ResolutionLevelFormula

/-!
# The cohomology of `LH₀(G, M)` is the homology `H_n(G, M)`

Let `π : Γ → Q` be a continuous surjection of profinite groups and `φ : G → Γ` a topological
embedding with image the kernel of `π`. Forgetting the action of `Q`, the cohomology of the
derived homology `LH₀(G, M) ∈ D(Λ[[Q]])` (`Stacks.ContinuousCohomology.kernelDerivedHomology`)
in degree `-n` is the homology `H_n(G, M) = Hⁿ(G, M^∨)^∨` of
`Stacks.ContinuousCohomology.restrictedHomologyDelta`, naturally in `M`
(`Stacks.ContinuousCohomology.kernelDerivedHomologyForgetHomologyIso`). In degree `0` the latter
is the module of coinvariants `M_G` (`Stacks.ContinuousCohomology.restrictedHomologyZeroIso`), so
`LH₀(G, -)` is a derived version of the functor of coinvariants.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.GroupHomology
open scoped CharacterModule.MulOppositeAction

universe v

namespace Stacks.GroupHomology.CompletedGroupAlgebra

/-- Changing coefficients along `f : Λ →+* Λ'` sends the constant `a` to the constant `f a`. -/
theorem mapCoeff_const {Λ Λ' : Type*} [Ring Λ] [Ring Λ'] {G : Type*} [Group G]
    [TopologicalSpace G] (f : Λ →+* Λ') (a : Λ) :
    mapCoeff f (const a : CompletedGroupAlgebra Λ G) = const (f a) :=
  ext fun U ↦ by simp [eval_const, MonoidAlgebra.mapRingHom_single]

end Stacks.GroupHomology.CompletedGroupAlgebra

namespace Stacks.ContinuousCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] [Finite Λ] {G Γ : Type (v + 1)} {Q : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q]

/-- Forgetting the action of `Q` on `Λ[[Q]]`-modules: restriction along the constants. -/
abbrev completedGroupAlgebraForget :
    ModuleCat.{v + 1} (CompletedGroupAlgebra Λ Q) ⥤ ModuleCat.{v + 1} Λ :=
  ModuleCat.restrictScalars.{v + 1} (CompletedGroupAlgebra.const (G := Q) : Λ →+* _)

/-- **The contragredient, with the action of `Q` forgotten, is the character dual**: for a
discrete `Λᵐᵒᵖ`-`Q`-module `V`, `Hom(V, ℚ/ℤ)` restricted to `Λ` is the dual of the underlying
`Λᵐᵒᵖ`-module, naturally in `V`. -/
def contragredientForgetIso :
    contragredient.{0, v, v + 1} Λᵐᵒᵖ Q ⋙
        ModuleCat.restrictScalars (completedGroupAlgebraOpOp Λ (Q := Q)) ⋙
        completedGroupAlgebraForget Λ (Q := Q) ≅
      (Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} Λᵐᵒᵖ Q).op ⋙
        CharacterModule.moduleCatDualOfMulOppositeFunctor Λ :=
  NatIso.ofComponents
    (fun V ↦
      let X := (contragredient.{0, v, v + 1} Λᵐᵒᵖ Q ⋙
        ModuleCat.restrictScalars (completedGroupAlgebraOpOp Λ (Q := Q)) ⋙
        completedGroupAlgebraForget Λ (Q := Q)).obj V
      let Y := ((Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} Λᵐᵒᵖ Q).op ⋙
        CharacterModule.moduleCatDualOfMulOppositeFunctor Λ).obj V
      have hsmul : ∀ (a : Λ) (χ : V.unop.obj.obj.V →+ (trivialRatCircle Q).obj.obj.V),
          (show V.unop.obj.obj.V →+ (trivialRatCircle Q).obj.obj.V from (a • (show X from χ))) =
            (show V.unop.obj.obj.V →+ (trivialRatCircle Q).obj.obj.V from (a • (show Y from χ))) :=
        fun a χ ↦ by
          have h1 : completedGroupAlgebraOpOp Λ (Q := Q) (CompletedGroupAlgebra.const a) =
              CompletedGroupAlgebra.const (MulOpposite.op (MulOpposite.op a)) :=
            CompletedGroupAlgebra.mapCoeff_const _ _
          change (letI := internalHomModule Λᵐᵒᵖ V.unop (trivialRatCircle Q);
            completedGroupAlgebraOpOp Λ (Q := Q) (CompletedGroupAlgebra.const a) • χ) = _
          rw [h1]
          exact AddMonoidHom.ext fun x ↦ internalHom_const_op_smul_apply Λᵐᵒᵖ V.unop
            (trivialRatCircle Q) (MulOpposite.op a) χ x
      { hom := ModuleCat.ofHom (X := X) (Y := Y)
          { toFun χ := χ
            map_add' _ _ := rfl
            map_smul' a χ := hsmul a χ }
        inv := ModuleCat.ofHom (X := Y) (Y := X)
          { toFun χ := χ
            map_add' _ _ := rfl
            map_smul' a χ := (hsmul a χ).symm }
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ ↦ rfl)

variable (φ : G →ₜ* Γ) (π : Γ →ₜ* Q) (hπ : Function.Surjective π)
  (hφπ : (φ : G →* Γ).range = (π : Γ →* Q).ker) (hφ : Topology.IsInducing φ)

/-- The category of discrete `R`-`H`-modules, for `H : Type (v + 1)`, has enough injectives. -/
local instance (priority := 3000) enoughInjectives_kernelDerivedHomologyForget (R : Type)
    [Ring R] (H : Type (v + 1)) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, v + 1, v + 1} R H) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, v + 1, 0} R H

/-- The category of discrete `R`-`H`-modules, for `H : Type v`, has enough injectives. -/
local instance (priority := 3000) enoughInjectives_kernelDerivedHomologyForget_quotient (R : Type)
    [Ring R] (H : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, v, v + 1} R H) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, v, v + 1} R H

section Steps

variable (R : Type) [Ring R]

/-- Restriction of discrete `R`-modules along `φ` is additive. -/
local instance (priority := 3000) additive_res_kdhf :
    (continuousModuleRes.{0, v + 1, v + 1} R φ).Additive :=
  additive_continuousModuleRes.{0, v + 1, 0} R φ

/-- Restriction of discrete `R`-modules along `φ` preserves finite limits. -/
local instance (priority := 3000) preservesFiniteLimits_res_kdhf :
    PreservesFiniteLimits (continuousModuleRes.{0, v + 1, v + 1} R φ) :=
  preservesFiniteLimits_continuousModuleRes.{0, v + 1, 0} R φ

/-- Restriction of discrete `R`-modules along `φ` preserves finite colimits. -/
local instance (priority := 3000) preservesFiniteColimits_res_kdhf :
    PreservesFiniteColimits (continuousModuleRes.{0, v + 1, v + 1} R φ) :=
  preservesFiniteColimits_continuousModuleRes.{0, v + 1, 0} R φ

/-- The underlying `R`-module functor on discrete `R`-`Q`-modules preserves finite limits. -/
local instance (priority := 3000) preservesFiniteLimits_underlying_kdhf :
    PreservesFiniteLimits (Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} R Q) :=
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{0, v, v + 1} R Q

/-- The underlying `R`-module functor on discrete `R`-`Q`-modules preserves finite colimits. -/
local instance (priority := 3000) preservesFiniteColimits_underlying_kdhf :
    PreservesFiniteColimits (Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} R Q) :=
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{0, v, v + 1} R Q

/-- The underlying `R`-module functor on discrete `R`-`Q`-modules is additive. -/
local instance (priority := 3000) additive_underlying_kdhf :
    (Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} R Q).Additive where
  map_add := rfl

/-- `U ∘ H^n ≅ H^n ∘ U` on bounded below derived categories, `U` the underlying module functor. -/
def plusHomologyUnderlyingIso (n : ℤ) :
    DerivedCategory.Plus.homologyFunctor (Stacks.Injectives.ContinuousModule.{0, v, v + 1} R Q) n ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} R Q ≅
      (Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} R Q).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{v + 1} R) n :=
  (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    (Functor.mapDerivedCategoryHomologyFunctorIso
      (Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} R Q) n)).symm

/-- `X[0] ↦ res(X)[0]`: the derived restriction of a single complex, naturally. -/
def singleResIso :
    DerivedCategory.Plus.singleFunctor
        (Stacks.Injectives.ContinuousModule.{0, v + 1, v + 1} R Γ) 0 ⋙
        (continuousModuleRes.{0, v + 1, v + 1} R φ).mapDerivedCategoryPlus ≅
      continuousModuleRes.{0, v + 1, v + 1} R φ ⋙
        DerivedCategory.Plus.singleFunctor
          (Stacks.Injectives.ContinuousModule.{0, v + 1, v + 1} R G) 0 :=
  haveI : IsIso (continuousModuleRes.{0, v + 1, v + 1} R φ).rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology _
  Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (continuousModuleRes.{0, v + 1, v + 1} R φ)).symm ≪≫
    Stacks.Cohomology.ModulePushforwardComparison.singleFunctorPlusRightDerivedIso
      (continuousModuleRes.{0, v + 1, v + 1} R φ)

include hφπ in
/-- **`U(Rⁿ H⁰(G, -)) ≅ Hⁿ(G, res -)`**: forgetting the action of `Q` on the higher derived
invariants under the kernel of `π`. -/
def kernelInvariantsRightDerivedForgetIso (n : ℕ) :
    (kernelInvariantsFunctor.{0, v + 1, v, v + 1} R π hπ).rightDerived n ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, v, v + 1} R Q ≅
      continuousModuleRes.{0, v + 1, v + 1} R φ ⋙
        (continuousModuleRingInvariants.{0, v + 1, v + 1} R G).rightDerived n :=
  Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso
      (kernelInvariantsFunctor.{0, v + 1, v, v + 1} R π hπ) n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (plusHomologyUnderlyingIso R n)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (derivedKernelInvariantsForgetIso.{0, v} R φ π hπ hφπ hφ) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleResIso φ R) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Stacks.DerivedIndexing.rightDerivedIso
      (continuousModuleRingInvariants.{0, v + 1, v + 1} R G) n).symm

end Steps

/-- The functor forgetting the action of `Q` on `Λ[[Q]]`-modules preserves finite limits. -/
local instance (priority := 3000) preservesFiniteLimits_forget_kdhf :
    PreservesFiniteLimits (completedGroupAlgebraForget Λ (Q := Q)) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{0, v, v + 1} _

/-- The functor forgetting the action of `Q` on `Λ[[Q]]`-modules preserves finite colimits. -/
local instance (priority := 3000) preservesFiniteColimits_forget_kdhf :
    PreservesFiniteColimits (completedGroupAlgebraForget Λ (Q := Q)) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{0, v, v + 1} _

include hφπ hφ in
/-- **The cohomology of `LH₀(G, M)` is `H_n(G, M)`**: forgetting the action of `Q`,
`H^{-n}(LH₀(G, M)) ≅ H_n(G, M) = Hⁿ(G, M^∨)^∨`, the homological δ-functor
`Stacks.ContinuousCohomology.restrictedHomologyDelta`, naturally in `M`. -/
def kernelDerivedHomologyForgetHomologyIso (n : ℕ) :
    kernelDerivedHomology Λ π hπ ⋙ (completedGroupAlgebraForget Λ (Q := Q)).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v + 1} Λ) (-(n : ℤ)) ≅
      (restrictedHomologyDelta Λ φ).functor n :=
  Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryHomologyFunctorIso
      (completedGroupAlgebraForget Λ (Q := Q)) (-(n : ℤ))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (kernelDerivedHomologyHomologyIso Λ π hπ n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (contragredientForgetIso Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.rightOpComp _ _).symm ≪≫
      natIsoRightOp (Functor.isoWhiskerLeft (finiteTypeContinuousModuleDual.{0, v + 1, v + 1} Λ Γ)
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
          (kernelInvariantsRightDerivedForgetIso φ π hπ hφπ hφ Λᵐᵒᵖ n))).symm) _

end Stacks.ContinuousCohomology

end
