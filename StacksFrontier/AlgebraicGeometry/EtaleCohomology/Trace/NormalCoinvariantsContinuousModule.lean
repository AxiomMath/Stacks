module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTateTwistCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteTypeContinuousModuleCoinvariants

/-!
# The coinvariants of a normal subgroup as a finite module with continuous action

For a finite `Λ`-module `M` with continuous action of `G` and a normal subgroup `N`, the
coinvariants `M_N` carry the residual action of `G`
(`Stacks.EtaleCohomology.normalCoinvariantsRepresentation`); it is again continuous, so `M_N` is a
finite `Λ`-module with continuous `G`-action, and `M ⟶ M_N` is a morphism of such.

## Main definitions

* `Stacks.EtaleCohomology.finiteTypeContinuousModuleNormalCoinvariants` — `M_N`.
* `Stacks.EtaleCohomology.finiteTypeContinuousModuleNormalCoinvariantsQuotient` — `M ⟶ M_N`.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.GroupCohomology

universe u v

namespace Stacks.EtaleCohomology

variable (Λ : Type u) [Ring Λ] {G : Type v} [Group G] [TopologicalSpace G]
  (N : Subgroup G) [N.Normal]

/-- **`M_N` with the residual `G`-action**, a finite `Λ`-module with continuous action. -/
def finiteTypeContinuousModuleNormalCoinvariants
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) : FiniteTypeContinuousModule.{u, v, v} Λ G := by
  let ρ := finiteTypeContinuousModuleRepresentation Λ G M
  let A : Action (ModuleCat.{v} Λ) G :=
    { V := ModuleCat.of Λ (Stacks.Trace.coinvariants (ρ.comp N.subtype))
      ρ :=
        { toFun := fun g ↦ End.of (ModuleCat.ofHom (normalCoinvariantsRepresentation ρ N g))
          map_one' := End.ext (ModuleCat.hom_ext (map_one (normalCoinvariantsRepresentation ρ N)))
          map_mul' := fun g h ↦ End.ext
            (ModuleCat.hom_ext (map_mul (normalCoinvariantsRepresentation ρ N) g h)) } }
  have hfin : Module.Finite Λ (Stacks.Trace.coinvariants (ρ.comp N.subtype)) := by
    haveI : Module.Finite Λ M.obj.obj.obj.V := M.property
    exact Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  letI : HasForget₂ (ModuleCat.{v} Λ) TopCat.{v} :=
    { forget₂ := forget (ModuleCat.{v} Λ) ⋙ TopCat.discrete
      forget_comp := rfl }
  refine ⟨⟨⟨A, ?_⟩, ⟨rfl⟩⟩, hfin⟩
  refine (Action.isContinuous_def _).2 ?_
  have hM := (Action.isContinuous_def M.obj.obj.obj).mp M.obj.obj.property
  haveI : DiscreteTopology ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj A) := ⟨rfl⟩
  haveI : DiscreteTopology ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj
      M.obj.obj.obj) := ⟨rfl⟩
  let mkT : ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj M.obj.obj.obj) →
      ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj A) :=
    fun x => Submodule.mkQ (Stacks.Trace.coinvariantsKer (ρ.comp N.subtype)) x
  have hmk : Continuous mkT := continuous_of_discreteTopology
  refine continuous_prod_of_discrete_right.2 fun w => ?_
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (Stacks.Trace.coinvariantsKer (ρ.comp N.subtype)) w
  convert hmk.comp (hM.comp (continuous_id.prodMk (continuous_const (y :=
    (m : ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj M.obj.obj.obj)))))) using 1
  all_goals first
    | rfl
    | (funext g; rw [← hm]; rfl)
    | (apply heq_of_eq; funext g; rw [← hm]; rfl)

/-- **The quotient `M ⟶ M_N`**, a morphism of finite `Λ`-modules with continuous `G`-action. -/
def finiteTypeContinuousModuleNormalCoinvariantsQuotient
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) :
    M ⟶ finiteTypeContinuousModuleNormalCoinvariants Λ N M :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (Stacks.Trace.coinvariantsMk
        ((finiteTypeContinuousModuleRepresentation Λ G M).comp N.subtype))
      comm := fun g => by
        ext m
        rfl }))

/-- The quotient `M ⟶ M_N` sends `m` to its class in the coinvariants `M_N`. -/
theorem finiteTypeContinuousModuleNormalCoinvariantsQuotient_apply
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) (m : M.obj.obj.obj.V) :
    (finiteTypeContinuousModuleNormalCoinvariantsQuotient Λ N M).hom.hom.hom.hom.hom m =
      Stacks.Trace.coinvariantsMk ((finiteTypeContinuousModuleRepresentation Λ G M).comp N.subtype)
        m := rfl

end Stacks.EtaleCohomology

end
