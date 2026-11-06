module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteTypeContinuousModuleCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction

/-!
# The invariants of a normal subgroup as a finite module with continuous action

For a finite `Λ`-module `M` with continuous action of `G` and a normal subgroup `N`, the
invariants `M^N` are stable under `G` and carry the restricted action; it is again continuous, so
`M^N` is a finite `Λ`-module with continuous `G`-action on which `N` acts trivially, and the
inclusion `M^N ⟶ M` is a morphism of such, natural in `M`.

## Main definitions

* `Stacks.EtaleCohomology.finiteTypeContinuousModuleNormalInvariants` — `M ↦ M^N`, a functor.
* `Stacks.EtaleCohomology.finiteTypeContinuousModuleNormalInvariantsι` — the inclusion
  `M^N ⟶ M`, natural in `M`.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.GroupCohomology

universe u v

namespace Stacks.EtaleCohomology

variable (Λ : Type u) [Ring Λ] [Finite Λ] {G : Type v} [Group G] [TopologicalSpace G]
  (N : Subgroup G) [N.Normal]

/-- The `N`-invariants of a representation, as a submodule. -/
def normalInvariantsSubmodule {P : Type*} [AddCommGroup P] [Module Λ P]
    (ρ : Representation Λ G P) : Submodule Λ P where
  carrier := {m | ∀ n ∈ N, ρ n m = m}
  zero_mem' n _ := map_zero _
  add_mem' {a b} ha hb n hn := by rw [map_add, ha n hn, hb n hn]
  smul_mem' c a ha n hn := by rw [map_smul, ha n hn]

omit [Finite Λ] [TopologicalSpace G] in
/-- `G` preserves the `N`-invariants, `N` being normal. -/
theorem normalInvariantsSubmodule_smul {P : Type*} [AddCommGroup P] [Module Λ P]
    (ρ : Representation Λ G P) (g : G) {m : P} (hm : m ∈ normalInvariantsSubmodule Λ N ρ) :
    ρ g m ∈ normalInvariantsSubmodule Λ N ρ := fun n hn ↦
  calc ρ n (ρ g m) = ρ g (ρ (g⁻¹ * n * g) m) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        group
    _ = ρ g m := by rw [hm _ (by simpa using ‹N.Normal›.conj_mem n hn g⁻¹)]

/-- The representation of `G` on the `N`-invariants. -/
def normalInvariantsRepresentation {P : Type*} [AddCommGroup P] [Module Λ P]
    (ρ : Representation Λ G P) : Representation Λ G (normalInvariantsSubmodule Λ N ρ) where
  toFun g := (ρ g).restrict (fun _ hm ↦ normalInvariantsSubmodule_smul Λ N ρ g hm)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- **`M^N` with the restricted `G`-action**, a finite `Λ`-module with continuous action. -/
def finiteTypeContinuousModuleNormalInvariantsObj
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) : FiniteTypeContinuousModule.{u, v, v} Λ G := by
  let ρ := finiteTypeContinuousModuleRepresentation Λ G M
  let A : Action (ModuleCat.{v} Λ) G :=
    { V := ModuleCat.of Λ (normalInvariantsSubmodule Λ N ρ)
      ρ :=
        { toFun := fun g ↦ End.of (ModuleCat.ofHom (normalInvariantsRepresentation Λ N ρ g))
          map_one' := End.ext (ModuleCat.hom_ext (map_one (normalInvariantsRepresentation Λ N ρ)))
          map_mul' g h := End.ext
            (ModuleCat.hom_ext (map_mul (normalInvariantsRepresentation Λ N ρ) g h)) } }
  letI : HasForget₂ (ModuleCat.{v} Λ) TopCat.{v} :=
    { forget₂ := forget (ModuleCat.{v} Λ) ⋙ TopCat.discrete
      forget_comp := rfl }
  refine ⟨⟨⟨A, ?_⟩, ⟨rfl⟩⟩, ?_⟩
  · refine (Action.isContinuous_def _).2 ?_
    have hM := (Action.isContinuous_def M.obj.obj.obj).mp M.obj.obj.property
    have : DiscreteTopology ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj A) := ⟨rfl⟩
    have : DiscreteTopology ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj
        M.obj.obj.obj) := ⟨rfl⟩
    have : DiscreteTopology ↑((forget₂ (ModuleCat.{v} Λ) TopCat.{v}).obj A.V) := ⟨rfl⟩
    refine continuous_prod_of_discrete_right.2 fun w => ?_
    refine continuous_discrete_rng.2 fun c => ?_
    let w' : normalInvariantsSubmodule Λ N ρ := w
    let c' : normalInvariantsSubmodule Λ N ρ := c
    let mT : G → ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj M.obj.obj.obj) :=
      fun g => ρ g (w' : M.obj.obj.obj.V)
    have hmT : Continuous mT := hM.comp (continuous_id.prodMk continuous_const)
    convert (isOpen_discrete
      ({(c' : M.obj.obj.obj.V)} : Set ↑((forget₂ (Action (ModuleCat.{v} Λ) G) TopCat.{v}).obj
        M.obj.obj.obj))).preimage hmT using 1
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subtype.ext_iff
  · have : Finite M.obj.obj.obj.V := (moduleCat_isFG_iff_finite Λ M.obj.obj.obj.V).1 M.property
    exact (Module.Finite.of_finite : Module.Finite Λ (normalInvariantsSubmodule Λ N ρ))

/-- **The inclusion `M^N ⟶ M`**, a morphism of finite `Λ`-modules with continuous `G`-action. -/
def finiteTypeContinuousModuleNormalInvariantsInclusion
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) :
    finiteTypeContinuousModuleNormalInvariantsObj Λ N M ⟶ M :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (normalInvariantsSubmodule Λ N
        (finiteTypeContinuousModuleRepresentation Λ G M)).subtype
      comm := fun g => by
        ext m
        rfl }))

omit [Finite Λ] [N.Normal] in
/-- A morphism of representations preserves `N`-invariants. -/
theorem normalInvariantsSubmodule_map {P Q : FiniteTypeContinuousModule.{u, v, v} Λ G} (φ : P ⟶ Q)
    {m : P.obj.obj.obj.V}
    (hm : m ∈ normalInvariantsSubmodule Λ N (finiteTypeContinuousModuleRepresentation Λ G P)) :
    φ.hom.hom.hom.hom m ∈
      normalInvariantsSubmodule Λ N (finiteTypeContinuousModuleRepresentation Λ G Q) :=
  fun n hn ↦ by
    have h := ConcreteCategory.congr_hom (φ.hom.hom.hom.comm n) m
    simp only [ConcreteCategory.comp_apply] at h
    change (Q.obj.obj.obj.ρ n).asHom.hom (φ.hom.hom.hom.hom m) = _
    rw [← h]
    exact congrArg _ (hm n hn)

/-- **The functor `M ↦ M^N`** on finite `Λ`-modules with continuous `G`-action. -/
def finiteTypeContinuousModuleNormalInvariants :
    FiniteTypeContinuousModule.{u, v, v} Λ G ⥤ FiniteTypeContinuousModule.{u, v, v} Λ G where
  obj M := finiteTypeContinuousModuleNormalInvariantsObj Λ N M
  map {P Q} φ := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (φ.hom.hom.hom.hom.hom.restrict
        (fun _ hm ↦ normalInvariantsSubmodule_map Λ N φ hm))
      comm := fun g => by
        ext m
        exact Subtype.ext (ConcreteCategory.congr_hom (φ.hom.hom.hom.comm g) m.1) }))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- **The inclusion `M^N ⟶ M`, natural in `M`.** -/
def finiteTypeContinuousModuleNormalInvariantsι :
    finiteTypeContinuousModuleNormalInvariants Λ N ⟶ 𝟭 _ where
  app M := finiteTypeContinuousModuleNormalInvariantsInclusion Λ N M
  naturality _ _ _ := by ext; rfl

/-- The inclusion `M^N ⟶ M` is injective. -/
theorem injective_finiteTypeContinuousModuleNormalInvariantsι
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) :
    Function.Injective ((finiteTypeContinuousModuleNormalInvariantsι Λ N).app M).hom.hom.hom.hom :=
  Subtype.val_injective

/-- `N` acts trivially on `M^N`. -/
theorem finiteTypeContinuousModuleNormalInvariants_rho_eq_one
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) (n : G) (hn : n ∈ N) :
    finiteTypeContinuousModuleRepresentation Λ G
      ((finiteTypeContinuousModuleNormalInvariants Λ N).obj M) n = 1 := by
  ext m
  exact Subtype.ext (m.2 n hn)

/-- The underlying module of `M^N` is the `N`-invariant submodule of `M`. -/
theorem range_finiteTypeContinuousModuleNormalInvariantsι
    (M : FiniteTypeContinuousModule.{u, v, v} Λ G) :
    Set.range ((finiteTypeContinuousModuleNormalInvariantsι Λ N).app M).hom.hom.hom.hom =
      (normalInvariantsSubmodule Λ N (finiteTypeContinuousModuleRepresentation Λ G M) :
        Set M.obj.obj.obj.V) :=
  Subtype.range_coe

end Stacks.EtaleCohomology
