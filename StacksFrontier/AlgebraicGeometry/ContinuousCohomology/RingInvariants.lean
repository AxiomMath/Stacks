module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.Basic

/-!
# Invariants of continuous discrete modules over a possibly noncommutative ring

Let `R` be a ring, not necessarily commutative, and `G` a topological group. The `G`-invariants
`M^G` of a continuous discrete `R`-`G`-module form an `R`-submodule, functorially in `M`. The
functor `M ↦ M^G` is right adjoint to the functor giving an `R`-module the trivial `G`-action,
hence left exact. For commutative `R` it is the functor
`Stacks.ContinuousCohomology.continuousModuleInvariants` of `Rep`.

## Main definitions

* `Stacks.ContinuousCohomology.continuousModuleRingInvariants` — `M ↦ M^G`.
* `Stacks.ContinuousCohomology.continuousModuleTrivialFunctor` — the trivial action.
* `Stacks.ContinuousCohomology.continuousModuleTrivialInvariantsAdj` — the adjunction.
* `Stacks.ContinuousCohomology.continuousModuleRingInvariantsIso` — for `R` commutative, the
  comparison with `continuousModuleInvariants`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v w

namespace Stacks.ContinuousCohomology

open scoped Stacks.DiscreteModuleTopology

section Ring

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying `R`-module functor is faithful. -/
instance faithful_injectivesContinuousModuleUnderlying :
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Action.hom_ext _ _ h))

/-- The underlying `R`-module functor reflects isomorphisms, for any ring `R`. -/
theorem reflectsIsomorphisms_injectivesContinuousModuleUnderlying :
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).ReflectsIsomorphisms :=
  have : (Action.forget (ModuleCat.{w} R) G).ReflectsIsomorphisms :=
    ⟨fun f hf => by
      have : IsIso f.hom := hf
      exact Action.isIso_of_hom_isIso f⟩
  have : (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) ⋙
      Action.forget (ModuleCat.{w} R) G).ReflectsIsomorphisms :=
    reflectsIsomorphisms_comp _ _
  reflectsIsomorphisms_comp
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)))
    (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) ⋙
      Action.forget (ModuleCat.{w} R) G)

/-- The `R`-submodule of `G`-invariants of a continuous discrete `R`-`G`-module. -/
def continuousModuleInvariantsSubmodule (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    Submodule R M.obj.obj.V where
  carrier := {x | ∀ g : G, (M.obj.obj.ρ g).hom x = x}
  zero_mem' := fun _ ↦ map_zero _
  add_mem' := fun ha hb g ↦ by rw [map_add, ha g, hb g]
  smul_mem' := fun a _ hx g ↦ by rw [map_smul, hx g]

/-- **The `G`-invariants `M ↦ M^G`** of continuous discrete `R`-`G`-modules, for any ring `R`. -/
def continuousModuleRingInvariants :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤ ModuleCat.{w} R where
  obj M := ModuleCat.of R (continuousModuleInvariantsSubmodule R G M)
  map {M N} f := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨f.hom.hom.hom x.1, fun g ↦
        (ConcreteCategory.congr_hom (f.hom.hom.comm g) x.1).symm.trans
          (congrArg _ (x.2 g))⟩
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (map_smul _ _ _) }

/-- The invariants functor sends a morphism to its restriction to invariant vectors. -/
@[simp]
lemma continuousModuleRingInvariants_map_coe
    {M N : Stacks.Injectives.ContinuousModule.{u, v, w} R G} (f : M ⟶ N)
    (x : (continuousModuleRingInvariants R G).obj M) :
    (((continuousModuleRingInvariants R G).map f) x).1 = f.hom.hom.hom x.1 := rfl

/-- The invariants functor is additive. -/
instance continuousModuleRingInvariants_additive :
    (continuousModuleRingInvariants.{u, v, w} R G).Additive where
  map_add := by
    intros
    rfl

/-- An `R`-module with the trivial `G`-action, as a continuous discrete `R`-`G`-module. -/
def continuousModuleTrivialFunctor :
    ModuleCat.{w} R ⥤ Stacks.Injectives.ContinuousModule.{u, v, w} R G where
  obj N := ⟨⟨Action.trivial G N, by
      rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
      exact fun _ => continuous_const⟩, ⟨rfl⟩⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk { hom := f, comm := fun _ ↦ rfl })

/-- **Invariants are right adjoint to the trivial action.** -/
def continuousModuleTrivialInvariantsAdj :
    continuousModuleTrivialFunctor.{u, v, w} R G ⊣ continuousModuleRingInvariants.{u, v, w} R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv N M :=
        { toFun := fun φ ↦ ModuleCat.ofHom
            { toFun := fun n ↦ ⟨φ.hom.hom.hom n, fun g ↦
                (ConcreteCategory.congr_hom (φ.hom.hom.comm g) n).symm⟩
              map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
              map_smul' := fun _ _ ↦ Subtype.ext (map_smul _ _ _) }
          invFun := fun ψ ↦ ObjectProperty.homMk (ObjectProperty.homMk
            { hom := ψ ≫ ModuleCat.ofHom (continuousModuleInvariantsSubmodule R G M).subtype
              comm := fun g ↦ by
                ext n
                exact ((ψ n).2 g).symm })
          left_inv := fun φ ↦ rfl
          right_inv := fun ψ ↦ rfl }
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun _ _ ↦ rfl }

/-- The invariants functor is a right adjoint. -/
instance : (continuousModuleRingInvariants.{u, v, w} R G).IsRightAdjoint :=
  (continuousModuleTrivialInvariantsAdj R G).isRightAdjoint

/-- **Taking invariants is left exact.** -/
instance preservesFiniteLimits_continuousModuleRingInvariants :
    PreservesFiniteLimits (continuousModuleRingInvariants.{u, v, w} R G) :=
  inferInstance

end Ring

section CommRing

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- For a commutative ring the invariants are those of `Rep`. -/
def continuousModuleRingInvariantsIso :
    continuousModuleRingInvariants.{u, v, w} R G ≅ continuousModuleInvariants.{u, v, w} R G :=
  NatIso.ofComponents (fun _ ↦ LinearEquiv.toModuleIso
    { toFun := fun x ↦ ⟨x.1, fun g ↦ x.2 g⟩
      invFun := fun x ↦ ⟨x.1, fun g ↦ x.2 g⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl })
    (fun _ ↦ rfl)

end CommRing

end Stacks.ContinuousCohomology

end
