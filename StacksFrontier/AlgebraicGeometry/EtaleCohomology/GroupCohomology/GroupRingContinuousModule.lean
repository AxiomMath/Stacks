module

public import Mathlib.RepresentationTheory.Rep.Iso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Modules over a group ring as modules with a continuous action

Let `Λ` be a finite commutative ring, `K` a finite group and `G` a topological group with a
homomorphism `π : G →* K` whose fibres are open. A module over the group ring `Λ[K]` is then a
`Λ`-module with an action of `G` through `K`, and that action is continuous for the discrete
topology. This file builds the resulting functor to
`Stacks.GroupCohomology.FiniteTypeContinuousModule` and proves it exact.

## Main definitions

* `Stacks.GroupCohomology.moduleMonoidAlgebraActionEquivalence`: the equivalence between modules
  over the group ring `Λ[K]` and `Λ`-modules with a `K`-action.
* `Stacks.GroupCohomology.groupRingFiniteTypeContinuousModule`: the resulting functor from the
  finitely generated modules over `Λ[K]` to the finite `Λ`-modules with a continuous
  `G`-action.

## Main results

* `Stacks.GroupCohomology.isContinuous_iff_isOpen_stabilizer`: an action of `G` on a `Λ`-module
  is continuous for the discrete topology exactly when every stabiliser is open.
* `Stacks.GroupCohomology.isContinuous_res_of_isOpen_fiber`: the action of `G` through `K` on a
  `Λ`-module is continuous for the discrete topology.
* `Stacks.GroupCohomology.preservesFiniteLimits_groupRingFiniteTypeContinuousModule` and
  `Stacks.GroupCohomology.preservesFiniteColimits_groupRingFiniteTypeContinuousModule`: that
  functor is exact.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r w

namespace Stacks.GroupCohomology

open scoped Stacks.DiscreteModuleTopology

/-- The equivalence between modules over the group ring `Λ[K]` and `Λ`-modules with an action
of `K`. -/
def moduleMonoidAlgebraActionEquivalence (Λ : Type r) [CommRing Λ] (K : Type w) [Group K] :
    ModuleCat.{w} (MonoidAlgebra Λ K) ≌ Action (ModuleCat.{w} Λ) K :=
  Rep.equivalenceModuleMonoidAlgebra.symm.trans (Rep.repIsoAction Λ K)

/-- An action of `G` on a `Λ`-module is continuous for the discrete topology exactly when every
stabiliser is open. -/
@[sga "4 IV 2.7.2" "special case"]
theorem isContinuous_iff_isOpen_stabilizer (Λ : Type r) [CommRing Λ] (G : Type w) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (X : Action (ModuleCat.{w} Λ) G) :
    X.IsContinuous ↔ ∀ x : X.V, IsOpen {g : G | (X.ρ g).hom x = x} :=
  continuousSMul_iff_stabilizer_isOpen

/-- Over a finite ring, the group ring of a finite group is finite. -/
instance finite_monoidAlgebra (Λ : Type r) [CommRing Λ] [Finite Λ] (K : Type w) [Group K]
    [Finite K] : Finite (MonoidAlgebra Λ K) :=
  have : Finite (K →₀ Λ) :=
    Finite.of_injective (fun f : K →₀ Λ ↦ (f : K → Λ)) DFunLike.coe_injective
  Finite.of_injective MonoidAlgebra.coeff fun a b h ↦ by
    cases a; cases b; exact congrArg _ h

section Reflects

variable (Λ : Type r) [CommRing Λ] [Finite Λ] (G : Type w) [Group G] [TopologicalSpace G]

omit [Finite Λ] in
/-- The underlying `Λ`-module functor on the `Λ`-modules with a continuous `G`-action reflects
isomorphisms. -/
theorem reflectsIsomorphisms_continuousModuleToModuleCat :
    (Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G).ReflectsIsomorphisms :=
  reflectsIsomorphisms_comp
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} Λ) (G := G)))
    (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} Λ) (G := G)) ⋙
      Action.forget (ModuleCat.{w} Λ) G)

/-- The underlying-module functor on the finite `Λ`-modules with a continuous `G`-action
reflects finite limits. -/
theorem reflectsFiniteLimits_finiteTypeContinuousModuleToModuleCat :
    ReflectsFiniteLimits (finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
      Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G) := by
  have h0 := reflectsIsomorphisms_continuousModuleToModuleCat.{r, w} Λ G
  have h1 := preservesFiniteLimits_finiteTypeContinuousModuleι.{r, w, w} Λ G
  have h2 := preservesFiniteLimits_continuousModuleToModuleCat.{r, w, w} Λ G
  have h3 : PreservesFiniteLimits (finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
      Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G) := comp_preservesFiniteLimits _ _
  infer_instance

/-- The underlying-module functor on the finite `Λ`-modules with a continuous `G`-action
reflects finite colimits. -/
theorem reflectsFiniteColimits_finiteTypeContinuousModuleToModuleCat :
    ReflectsFiniteColimits (finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
      Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G) := by
  have h0 := reflectsIsomorphisms_continuousModuleToModuleCat.{r, w} Λ G
  have h1 := preservesFiniteColimits_finiteTypeContinuousModuleι.{r, w, w} Λ G
  have h2 := preservesFiniteColimits_continuousModuleToModuleCat.{r, w, w} Λ G
  have h3 : PreservesFiniteColimits (finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
      Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G) :=
    comp_preservesFiniteColimits _ _
  infer_instance

end Reflects

section Functor

variable (Λ : Type r) [CommRing Λ] [Finite Λ] {K : Type w} [Group K] [Finite K]
  {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Finite Λ] [Finite K] in
/-- For a homomorphism `π : G →* K` with open fibres, the action of `G` through `π` on a
`Λ`-module with a `K`-action is continuous for the discrete topology. -/
theorem isContinuous_res_of_isOpen_fiber (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k}) (Y : Action (ModuleCat.{w} Λ) K) :
    ((Action.res (ModuleCat.{w} Λ) π).obj Y).IsContinuous := by
  rw [isContinuous_iff_isOpen_stabilizer]
  intro x
  have hcov : {g : G | (((Action.res (ModuleCat.{w} Λ) π).obj Y).ρ g).hom x = x} =
      ⋃ k ∈ {k : K | (Y.ρ k).hom x = x}, {g : G | π g = k} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    refine ⟨fun hg ↦ ⟨π g, hg, rfl⟩, ?_⟩
    rintro ⟨k, hk, hg⟩
    subst hg
    exact hk
  rw [hcov]
  exact isOpen_biUnion fun k _ ↦ hπ k

/-- The functor taking a finitely generated module over the group ring `Λ[K]` to the finite
`Λ`-module with the continuous action of `G` through `π : G →* K`. -/
def groupRingFiniteTypeContinuousModule (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k}) :
    (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)).FullSubcategory ⥤
      FiniteTypeContinuousModule.{r, w, w} Λ G :=
  ObjectProperty.lift _
    (ObjectProperty.lift _
      (ObjectProperty.lift _
        (ObjectProperty.ι (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)) ⋙
          (moduleMonoidAlgebraActionEquivalence Λ K).functor ⋙
            Action.res (ModuleCat.{w} Λ) π)
        fun _ ↦ isContinuous_res_of_isOpen_fiber Λ π hπ _)
      fun _ ↦ ⟨rfl⟩)
    fun M ↦ by
      have hfin : Finite (ToType M.obj) :=
        (moduleCat_isFG_iff_finite (MonoidAlgebra Λ K) M.obj).1 M.property
      exact (moduleCat_isFG_iff_finite Λ _).2 hfin

/-- The underlying `Λ`-module of the value of
`Stacks.GroupCohomology.groupRingFiniteTypeContinuousModule` is the underlying `Λ`-module of the
module over the group ring, on the nose. -/
theorem groupRingFiniteTypeContinuousModule_comp_toModuleCat (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k}) :
    groupRingFiniteTypeContinuousModule Λ π hπ ⋙
        finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
          Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G =
      ObjectProperty.ι (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)) ⋙
        (moduleMonoidAlgebraActionEquivalence Λ K).functor ⋙
          Action.forget (ModuleCat.{w} Λ) K :=
  rfl

/-- `Stacks.GroupCohomology.groupRingFiniteTypeContinuousModule` preserves finite limits. -/
theorem preservesFiniteLimits_groupRingFiniteTypeContinuousModule (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k}) :
    PreservesFiniteLimits (groupRingFiniteTypeContinuousModule Λ π hπ) := by
  have hR := reflectsFiniteLimits_finiteTypeContinuousModuleToModuleCat.{r, w} Λ G
  have hfg : PreservesFiniteLimits
      (ObjectProperty.ι (ModuleCat.isFG.{w} (MonoidAlgebra Λ K))) :=
    have {X Y : (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)).FullSubcategory} (f : X ⟶ Y) :=
      ObjectProperty.preservesKernels_ι (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)) f
    Functor.preservesFiniteLimits_of_preservesKernels _
  have hcomp : PreservesFiniteLimits (groupRingFiniteTypeContinuousModule Λ π hπ ⋙
      finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
        Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G) := by
    rw [groupRingFiniteTypeContinuousModule_comp_toModuleCat Λ π hπ]
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
      Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G)

/-- `Stacks.GroupCohomology.groupRingFiniteTypeContinuousModule` preserves finite colimits. -/
theorem preservesFiniteColimits_groupRingFiniteTypeContinuousModule (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k}) :
    PreservesFiniteColimits (groupRingFiniteTypeContinuousModule Λ π hπ) := by
  have hR := reflectsFiniteColimits_finiteTypeContinuousModuleToModuleCat.{r, w} Λ G
  have hfg : PreservesFiniteColimits
      (ObjectProperty.ι (ModuleCat.isFG.{w} (MonoidAlgebra Λ K))) :=
    have {X Y : (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)).FullSubcategory} (f : X ⟶ Y) :=
      ObjectProperty.preservesCokernels_ι (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)) f
    Functor.preservesFiniteColimits_of_preservesCokernels _
  have hcomp : PreservesFiniteColimits (groupRingFiniteTypeContinuousModule Λ π hπ ⋙
      finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
        Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G) := by
    rw [groupRingFiniteTypeContinuousModule_comp_toModuleCat Λ π hπ]
    exact comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (finiteTypeContinuousModuleι.{r, w, w} Λ G ⋙
      Stacks.Injectives.continuousModuleUnderlying.{r, w, w} Λ G)

end Functor

end Stacks.GroupCohomology

end
