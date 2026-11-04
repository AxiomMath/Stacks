module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictionCoinducedEffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.GroupRingContinuousModule
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.ElementwiseEffaceable
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp

/-!
# `M ↦ H^i(G, M)` on finite `Γ`-modules, for a subgroup `G` of `Γ`

Let `φ : G → Γ` be a continuous homomorphism of compact groups, `Λ` a finite ring.
On the abelian category of finite `Λ`-modules with a continuous action of `Γ`, the continuous
cohomology of `G` with coefficients restricted along `φ` is a cohomological δ-functor
(`Stacks.ContinuousCohomology.restrictedCohomologyDelta`): the right derived functors of
`G`-invariants precomposed with the exact functor "restrict to `G`". When `φ` is a topological
embedding of profinite groups it is elementwise effaceable, by coinduction from open normal
subgroups of `Γ` (`Stacks.ContinuousCohomology.exists_map_res_coindUnit_eq_zero`), hence a
universal δ-functor.

For `φ : π₁(X_{k̄}) → π₁(X)` this is the right-hand side `H^i(π₁(X_{k̄}), M)` of Tag 03VM.

## Main definitions

* `Stacks.ContinuousCohomology.restrictedCohomologyDelta` — the δ-functor.

## Main results

* `Stacks.ContinuousCohomology.elementwiseEffaceable_restrictedCohomologyDelta`.
* `Stacks.ContinuousCohomology.isUniversal_restrictedCohomologyDelta`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe w

namespace Stacks.ContinuousCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] [Finite Λ] {G Γ : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] (φ : G →ₜ* Γ)

/-- The finite `Λ`-modules with a continuous `Γ`-action, read as continuous discrete
`Λ`-`G`-modules through `φ`. -/
abbrev finiteTypeContinuousModuleToRes :
    FiniteTypeContinuousModule.{0, w, w} Λ Γ ⥤ Stacks.Injectives.ContinuousModule.{0, w, w} Λ G :=
  finiteTypeContinuousModuleι.{0, w, w} Λ Γ ⋙ continuousModuleRes.{0, w, w} Λ φ

omit [Finite Λ] [IsTopologicalGroup G] [CompactSpace G] [IsTopologicalGroup Γ]
  [CompactSpace Γ] in
/-- Restricting to `G` does not change the underlying module. -/
theorem finiteTypeContinuousModuleToRes_comp_underlying :
    finiteTypeContinuousModuleToRes Λ φ ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ G =
      finiteTypeContinuousModuleι.{0, w, w} Λ Γ ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ Γ :=
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- Restriction to `G` preserves finite limits: the underlying module functor of `G`-modules
reflects them, and the composite is the underlying module functor of `Γ`-modules. -/
theorem preservesFiniteLimits_finiteTypeContinuousModuleToRes :
    PreservesFiniteLimits (finiteTypeContinuousModuleToRes Λ φ) := by
  have := preservesFiniteLimits_finiteTypeContinuousModuleι.{0, w, w} Λ Γ
  have := preservesFiniteLimits_continuousModuleToModuleCat.{0, w, w} Λ Γ
  have := preservesFiniteLimits_continuousModuleToModuleCat.{0, w, w} Λ G
  have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{0, w, w} Λ G
  have : PreservesFiniteLimits (finiteTypeContinuousModuleToRes Λ φ ⋙
      Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ G) :=
    comp_preservesFiniteLimits (finiteTypeContinuousModuleι.{0, w, w} Λ Γ)
      (Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ Γ)
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ G)

omit [IsTopologicalGroup G] [CompactSpace G] [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- Restriction to `G` preserves finite colimits. -/
theorem preservesFiniteColimits_finiteTypeContinuousModuleToRes :
    PreservesFiniteColimits (finiteTypeContinuousModuleToRes Λ φ) := by
  have := preservesFiniteColimits_finiteTypeContinuousModuleι.{0, w, w} Λ Γ
  have := preservesFiniteColimits_continuousModuleToModuleCat.{0, w, w} Λ Γ
  have := preservesFiniteColimits_continuousModuleToModuleCat.{0, w, w} Λ G
  have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{0, w, w} Λ G
  have : PreservesFiniteColimits (finiteTypeContinuousModuleToRes Λ φ ⋙
      Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ G) :=
    comp_preservesFiniteColimits (finiteTypeContinuousModuleι.{0, w, w} Λ Γ)
      (Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ Γ)
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (Stacks.Injectives.continuousModuleUnderlying.{0, w, w} Λ G)

/-- Restriction to `G` is additive, being exact. -/
instance additive_finiteTypeContinuousModuleToRes :
    (finiteTypeContinuousModuleToRes Λ φ).Additive :=
  have := preservesFiniteLimits_finiteTypeContinuousModuleToRes Λ φ
  Functor.additive_of_preserves_binary_products _

/-- **The δ-functor `M ↦ H^i(G, M)` on finite `Λ`-modules with continuous `Γ`-action.** The right
derived functors of `G`-invariants, precomposed with restriction along `φ`. -/
def restrictedCohomologyDelta :
    DeltaFunctor (FiniteTypeContinuousModule.{0, w, w} Λ Γ) (ModuleCat.{w} Λ) :=
  have := preservesFiniteLimits_finiteTypeContinuousModuleToRes Λ φ
  have := preservesFiniteColimits_finiteTypeContinuousModuleToRes Λ φ
  (invariantsDelta.{0, w, w} Λ (G := G)).precomp (finiteTypeContinuousModuleToRes Λ φ)

omit [CompactSpace G] [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- The degree-`n` component of `Stacks.ContinuousCohomology.restrictedCohomologyDelta` is
`M ↦ Hⁿ(G, M)`. -/
theorem restrictedCohomologyDelta_functor (n : ℕ) :
    (restrictedCohomologyDelta Λ φ).functor n =
      finiteTypeContinuousModuleToRes Λ φ ⋙ (invariantsDelta.{0, w, w} Λ (G := G)).functor n :=
  rfl

variable [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace Γ]

/-- **`M ↦ H^i(G, M)` is elementwise effaceable on finite `Γ`-modules**, for `φ` a topological
embedding of profinite groups: a class dies in the coinduced module `Coind_U M`
(`Stacks.ContinuousCohomology.exists_map_res_coindUnit_eq_zero`), which is again finite since
`Γ ⧸ U` is. -/
theorem elementwiseEffaceable_restrictedCohomologyDelta (hφ : Topology.IsInducing φ) :
    (restrictedCohomologyDelta Λ φ).ElementwiseEffaceable where
  exists_mono {M} {n} ξ := by
    obtain ⟨U, hU⟩ := exists_map_res_coindUnit_eq_zero.{0, w, w} Λ φ hφ n
      ((finiteTypeContinuousModuleι.{0, w, w} Λ Γ).obj M) ξ
    have : Finite (Γ ⧸ (U.toOpenSubgroup : Subgroup Γ)) := inferInstance
    have hFG : continuousModuleIsFG.{0, w, w} Λ Γ
        ((coind.{0, w, w} Λ U.toOpenSubgroup).obj
          ((finiteTypeContinuousModuleι.{0, w, w} Λ Γ).obj M)) := by
      have : Module.Finite Λ M.obj.obj.obj.V := M.property
      show Module.Finite Λ (Γ ⧸ (U.toOpenSubgroup : Subgroup Γ) → M.obj.obj.obj.V)
      infer_instance
    let N : FiniteTypeContinuousModule.{0, w, w} Λ Γ := ⟨_, hFG⟩
    let u : M ⟶ N := ObjectProperty.homMk (coindUnit.{0, w, w} Λ U.toOpenSubgroup
      ((finiteTypeContinuousModuleι.{0, w, w} Λ Γ).obj M))
    refine ⟨N, u, ?_, hU⟩
    have : Mono ((finiteTypeContinuousModuleι.{0, w, w} Λ Γ).map u) :=
      inferInstanceAs (Mono (coindUnit.{0, w, w} Λ U.toOpenSubgroup _))
    exact (finiteTypeContinuousModuleι.{0, w, w} Λ Γ).mono_of_mono_map this

/-- **`M ↦ H^i(G, M)` is a universal δ-functor** on finite `Γ`-modules. -/
theorem isUniversal_restrictedCohomologyDelta (hφ : Topology.IsInducing φ) :
    (restrictedCohomologyDelta Λ φ).IsUniversal :=
  have := elementwiseEffaceable_restrictedCohomologyDelta Λ φ hφ
  DeltaFunctor.isUniversal_of_elementwiseEffaceable _

end Stacks.ContinuousCohomology

end
