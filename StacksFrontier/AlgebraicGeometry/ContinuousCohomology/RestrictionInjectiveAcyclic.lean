module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictionCoinducedEffacement
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons

/-!
# Restriction to a closed subgroup carries injectives to invariants-acyclic modules

Let `φ : G → Γ` be a continuous homomorphism of profinite groups which is a topological embedding,
and `R` a ring. For an injective continuous discrete `R`-`Γ`-module `I`, the restriction of `I` to
`G` has no higher cohomology: `Hⁿ⁺¹(G, res I) = 0`. Every class of `Hⁿ⁺¹(G, res I)` dies in
`Hⁿ⁺¹(G, res Coind_U I)` for an open normal subgroup `U` of `Γ`
(`Stacks.ContinuousCohomology.exists_map_res_coindUnit_eq_zero`), and the embedding
`I ⟶ Coind_U I` of the constant functions splits because `I` is injective.

Consequently `res I` is right acyclic for the invariants functor of `G`, and the canonical
transformation `R(inv_G ∘ res) ⟶ R(res) ⋙ R(inv_G)` of [Stacks, Tag 05T2] is an isomorphism
([Stacks, Tag 015M]). In the proof of [Stacks, Tag 03VM] this identifies `RΓ(G, res M)` with the
right derived functor of `M ↦ M^G` on `Γ`-modules, `G = π₁(X_{k̄})` and `Γ = π₁(X)`.

## Main results

* `Stacks.ContinuousCohomology.isZero_rightDerived_res_of_injective` — `Hⁿ⁺¹(G, res I) = 0`.
* `Stacks.ContinuousCohomology.rightAcyclic_res_of_injective` — `res I` is right acyclic for the
  invariants of `G`.
* `Stacks.ContinuousCohomology.rightDerivedFunctorPlusResCompIso` — `R(inv_G ∘ res) ≅ R(res) ⋙
  R(inv_G)`, with the canonical transformation as its `hom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u v w

namespace Stacks.ContinuousCohomology

section Exact

variable (R : Type u) [Ring R] {G Γ : Type v} [Group G] [TopologicalSpace G]
  [Group Γ] [TopologicalSpace Γ] (φ : G →ₜ* Γ)

/-- Restriction along `φ` preserves finite limits: the underlying module functor of `G`-modules
reflects them, and restriction followed by it is the underlying module functor of `Γ`-modules. -/
theorem preservesFiniteLimits_continuousModuleRes :
    PreservesFiniteLimits (continuousModuleRes.{u, v, max u v w} R φ) := by
  have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{u, v, max u v w} R G
  have := preservesFiniteLimits_continuousModuleToModuleCat.{u, v, max u v w} R Γ
  have := preservesFiniteLimits_continuousModuleToModuleCat.{u, v, max u v w} R G
  have : PreservesFiniteLimits (continuousModuleRes.{u, v, max u v w} R φ ⋙
      Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G) :=
    inferInstanceAs (PreservesFiniteLimits
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R Γ))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G)

/-- Restriction along `φ` preserves finite colimits. -/
theorem preservesFiniteColimits_continuousModuleRes :
    PreservesFiniteColimits (continuousModuleRes.{u, v, max u v w} R φ) := by
  have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{u, v, max u v w} R G
  have := preservesFiniteColimits_continuousModuleToModuleCat.{u, v, max u v w} R Γ
  have := preservesFiniteColimits_continuousModuleToModuleCat.{u, v, max u v w} R G
  have : PreservesFiniteColimits (continuousModuleRes.{u, v, max u v w} R φ ⋙
      Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G) :=
    inferInstanceAs (PreservesFiniteColimits
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R Γ))
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u v w} R G)

/-- Restriction along `φ` is additive, being exact. -/
instance additive_continuousModuleRes : (continuousModuleRes.{u, v, max u v w} R φ).Additive :=
  have := preservesFiniteLimits_continuousModuleRes.{u, v, w} R φ
  Functor.additive_of_preserves_binary_products _

/-- The composite of restriction along `φ` with the invariants of `G` is additive. -/
instance additive_continuousModuleRes_comp_invariants :
    (continuousModuleRes.{u, v, max u v w} R φ ⋙
      continuousModuleRingInvariants.{u, v, max u v w} R G).Additive where
  map_add {_ _ f g} := by
    simp only [Functor.comp_map]
    rw [Functor.map_add, Functor.map_add]

end Exact

variable (R : Type u) [Ring R] {G Γ : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] (φ : G →ₜ* Γ)
  [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace Γ]

/-- The category of continuous discrete `R`-`G`-modules has enough injectives. -/
local instance (priority := 3000) enoughInjectives_res_source :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{u, v, w} R G

/-- The category of continuous discrete `R`-`Γ`-modules has enough injectives. -/
local instance (priority := 3000) enoughInjectives_res_target :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ) :=
  Stacks.ContinuousCohomology.enoughInjectives.{u, v, w} R Γ

/-- **`Hⁿ⁺¹(G, res I) = 0` for an injective `Γ`-module `I`**, for `φ : G → Γ` a topological
embedding of profinite groups. -/
theorem isZero_rightDerived_res_of_injective (hφ : Topology.IsInducing φ) (n : ℕ)
    (I : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ) [Injective I] :
    IsZero (((continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerived (n + 1)).obj
      ((continuousModuleRes.{u, v, max u v w} R φ).obj I)) := by
  let F := (continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerived (n + 1)
  let res := continuousModuleRes.{u, v, max u v w} R φ
  suffices h : ∀ c : F.obj (res.obj I), c = 0 by
    have : Subsingleton (F.obj (res.obj I)) := ⟨fun a b ↦ (h a).trans (h b).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  intro c
  obtain ⟨U, hU⟩ := exists_map_res_coindUnit_eq_zero.{u, v, w} R φ hφ n I c
  let ι := coindUnit.{u, v, w} R U.toOpenSubgroup I
  have hs : ι ≫ Injective.factorThru (𝟙 I) ι = 𝟙 I := Injective.comp_factorThru _ _
  have hc : F.map (res.map (ι ≫ Injective.factorThru (𝟙 I) ι)) c = c := by
    rw [hs, res.map_id, F.map_id]; rfl
  rw [← hc, res.map_comp, F.map_comp, ModuleCat.comp_apply]
  change F.map (res.map (Injective.factorThru (𝟙 I) ι)) (F.map (res.map ι) c) = 0
  rw [show F.map (res.map ι) c = 0 from hU, map_zero]

variable [HasDerivedCategory (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)]
  [HasDerivedCategory (ModuleCat.{max u v w} R)]

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The restriction of an injective `Γ`-module is right acyclic for the invariants of `G`.** -/
theorem rightAcyclic_res_of_injective (hφ : Topology.IsInducing φ)
    (I : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ) [Injective I] :
    (continuousModuleRingInvariants.{u, v, max u v w} R G).rightAcyclic
      ((continuousModuleRes.{u, v, max u v w} R φ).obj I) := by
  rw [rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa using isZero_rightDerived_res_of_injective.{u, v, w} R φ hφ n I

variable [HasDerivedCategory (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ)]

/-- **`R(inv_G ∘ res) ≅ R(res) ⋙ R(inv_G)`** on bounded below derived categories, for `φ : G → Γ`
a topological embedding of profinite groups: the canonical transformation of [Stacks, Tag 05T2] is
invertible because restriction carries injective `Γ`-modules to `inv_G`-acyclic `G`-modules
([Stacks, Tag 015M]). -/
def rightDerivedFunctorPlusResCompIso (hφ : Topology.IsInducing φ) :
    (continuousModuleRes.{u, v, max u v w} R φ ⋙
        continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerivedFunctorPlus ≅
      (continuousModuleRes.{u, v, max u v w} R φ).rightDerivedFunctorPlus ⋙
        (continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ _
    (fun I hI ↦ haveI := hI; rightAcyclic_res_of_injective.{u, v, w} R φ hφ I)

/-- The `hom` of `rightDerivedFunctorPlusResCompIso` is the canonical transformation
`Functor.rightDerivedFunctorPlusComp` from `R(inv_G ∘ res)` to `R(res) ⋙ R(inv_G)`. -/
theorem rightDerivedFunctorPlusResCompIso_hom (hφ : Topology.IsInducing φ) :
    (rightDerivedFunctorPlusResCompIso.{u, v, w} R φ hφ).hom =
      Functor.rightDerivedFunctorPlusComp (continuousModuleRes.{u, v, max u v w} R φ)
        (continuousModuleRingInvariants.{u, v, max u v w} R G) :=
  rfl

end Stacks.ContinuousCohomology

end
