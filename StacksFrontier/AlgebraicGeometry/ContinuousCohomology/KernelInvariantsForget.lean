module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelInvariants
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictionInjectiveAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition

/-!
# Forgetting the action of the quotient on `RH⁰(G, -)`

Let `π : Γ → Q` be a continuous surjection of profinite groups and `φ : G → Γ` a topological
embedding with image the kernel of `π`. The derived invariants
`RH⁰(G, -) : D⁺(Mod_{R,Γ}) ⥤ D⁺(Mod_{R,Q})` of `Stacks.GroupCohomology.derivedKernelInvariants`
carry the residual action of `Q`; forgetting it gives back the derived invariants of `G` acting
through `φ`:

`U(RH⁰(G, M)) ≅ RΓ(G, res_φ M)` in `D⁺(R)`,

naturally in `M ∈ D⁺(Mod_{R,Γ})`. Indeed `U ∘ H⁰(G, -) = H⁰(G, -) ∘ res_φ` on modules, the
underlying-module functor `U` is exact (so every object is acyclic for it), and restriction along
`φ` is exact and carries injective `Γ`-modules to `G`-acyclic ones
(`Stacks.ContinuousCohomology.rightDerivedFunctorPlusResCompIso`, Tag 015M).

The groups `G` and `Γ` live one universe above `Q` and the modules in the universe of `G`, which
is the shape of `π₁(X_k̄) → π₁(X) → Aut(k̄/k)` with the representations of Tag 0DV5; this keeps
enough injectives available on both sides without ambiguous universe constraints.

## Main results

* `Stacks.ContinuousCohomology.kernelInvariantsForgetIso`: `U ∘ H⁰(G, -) ≅ H⁰(G, -) ∘ res_φ`.
* `Stacks.ContinuousCohomology.derivedKernelInvariantsForgetIso`: the derived version.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u v

namespace Stacks.ContinuousCohomology

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [Ring R] {G Γ : Type (v + 1)} {Q : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group Γ]
  [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
  (φ : G →ₜ* Γ) (π : Γ →ₜ* Q) (hπ : Function.Surjective π)
  (hφπ : (φ : G →* Γ).range = (π : Γ →* Q).ker)

/-- Enough injectives for `G`-modules, pinned at the coefficient universe used here. -/
local instance (priority := 3000) enoughInjectives_kernelInvariantsForget_sub :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{u, v + 1, max u (v + 1)} R G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{u, v + 1, 0} R G

/-- Enough injectives for `Γ`-modules, pinned at the coefficient universe used here. -/
local instance (priority := 3000) enoughInjectives_kernelInvariantsForget_group :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{u, v + 1, max u (v + 1)} R Γ) :=
  Stacks.ContinuousCohomology.enoughInjectives.{u, v + 1, 0} R Γ

/-- Enough injectives for `Q`-modules, pinned at the coefficient universe used here. -/
local instance (priority := 3000) enoughInjectives_kernelInvariantsForget_quotient :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{u, v, max u (v + 1)} R Q) :=
  Stacks.ContinuousCohomology.enoughInjectives.{u, v, v + 1} R Q

/-- Restriction of `Γ`-modules to `G`-modules along `φ` is additive. -/
local instance (priority := 3000) additive_res_kernelInvariantsForget :
    (continuousModuleRes.{u, v + 1, max u (v + 1)} R φ).Additive :=
  additive_continuousModuleRes.{u, v + 1, 0} R φ

/-- Restriction of `Γ`-modules to `G`-modules along `φ` preserves finite limits. -/
local instance (priority := 3000) preservesFiniteLimits_res_kernelInvariantsForget :
    PreservesFiniteLimits (continuousModuleRes.{u, v + 1, max u (v + 1)} R φ) :=
  preservesFiniteLimits_continuousModuleRes.{u, v + 1, 0} R φ

/-- Restriction of `Γ`-modules to `G`-modules along `φ` preserves finite colimits. -/
local instance (priority := 3000) preservesFiniteColimits_res_kernelInvariantsForget :
    PreservesFiniteColimits (continuousModuleRes.{u, v + 1, max u (v + 1)} R φ) :=
  preservesFiniteColimits_continuousModuleRes.{u, v + 1, 0} R φ

/-- The underlying-module functor on `Q`-modules preserves finite limits. -/
local instance (priority := 3000) preservesFiniteLimits_underlying_kernelInvariantsForget :
    PreservesFiniteLimits
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q) :=
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{u, v, max u (v + 1)} R Q

/-- The underlying-module functor on `Q`-modules preserves finite colimits. -/
local instance (priority := 3000) preservesFiniteColimits_underlying_kernelInvariantsForget :
    PreservesFiniteColimits
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q) :=
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{u, v, max u (v + 1)}
    R Q

/-- The underlying-module functor on `Q`-modules is an additive functor. -/
local instance (priority := 3000) additive_underlying_kernelInvariantsForget :
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q).Additive where
  map_add := rfl

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [IsTopologicalGroup Q] [T2Space Q] in
include hφπ in
/-- The invariants under the kernel of `π` are the invariants of `G` acting through `φ`. -/
lemma kernelInvariants_eq_invariantsSubmodule
    (M : Stacks.Injectives.ContinuousModule.{u, v + 1, max u (v + 1)} R Γ) :
    kernelInvariants R π M = continuousModuleInvariantsSubmodule R G
      ((continuousModuleRes.{u, v + 1, max u (v + 1)} R φ).obj M) := by
  ext x
  change (∀ γ : Γ, π γ = 1 → (M.obj.obj.ρ γ).hom x = x) ↔ ∀ g : G, (M.obj.obj.ρ (φ g)).hom x = x
  constructor
  · intro h g
    exact h _ (show (φ : G →* Γ) g ∈ (π : Γ →* Q).ker from hφπ ▸ ⟨g, rfl⟩)
  · intro h γ hγ
    obtain ⟨g, rfl⟩ : γ ∈ (φ : G →* Γ).range := hφπ ▸ hγ
    exact h g

include hφπ in
/-- **`U ∘ H⁰(G, -) ≅ H⁰(G, -) ∘ res_φ`**: forgetting the action of `Q` on the invariants under
the kernel of `π` gives the invariants of `G`. -/
def kernelInvariantsForgetIso :
    kernelInvariantsFunctor.{u, v + 1, v, max u (v + 1)} R π hπ ⋙
        Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q ≅
      continuousModuleRes.{u, v + 1, max u (v + 1)} R φ ⋙
        continuousModuleRingInvariants.{u, v + 1, max u (v + 1)} R G :=
  NatIso.ofComponents
    (fun M ↦ (LinearEquiv.ofEq _ _ (kernelInvariants_eq_invariantsSubmodule.{u, v} R φ π
      hφπ M)).toModuleIso)
    (fun _ ↦ by
      ext
      rfl)

include hφπ in
/-- **`U(RH⁰(G, -)) ≅ RΓ(G, res_φ -)`** on bounded below derived categories: forgetting the
residual action of `Q` on the derived invariants under the kernel of `π` gives the derived
invariants of `G` acting through `φ`. -/
def derivedKernelInvariantsForgetIso (hφ : Topology.IsInducing φ) :
    derivedKernelInvariants.{u, v + 1, v, 0} R π hπ ⋙
        (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R
          Q).mapDerivedCategoryPlus ≅
      (continuousModuleRes.{u, v + 1, max u (v + 1)} R φ).mapDerivedCategoryPlus ⋙
        (continuousModuleRingInvariants.{u, v + 1, max u (v + 1)} R G).rightDerivedFunctorPlus :=
  Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q)).symm ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic
      (kernelInvariantsFunctor.{u, v + 1, v, max u (v + 1)} R π hπ)
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q) fun _ _ ↦
      Functor.rightAcyclic_of_exact
        (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q) _).symm ≪≫
    Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso
      (kernelInvariantsFunctor.{u, v + 1, v, max u (v + 1)} R π hπ)
      (Stacks.Injectives.continuousModuleUnderlying.{u, v, max u (v + 1)} R Q)
      (continuousModuleRes.{u, v + 1, max u (v + 1)} R φ ⋙
        continuousModuleRingInvariants.{u, v + 1, max u (v + 1)} R G)
      (kernelInvariantsForgetIso.{u, v} R φ π hπ hφπ) ≪≫
    rightDerivedFunctorPlusResCompIso.{u, v + 1, 0} R φ hφ ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (continuousModuleRes.{u, v + 1, max u (v + 1)} R φ)) _

end Stacks.ContinuousCohomology

end
