module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.CechPullbackFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsArbitraryBase
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsFunctorialModel
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.Homology.Perfect.FirstHomologyInjectiveDescent

/-!
# Comparing two descent conditions over an affine base

This file carries out, over an affine base `Spec A`, the argument of [Stacks, Tag 0BF1]: for
proper flat morphisms `f : X ⟶ Spec A` and `f' : X' ⟶ Spec A` of finite presentation, a morphism
`a : X' ⟶ X` over `Spec A`, a finitely presented `𝒪_X`-module `L` flat over `A` and a field-valued
point of `Spec A` at which `L` is trivial and `H¹(X₀, 𝒪) → H¹(X'₀, 𝒪)` is injective, it produces
an element `g` not vanishing at the point and finitely many elements `c` vanishing there, such that
over `D(g)`, the vanishing of the `c` is implied by the triviality of `a^* L`, and in turn produces
a global section of `L` which is nonzero on every fibre.

## Main results

* `AlgebraicGeometry.DescentLocusComparison.exists_affine_refinement`: an affine refinement of the
  inverse image of an affine cover, with affine finite intersections.
* `AlgebraicGeometry.DescentLocusComparison.homologyZeroLinearEquiv`: degree-zero cohomology of the
  alternating Čech complex is the module of global sections.

The elementwise criterion for injectivity on homology used with these results is
`HomologicalComplex.mono_homologyMap_iff_elementwise`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.DescentLocusComparison

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

/-- **An affine refinement of the inverse image of a cover, with affine intersections.** For
`a : X' ⟶ X`, an open cover `U` of `X`, and `X'` quasi-compact and separated over an affine
scheme, there is a finite family of affine opens of `X'` covering it, each contained in the inverse
image of a member of `U`, with affine finite intersections. -/
theorem exists_affine_refinement {A : Type u} [CommRing A] {X X' : Scheme.{u}} (a : X' ⟶ X)
    (f' : X' ⟶ Spec (.of A)) [QuasiCompact f'] [IsSeparated f'] {I : Type u}
    (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) :
    ∃ (I' : Type u) (_ : Fintype I') (_ : LinearOrder I') (W : I' → X'.Opens) (π : I' → I),
      (∀ k, W k ≤ a ⁻¹ᵁ U (π k)) ∧ (⊤ : X'.Opens) = ⨆ k, W k ∧ (∀ k, IsAffineOpen (W k)) ∧
        ∀ (r : ℕ) (s : Fin (r + 1) → I'), IsAffineOpen (⨅ k, W (s k)) := by
  classical
  have hcompact : CompactSpace ↥X' := QuasiCompact.compactSpace_of_compactSpace f'
  have hmem : ∀ x : X', ∃ i, a x ∈ U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 (hU ▸ trivial : a x ∈ (⨆ i, U i : X.Opens))
  choose ι hι using hmem
  have hV : ∀ x : X', ∃ V : X'.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ a ⁻¹ᵁ U (ι x) := fun x => by
    obtain ⟨_, ⟨V', hV', rfl⟩, hxV, hVle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (a ⁻¹ᵁ U (ι x) : Set X') from hι x) (a ⁻¹ᵁ U (ι x)).isOpen
    exact ⟨V', hV', hxV, hVle⟩
  choose V hVaff hxV hVle using hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X' => (V x : Set X'))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let W : ↥t → X'.Opens := fun k => V k.1
  have hWaff : ∀ k, IsAffineOpen (W k) := fun k => hVaff k.1
  refine ⟨↥t, inferInstance, linearOrderOfSTO WellOrderingRel, W, fun k => ι k.1,
    fun k => hVle k.1, ?_, hWaff, fun r s => Stacks.Cech.inter_isAffineOpen f' W hWaff s⟩
  refine le_antisymm (fun x _ => ?_) le_top
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk⟩, hxk⟩

/-- **Degree-zero cohomology of the alternating Čech complex is the module of global sections**,
for a cover of the whole scheme. -/
def homologyZeroLinearEquiv {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules) :
    letI := Stacks.Cech.sectionsModule f F ⊤
    (Stacks.Cech.alternatingCechModuleComplex f U F).homology 0 ≃ₗ[B] Γ(F, ⊤) :=
  letI := Stacks.Cech.sectionsModule f F ⊤
  letI := Stacks.Cech.cochainModule f U F 0
  letI := Stacks.Cech.cochainModule f U F 1
  have hUW : ∀ i, U i ≤ ⊤ := fun _ => le_top
  (kerEquivHomologyZero (Stacks.Cech.alternatingCechModuleComplex f U F)).symm.trans
    ((LinearEquiv.ofEq _ _ (by
      rw [Stacks.Cech.alternatingCechModuleComplex_d]
      exact (Stacks.Cech.range_sectionsToAlternatingₗ f U F hUW hU.le).symm)).trans
      (LinearEquiv.ofInjective _
        (Stacks.Cech.sectionsToAlternatingₗ_injective f U F hUW hU.le)).symm)

end AlgebraicGeometry.DescentLocusComparison

end
