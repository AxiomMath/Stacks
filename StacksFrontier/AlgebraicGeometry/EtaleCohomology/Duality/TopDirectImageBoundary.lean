module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyConstantUnibranch
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition

/-!
# `R^q f̄_*` does not see a boundary which is finite over the base

Let `f̄ : X ⟶ S`, `j : U ⟶ X` an open immersion with closed complement `i : Z ⟶ X` such that
`i ≫ f̄` is finite. For a sheaf `F` of `Λ`-modules on `X`, the short exact sequence
`0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0` and the vanishing of `R^q f̄_*(i_* M) = R^q (f̄ ∘ i)_* M` for
`q ≥ 1` (the morphism `f̄ ∘ i` is finite, so its direct image is exact) show that
`R^q f̄_*(j_! j⁻¹ F) → R^q f̄_* F` is an isomorphism for `q ≥ 2`
(`Stacks.EtaleCohomology.isIso_singleHomology_map_extensionByZero_counit`).

## Main results

* `Stacks.EtaleCohomology.isZero_singleHomology_directImage_of_isFinite`.
* `Stacks.EtaleCohomology.isIso_singleHomology_map_extensionByZero_counit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ]

/-- **`R^q f̄_*(i_* M) = 0` for `q ≠ 0` when `f̄ ∘ i` is finite**: `Rf̄_* ∘ Ri_* ≅ R(f̄ ∘ i)_*`,
and both `i` and `f̄ ∘ i` are integral, so their derived direct images are their direct images. -/
theorem isZero_singleHomology_directImage_of_isFinite {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsIntegralHom i] (f : X ⟶ S) [IsIntegralHom (i ≫ f)] (M : EtaleModules.{u, 0} Λ Z)
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((singleHomology (etaleModuleDerivedDirectImage.{u, 0} Λ f) q).obj
      ((etaleModuleDirectImage.{u, 0} Λ i).obj M)) := by
  obtain ⟨e₁⟩ := nonempty_derivedDirectImage_singleFunctor_iso_of_isIntegralHom i Λ M
  obtain ⟨e₂⟩ := nonempty_derivedDirectImage_singleFunctor_iso_of_isIntegralHom (i ≫ f) Λ M
  let e : DerivedCategory.Plus.Q.obj ((singlePlus (EtaleModules.{u, 0} Λ X)).obj
        ((etaleModuleDirectImage.{u, 0} Λ i).obj M)) ≅
      (etaleModuleDerivedDirectImage.{u, 0} Λ i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) :=
    (StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} Λ X)).app _ ≪≫
      e₁.symm
  let e' := (etaleModuleDerivedDirectImage.{u, 0} Λ f).mapIso e ≪≫
    ((etaleModuleDerivedDirectImageComp.{u, 0} Λ i f (i ≫ f) rfl).app _).symm ≪≫ e₂
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e')
  rcases lt_or_gt_of_ne hq with h | h
  · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q h
  · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q h

/-- **`R^q f̄_*(j_! j⁻¹ F) ≅ R^q f̄_* F` for `q ≥ 2`** when the complement `Z` of `U` is finite
over `S`: the long exact sequence of `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0`. -/
theorem isIso_singleHomology_map_extensionByZero_counit {Z U X S : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (f : X ⟶ S) [IsIntegralHom (i ≫ f)]
    (F : EtaleModules.{u, 0} Λ X) (q : ℤ) (hq : 2 ≤ q) :
    IsIso ((singleHomology (etaleModuleDerivedDirectImage.{u, 0} Λ f) q).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app F)) := by
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ i j hij F
  let Φ := etaleModuleDerivedDirectImage.{u, 0} Λ f
  have h₃ : ∀ p : ℤ, p ≠ 0 → IsZero ((singleHomology Φ p).obj
      ((etaleModuleDirectImage.{u, 0} Λ i).obj ((etaleModuleInverseImage.{u, 0} Λ i).obj F))) :=
    fun p hp => isZero_singleHomology_directImage_of_isFinite Λ i f _ p hp
  have hmono : Mono ((singleHomology Φ q).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app F)) :=
    (singleHomology_exact₁ Φ hS (q - 1) q (by omega)).mono_g
      ((h₃ (q - 1) (by omega)).eq_of_src _ _)
  have hepi : Epi ((singleHomology Φ q).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app F)) :=
    (singleHomology_exact₂ Φ hS q).epi_f ((h₃ q (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Stacks.EtaleCohomology

end
