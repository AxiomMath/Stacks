module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# Inverse image along a surjective morphism detects zero morphisms

Let `c : Y ⟶ X` be a surjective morphism of schemes. A morphism `φ` of sheaves of modules on
`X_étale` whose inverse image `c⁻¹ φ` vanishes is zero: `c⁻¹` is left exact, so it carries the
kernel of `φ` to the kernel of `c⁻¹ φ = 0`, an isomorphism, and inverse image along a family of
morphisms covering `X` reflects isomorphisms
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleInverseImage_family`). So the kernel of `φ` is
everything.

This transfers the existence of a nonzero morphism to a constant sheaf along the base change of
the fibres of `pr₂ : 𝔸¹ × 𝔸¹ → 𝔸¹` by an extension of algebraically closed fields, in the
Artin–Schreier half of the generic coinvariant vanishing in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.eq_zero_of_etaleModuleInverseImage_map_eq_zero_of_surjective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- **Inverse image along a surjective morphism detects zero morphisms** of sheaves of modules on
the small étale site. -/
theorem eq_zero_of_etaleModuleInverseImage_map_eq_zero_of_surjective {X Y : Scheme.{u}}
    (c : Y ⟶ X) [Surjective c] {F G : EtaleModules.{u, r} Λ X} (φ : F ⟶ G)
    (h : (etaleModuleInverseImage.{u, r} Λ c).map φ = 0) : φ = 0 := by
  let I := etaleModuleInverseImage.{u, r} Λ c
  have : PreservesFiniteLimits I := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ c
  have : IsIso (kernel.ι (I.map φ)) := kernel.ι_of_zero h
  have hI : IsIso (I.map (kernel.ι φ)) := by
    rw [← kernelComparison_comp_ι φ I]
    infer_instance
  have hcov : ⋃ _ : PUnit.{u + 1}, Set.range c.base = Set.univ := by
    rw [Set.iUnion_const]
    exact Set.range_eq_univ.2 c.surjective
  have : IsIso (kernel.ι φ) :=
    isIso_of_isIso_etaleModuleInverseImage_family Λ (fun _ : PUnit.{u + 1} => c) hcov
      (kernel.ι φ) fun _ => hI
  rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]

end Stacks.EtaleCohomology

end
