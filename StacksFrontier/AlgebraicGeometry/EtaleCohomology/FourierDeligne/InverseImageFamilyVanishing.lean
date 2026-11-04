module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# Vanishing is detected by inverse images along a jointly surjective family

For a family of morphisms `g a : T a ⟶ X` whose images cover `X` (for instance the geometric points
of `X`), a sheaf of `Λ`-modules on the small étale site of `X`, or an object of `D⁺(X_étale, Λ)`,
vanishes as soon as all of its inverse images along the `g a` do. This is how the vanishing of
`R pr! (pr⁻¹ K ⊗ L_ψ(c t))` off the antidiagonal in Fourier inversion is reduced to the geometric
fibres, where it is `RΓ_c(𝔸¹_Ω, M ⊗ L_ψ(c t)) = 0`.

## Main results

* `Stacks.EtaleCohomology.isZero_of_forall_isZero_etaleModuleInverseImage`.
* `Stacks.EtaleCohomology.isZero_of_forall_isZero_etaleModuleDerivedInverseImagePlus`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}} {ι : Type u} {T : ι → Scheme.{u}} (g : ∀ a, T a ⟶ X)
  (hg : ⋃ a, Set.range (g a).base = Set.univ)

include hg in
/-- **A sheaf of modules whose inverse images along a jointly surjective family vanish is zero**:
the endomorphism `0` becomes invertible after every inverse image, so it is invertible
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleInverseImage_family`). -/
theorem isZero_of_forall_isZero_etaleModuleInverseImage (F : EtaleModules.{u, 0} Λ X)
    (h : ∀ a, IsZero ((etaleModuleInverseImage.{u, 0} Λ (g a)).obj F)) : IsZero F := by
  have : IsIso (0 : F ⟶ F) := isIso_of_isIso_etaleModuleInverseImage_family Λ g hg 0 fun a => by
    rw [Functor.map_zero]
    exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨h a, h a⟩
  exact ((isIsoZero_iff_source_target_isZero _ _).1 this).1

include hg in
/-- **An object of `D⁺(X_étale, Λ)` whose inverse images along a jointly surjective family vanish
is zero**: inverse image is exact, so the inverse images of its cohomology sheaves vanish. -/
theorem isZero_of_forall_isZero_etaleModuleDerivedInverseImagePlus
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (h : ∀ a, IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (g a)).obj K)) : IsZero K := by
  have hq : ∀ q : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K) := fun q =>
    isZero_of_forall_isZero_etaleModuleInverseImage Λ g hg _ fun a =>
      (Functor.map_isZero (DerivedCategory.Plus.homologyFunctor _ q) (h a)).of_iso
        (etaleModuleDerivedInverseImagePlusHomologyIso Λ (g a) K q).symm
  have : IsIso (0 : K ⟶ K) := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro q
    rw [Functor.map_zero]
    exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hq q, hq q⟩
  exact ((isIsoZero_iff_source_target_isZero _ _).1 this).1

end Stacks.EtaleCohomology

end
