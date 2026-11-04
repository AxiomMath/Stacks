module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.MeromorphicConstantModule.LocallyBijective

/-!
# Isomorphisms of higher direct images detected on a basis

Let `f : X ⟶ S` be a morphism of schemes and `φ : F ⟶ G` a morphism of `𝒪_X`-modules. If
`Hⁿ(f⁻¹(V), φ)` is an isomorphism for every member `V` of a basis of the opens of `S`, then
`Rⁿ f_* φ` is an isomorphism: by [Stacks, Tag 01E4] the higher direct image is the
sheafification of the presheaf `V ↦ Hⁿ(f⁻¹(V), -)`, and a morphism of presheaves of modules
which is bijective on the members of a basis has an isomorphism for its sheafification.

## Main results

* `Stacks.AffineHigherDirectImage.isIso_rightDerivedPlus_pushforward_map_of_isIso_hgroup`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImagePresheaf

universe u

namespace Stacks.AffineHigherDirectImage

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

attribute [local instance] RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **An isomorphism of higher direct images is detected on a basis of the target.** If
`Hⁿ(f⁻¹(V), φ)` is an isomorphism for every member `V` of a basis `B` of the opens of `S`, then
`Rⁿ f_* φ` is an isomorphism. -/
theorem isIso_rightDerivedPlus_pushforward_map_of_isIso_hgroup {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) {B : Set S.Opens} (hB : Opens.IsBasis B)
    (hiso : ∀ V ∈ B, IsIso ((Hfunctor X.ringCatSheaf (f ⁻¹ᵁ V) n).map φ)) :
    IsIso (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map φ) := by
  refine (NatIso.isIso_map_iff
    (higherDirectImage_iso_sheafify_preimageCohomology (Stacks.SchemeCohomology.hom f) n) φ).2 ?_
  refine
    Stacks.AlgebraicGeometry.MeromorphicConstantModule.isIso_sheafification_map_of_bijective_basis
    (B := (Subtype.val : B → S.Opens)) _ (by rwa [Subtype.range_coe]) _ fun V => ?_
  have h := (NatIso.isIso_map_iff
    (preimageCohomologyPresheaf_evaluation_iso (Stacks.SchemeCohomology.hom f) V.1 n) φ).2
      (hiso V.1 V.2)
  exact (ConcreteCategory.isIso_iff_bijective (C := AddCommGrpCat.{u}) _).1 h

end Stacks.AffineHigherDirectImage
