module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartPerfectComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineSmallEtaleTensorCohomology

/-!
# `H^i(Spec A, K ⊗^L M~) = H^i(K_A ⊗^L_A M)` for a perfect `K` on `(Spec A)_étale`

For a ring `A` and a perfect object `K` of `D(𝒪_{Spec A})` on the small étale site of `Spec A`,
there is a perfect complex `K_A` of `A`-modules with isomorphisms
`H^i(Spec A, K ⊗^L M~) ≅ H^i(K_A ⊗^L_A M)`, natural in the `A`-module `M` and compatible with the
boundary maps of short exact sequences, where `M~ = 𝒪_{Spec A} ⊗_A M` is
`AlgebraicGeometry.Space.affineBaseTilde`. This is the hypothesis `hperfect` of
`Space.ProperFlatLift.exists_isPerfect_derivedCohomology_iso_cotangentExt_of_comparison`.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_smallEtaleTensorCohomology_affineBaseTilde_addEquiv`.

## Implementation notes

It is `Space.exists_isPerfect_smallEtaleTensorCohomology_addEquiv_derivedCohomology_of_iso` at
`H = M ↦ M~`, identified with the associated module of the affine represented space `Spec A` read
through `A ≅ Γ(Spec A)` by `AlgebraicGeometry.Space.restrictScalarsRepresentedAffineAssociatedIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- One standard-model line, scoped to this file: the base declarations
-- `Deformation.Artin.derivedCohomology`, `Deformation.Artin.boundaryMap` and
-- `AlgebraicGeometry.Space.smallEtaleTensorCohomology` are stated in the model
-- `HasDerivedCategory.standard`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology
attribute [local instance 5000] SheafOfModules.instAbelian

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- **`H^i(Spec A, K ⊗^L M~) ≅ H^i(K_A ⊗^L_A M)` for a perfect `K` on `(Spec A)_étale`**: there is
a perfect complex `K_A` of `A`-modules and isomorphisms, natural in the `A`-module `M`, carrying
the boundary map of `K ⊗^L` a short exact sequence `0 → M₁~ → M₂~ → M₃~ → 0` to the boundary map of
`K_A ⊗^L_A (0 → M₁ → M₂ → M₃ → 0)`. -/
theorem exists_isPerfect_smallEtaleTensorCohomology_affineBaseTilde_addEquiv
    (K : smallEtaleModulesDerived B S hS
      (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))
    (hK : SmallEtaleIsPerfect B S hS K) :
    ∃ (K_A : DerivedCategory (ModuleCat.{u} A)) (_ : StacksDraft.Perfect.IsPerfect K_A)
      (γ : ∀ (M : ModuleCat.{u} A) (i : ℤ),
        smallEtaleTensorCohomology B S hS K ((affineBaseTilde A B S hS toS hA).obj M) i ≃+
          (Deformation.Artin.derivedCohomology A K_A i).obj M),
      (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ) (y),
        γ N i ((smallEtaleTensorCohomologyMap B S hS K
            ((affineBaseTilde A B S hS toS hA).map g) i) y) =
          (Deformation.Artin.derivedCohomology A K_A i).map g (γ M i y)) ∧
      (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
        (hT : (Sq.map (affineBaseTilde A B S hS toS hA)).ShortExact) (y),
        γ Sq.X₁ 2 ((smallEtaleTensorCohomologyDelta B S hS K
            (Sq.map (affineBaseTilde A B S hS toS hA)) hT 1 2 rfl) y) =
          Deformation.Artin.boundaryMap A K_A hSq (γ Sq.X₃ 1 y)) :=
  exists_isPerfect_smallEtaleTensorCohomology_addEquiv_derivedCohomology_of_iso
    (affineBaseTilde A B S hS toS hA)
    (restrictScalarsRepresentedAffineAssociatedIso A B S hS toS hA) K hK

end AlgebraicGeometry.Space

end
