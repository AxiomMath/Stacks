module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EdgeTensorMatchingCriterion

/-!
# Naturality of the multiplication of Tag 0G75 in the left factor

`Stacks.Cohomology.SupportedComplexes.supportedTensorPushMap` is the map
`K ⊗^L i_*R𝓗_Z(M) ⟶ i_*R𝓗_Z(K ⊗^L M)` of [Stacks, Tag 0G75] read on `X`. It is natural in `K`
for every morphism of the derived category: composed with the counit both sides are
`K ⊗^L` of the counit at `M` followed by the morphism, and composition with the counit is
injective on morphisms out of `K ⊗^L i_*R𝓗_Z(M)` by
`Stacks.Cohomology.SupportedComplexes.eq_supportedTensorPushMap`'s argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.SupportedComplexes
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)

universe u

namespace Stacks.DeRham.GysinCupHodge

/-- The algebra of `supportedTensorPushMap_naturality_left`, at variables. -/
private lemma counit_naturality_chase {C : Type*} [Category* C] {P P' Q Q' N N' : C}
    (a : P ⟶ P') (s : P' ⟶ N') (s₀ : P ⟶ N) (b : N ⟶ N') (ε : N' ⟶ Q') (ε₀ : N ⟶ Q)
    (t : Q ⟶ Q') (tK : P ⟶ Q) (tK' : P' ⟶ Q')
    (h₁ : tK' = s ≫ ε) (h₂ : tK = s₀ ≫ ε₀) (h₃ : b ≫ ε = ε₀ ≫ t) (h₄ : a ≫ tK' = tK ≫ t) :
    (a ≫ s) ≫ ε = (s₀ ≫ b) ≫ ε := by
  rw [Category.assoc, ← h₁, h₄, h₂, Category.assoc, Category.assoc, h₃]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The multiplication of [Stacks, Tag 0G75] on `X` is natural in the left factor**, for an
arbitrary morphism `f : K ⟶ K'` of `D(𝒪_X)`. -/
theorem supportedTensorPushMap_naturality_left
    {K K' : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))} (f : K ⟶ K')
    (M : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedTensorProductFunctor X.sheaf).map f).app ((derivedSupportedPushforward X Z hZ).obj M) ≫
        supportedTensorPushMap X Z hZ K' M =
      supportedTensorPushMap X Z hZ K M ≫
        (derivedSupportedPushforward X Z hZ).map
          (((derivedTensorProductFunctor X.sheaf).map f).app M) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  have := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).full
  have := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).faithful
  refine eq_of_comp_counit (derivedPushforwardAdjunction X Z hZ)
    (supportedTensorPushIso X Z hZ K M) _ _ ?_
  exact counit_naturality_chase _ _ _ _ _ _ _ _ _
    (tensor_map_counit_eq X Z hZ K' M) (tensor_map_counit_eq X Z hZ K M)
    ((derivedPushforwardAdjunction X Z hZ).counit.naturality
      (((derivedTensorProductFunctor X.sheaf).map f).app M))
    (((derivedTensorProductFunctor X.sheaf).map f).naturality
      ((derivedPushforwardAdjunction X Z hZ).counit.app M)).symm

end StandardModel

end Stacks.DeRham.GysinCupHodge
