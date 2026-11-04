module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictScalarsTensorModels
public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex

/-!
# `E ⊗^L 𝒢` has finite Tor dimension over `f⁻¹𝒪_Y`

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `E` a perfect object of `D(𝒪_X)` and `𝒢` a
bounded complex of `𝒪_X`-modules whose terms have support in a compact closed set and are flat as
`f⁻¹𝒪_Y`-modules.  Then `E ⊗^L_{𝒪_X} 𝒢`, read in `D(f⁻¹𝒪_Y)`, has finite Tor dimension.  This is
the Tor-dimension clause in the proof of Stacks 0DKJ.

## Main results

* `AlgebraicGeometry.Space.hasFiniteTorDimension_derivedScalarRestriction_derivedTensor`: for `E`
  perfect and `𝒢` bounded with terms supported in a compact closed set and flat over `f⁻¹𝒪_Y`, the
  object `E ⊗^L_{𝒪_X} 𝒢` of `D(f⁻¹𝒪_Y)` has finite Tor dimension.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The derived category of the modules on a slice of the small étale site, built from the abelian
structure named in `AlgebraicGeometry.Space.smallEtaleRingedSite_over_abelian`. -/
local instance (priority := 20000) sliceHasDerivedCategory'
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) :=
  @HasDerivedCategory.standard _ _ (smallEtaleRingedSite_over_abelian B S hS X.1 X.2 U)

/-- For `E` perfect and `𝒢` a bounded complex whose terms have support in a compact closed set and
are flat over `f⁻¹𝒪_Y`, the object `E ⊗^L_{𝒪_X} 𝒢` of `D(𝒪_X)`, read in `D(f⁻¹𝒪_Y)`, has finite
Tor dimension. -/
theorem hasFiniteTorDimension_derivedScalarRestriction_derivedTensor (f : X ⟶ Y)
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (T' : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (inverseImageRingedSite B S hS f))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (g₀ g₁ : ℤ)
    (hGb : ∀ q : ℤ, q < g₀ ∨ g₁ < q → IsZero (G.X q)) (Z : Set (points B S hS X.1))
    (hZc : IsCompact Z) (hZcl : IsClosed Z)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (hGflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) ((scalarRestriction B S hS f).obj (G.X q))) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T'
      ((derivedScalarRestriction B S hS f).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) := by
  obtain ⟨N, I, W, hW, hmodel⟩ :=
    exists_coversTop_uniform_tensor_models B S hS X T E hE G Z hZc hZcl
  refine ⟨-N + g₀, N + g₁, ?_⟩
  open Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall in
  refine hasTorAmplitude_restrictScalars_of_models
    (smallEtaleRingedSite B S hS X.1 X.2) (inverseImageRingedSite B S hS f).O
    (inverseImageStructureMap B S hS f) T' _ G N g₀ g₁ hGb hGflat W hW fun i =>
      (hmodel i).imp_right fun hout =>
        Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj _ fun n => ?_
  have : PreservesFiniteLimits
      (Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.restriction
        (smallEtaleRingedSite B S hS X.1 X.2) (W i)) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits.{u + 1, u, u, u} (W i)
  have : PreservesFiniteColimits
      (Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.restriction
        (smallEtaleRingedSite B S hS X.1 X.2) (W i)) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u, u, u} (W i)
  refine IsZero.of_iso ?_ ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.restriction
      (smallEtaleRingedSite B S hS X.1 X.2) (W i)) n).app _)
  exact isZero_over_of_forall_notMem_supportOfSheaf B S hS X _ (W i) fun z hz =>
    hout z (cohomologySupportedOn_derivedTensor B S hS X T E G Z hGZ n hz)

end AlgebraicGeometry.Space

end
