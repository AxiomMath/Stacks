module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.InvertibleL.ConstructibleOfIsUnit

/-!
# Constructibility of the derived lower shriek, for coefficients killed by an invertible integer

Let `Λ : Type` be a Noetherian ring in which an integer `n > 0` vanishes, and let `n` be
invertible on the target. This file proves Tags 0GKZ and 0GL0 in this setting, by combining
Tag 0GKV for primes invertible on the base,
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit`,
with the results of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityAssembly`.
The hypothesis "`n` invertible on the target" is the one under which the source proves these
tags.

## Main results

* `Stacks.EtaleCohomology.lowerShriekConstructibleOnSheaves_affineLine_of_isUnit_natCast`:
  Tag 0GKZ.
* `isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_isUnit_natCast`:
  Tag 0GL0 on `D⁺_{tors, c}`.
* `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_isUnit_natCast`:
  Tag 0GL0 on `D_c`.

## References

* [Stacks Project, Tag 0GKZ](https://stacks.math.columbia.edu/tag/0GKZ)
* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **[Stacks, Tag 0GKZ] for a coefficient ring in `Type` killed by an integer invertible on the
base.** Let `Λ` be a Noetherian ring in which the integer `n > 0` vanishes, and `Y` an affine
scheme on which `n` is invertible. For every constructible sheaf `ℱ` of `Λ`-modules on `𝔸¹_Y`,
`Rf_! ℱ` has constructible cohomology sheaves, where `f : 𝔸¹_Y ⟶ Y` is the structure morphism
and `Rf_!` is computed through any compactification of `f`. -/
theorem lowerShriekConstructibleOnSheaves_affineLine_of_isUnit_natCast {n : ℕ} (hn0 : 0 < n)
    (hΛ : (n : Λ) = 0) (Y : Scheme.{u}) [IsAffine Y] (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    LowerShriekConstructibleOnSheaves Λ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) :=
  lowerShriekConstructibleOnSheaves_affineLine_of_isUnit_natCast_of_directImageZMod Λ
    (fun f _ _ _ hd ℓ _ hℓ q ↦
      isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit f hd ℓ hℓ q)
    hn0 hΛ Y hnY

/-- **[Stacks, Tag 0GL0] for `D⁺_{tors, c}` and a coefficient ring in `Type` killed by an integer
invertible on the target.** Let `f : X ⟶ Y` be a separated morphism of finite presentation of
quasi-compact and quasi-separated schemes, `j` a compactification of `f`, `Λ` a Noetherian ring
in which the integer `n > 0` vanishes, with `n` invertible on `Y`. Then `Rf_!` carries
`D⁺_{tors, c}(X_étale, Λ)` into `D⁺_{tors, c}(Y_étale, Λ)`. -/
theorem isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_isUnit_natCast
    {n : ℕ} (hn0 : 0 < n) (hΛ : (n : Λ) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (hK : IsTorsionConstructibleEtaleComplexPlus Λ K) :
    IsTorsionConstructibleEtaleComplexPlus Λ ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K) :=
  isTorsionConstructiblePlus_derivedLowerShriekUnbounded_of_isUnit_natCast_of_directImageZMod
    Λ (fun f _ _ _ hd ℓ _ hℓ q ↦
      isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit f hd ℓ hℓ q)
    hn0 hΛ f hnY j K hK

/-- **[Stacks, Tag 0GL0] for `D_c` and a coefficient ring in `Type` killed by an integer
invertible on the target.** With `f`, `j`, `Λ` and `n` as in
`isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_isUnit_natCast`,
`Rf_!` carries `D_c(X_étale, Λ)` into `D_c(Y_étale, Λ)`. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_isUnit_natCast
    {n : ℕ} (hn0 : 0 < n) (hΛ : (n : Λ) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (hK : IsConstructibleEtaleComplex Λ K) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K) :=
  isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_isUnit_natCast_of_directImageZMod Λ
    (fun f _ _ _ hd ℓ _ hℓ q ↦
      isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit f hd ℓ hℓ q)
    hn0 hΛ f hnY j K hK

end Stacks.EtaleCohomology

end
