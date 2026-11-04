module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Surjectivity and bijectivity of a map of modules are étale local

Let `φ : Z' ⟶ Z` be a surjective flat morphism of algebraic spaces, for instance a surjective
étale atlas. A map `v : M ⟶ N` of `𝒪_Z`-modules is an epimorphism, a monomorphism, or an
isomorphism exactly when its inverse image `φ^*v` is. The modules need not be quasi-coherent.

These are the cases of `AlgebraicGeometry.Space.epi_modulePullback_map_iff_of_isFlat` and its
analogues in which the morphism is surjective, so that every set of points lies in its image.

## Main results

* `AlgebraicGeometry.Space.epi_modulePullback_map_iff_of_isFlat_of_isSurjective`,
  `…mono_…` and `…isIso_…`: along a surjective flat morphism.
* `AlgebraicGeometry.Space.epi_modulePullback_map_iff_of_isEtale_of_isSurjective`,
  `…mono_…` and `…isIso_…`: along a surjective étale morphism.
* `AlgebraicGeometry.Space.Presentation.epi_modulePullback_atlas_map_iff`, `…mono_…` and
  `…isIso_…`: along the atlas `U ⟶ X` of a presentation.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Z' : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS Z.1 Z.2}

/-- Every set of points lies in the image of a surjective morphism. -/
theorem subset_range_pointsMap_of_isSurjective (φ : Z' ⟶ Z) (hs : IsSurjective B S hS φ.hom)
    (T : Set (points B S hS Z.1)) : T ⊆ Set.range (pointsMap B S hS Z'.1 φ.hom) := by
  rw [Set.range_eq_univ.2 hs]
  exact Set.subset_univ T

/-- **Surjectivity of a map of modules descends along a surjective flat morphism.** -/
theorem epi_modulePullback_map_iff_of_isFlat_of_isSurjective (φ : Z' ⟶ Z)
    (hφ : IsFlat B S hS φ.hom) (hs : IsSurjective B S hS φ.hom) (v : M ⟶ N) :
    Epi ((modulePullback B S hS φ).map v) ↔ Epi v :=
  epi_modulePullback_map_iff_of_isFlat B S hS φ hφ v
    (subset_range_pointsMap_of_isSurjective B S hS φ hs _)

/-- **Injectivity of a map of modules descends along a surjective flat morphism.** -/
theorem mono_modulePullback_map_iff_of_isFlat_of_isSurjective (φ : Z' ⟶ Z)
    (hφ : IsFlat B S hS φ.hom) (hs : IsSurjective B S hS φ.hom) (v : M ⟶ N) :
    Mono ((modulePullback B S hS φ).map v) ↔ Mono v :=
  mono_modulePullback_map_iff_of_isFlat B S hS φ hφ v
    (subset_range_pointsMap_of_isSurjective B S hS φ hs _)

/-- **Being an isomorphism descends along a surjective flat morphism.** -/
theorem isIso_modulePullback_map_iff_of_isFlat_of_isSurjective (φ : Z' ⟶ Z)
    (hφ : IsFlat B S hS φ.hom) (hs : IsSurjective B S hS φ.hom) (v : M ⟶ N) :
    IsIso ((modulePullback B S hS φ).map v) ↔ IsIso v :=
  isIso_modulePullback_map_iff_of_isFlat B S hS φ hφ v
    (subset_range_pointsMap_of_isSurjective B S hS φ hs _)
    (subset_range_pointsMap_of_isSurjective B S hS φ hs _)

/-- **Surjectivity of a map of modules is étale local**: it holds exactly when it holds after
inverse image along a surjective étale morphism. -/
theorem epi_modulePullback_map_iff_of_isEtale_of_isSurjective (φ : Z' ⟶ Z)
    (hφ : IsEtale B S hS φ.hom) (hs : IsSurjective B S hS φ.hom) (v : M ⟶ N) :
    Epi ((modulePullback B S hS φ).map v) ↔ Epi v :=
  epi_modulePullback_map_iff_of_isFlat_of_isSurjective B S hS φ (isFlat_of_isEtale B S hS hφ) hs v

/-- **Injectivity of a map of modules is étale local.** -/
theorem mono_modulePullback_map_iff_of_isEtale_of_isSurjective (φ : Z' ⟶ Z)
    (hφ : IsEtale B S hS φ.hom) (hs : IsSurjective B S hS φ.hom) (v : M ⟶ N) :
    Mono ((modulePullback B S hS φ).map v) ↔ Mono v :=
  mono_modulePullback_map_iff_of_isFlat_of_isSurjective B S hS φ (isFlat_of_isEtale B S hS hφ) hs v

/-- **Being an isomorphism is étale local** for maps of modules on an algebraic space. -/
theorem isIso_modulePullback_map_iff_of_isEtale_of_isSurjective (φ : Z' ⟶ Z)
    (hφ : IsEtale B S hS φ.hom) (hs : IsSurjective B S hS φ.hom) (v : M ⟶ N) :
    IsIso ((modulePullback B S hS φ).map v) ↔ IsIso v :=
  isIso_modulePullback_map_iff_of_isFlat_of_isSurjective B S hS φ
    (isFlat_of_isEtale B S hS hφ) hs v

namespace Presentation

variable {B S hS} {X : AlgebraicSpaces B S hS} (P : Presentation B S hS X.1 X.2)
    {M N : Modules.{u, u} B S hS X.1 X.2}

/-- The atlas of a presentation, as a morphism of algebraic spaces. -/
abbrev atlas : schemeSpace P.U ⟶ X := ObjectProperty.homMk P.toSpace

/-- The atlas of a presentation is étale. -/
theorem isEtale_atlas : IsEtale B S hS P.atlas.hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS P.toSpace).2 P.etale

/-- The atlas of a presentation is surjective. -/
theorem isSurjective_atlas : IsSurjective B S hS P.atlas.hom :=
  surjective_pointsMap_of_presheaf_surjective B S hS P.toSpace P.surjective

/-- **A map of modules is surjective exactly when it is so on the atlas of a presentation.** -/
theorem epi_modulePullback_atlas_map_iff (v : M ⟶ N) :
    Epi ((modulePullback B S hS P.atlas).map v) ↔ Epi v :=
  epi_modulePullback_map_iff_of_isEtale_of_isSurjective B S hS P.atlas P.isEtale_atlas
    P.isSurjective_atlas v

/-- **A map of modules is injective exactly when it is so on the atlas of a presentation.** -/
theorem mono_modulePullback_atlas_map_iff (v : M ⟶ N) :
    Mono ((modulePullback B S hS P.atlas).map v) ↔ Mono v :=
  mono_modulePullback_map_iff_of_isEtale_of_isSurjective B S hS P.atlas P.isEtale_atlas
    P.isSurjective_atlas v

/-- **A map of modules is an isomorphism exactly when it is so on the atlas of a
presentation.** -/
theorem isIso_modulePullback_atlas_map_iff (v : M ⟶ N) :
    IsIso ((modulePullback B S hS P.atlas).map v) ↔ IsIso v :=
  isIso_modulePullback_map_iff_of_isEtale_of_isSurjective B S hS P.atlas P.isEtale_atlas
    P.isSurjective_atlas v

end Presentation

end AlgebraicGeometry.Space

end
