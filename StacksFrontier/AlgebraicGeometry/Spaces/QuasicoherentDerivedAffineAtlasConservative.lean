module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffineConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory

/-!
# Isomorphisms of `D_QCoh` are detected by derived sections over an affine étale atlas

Let `c : W ⟶ Y` be an étale surjective morphism of algebraic spaces and `f : W ⟶ T` an affine
morphism to an affine scheme `T`. A morphism `φ` of `D_QCoh(𝒪_Y)` is an isomorphism as soon as
`RΓ(T, Rf_* Lc^* φ)` is. This is how the source deduces, in the proof of [Stacks, Tag 0DIQ],
that a map of `D_QCoh(𝒪_{Xₙ})` inducing isomorphisms on `RΓ(Uₙ, -)` for affine `U` étale over
`X` is an isomorphism.

The three functors each detect zero objects of `D_QCoh`: `RΓ` over an affine scheme by
`AlgebraicGeometry.Space.isZero_of_isZero_representedAffineDerivedSectionsQcoh_obj`, `Rf_*` along
an affine morphism by
`AlgebraicGeometry.Space.isZero_of_isZero_derivedModulePushforward_of_isAffineHom`, and `Lc^*`
along an étale surjection because its cohomology sheaves are the pullbacks of those of the source
and `AlgebraicGeometry.Space.isZero_of_isZero_etaleModulePullback_of_isSurjective`. Each functor
is triangulated and preserves `D_QCoh`, so the cone of `φ` is zero.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_smallEtaleDerivedModulePullback_of_isSurjective`:
  `Lc^*` along an étale surjection detects zero objects.
* `AlgebraicGeometry.Space.isIso_of_isIso_representedAffineDerivedSections_map`: the criterion.

## References

* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

/- The modules on the small étale site carry the abelian structure of `spaceDerivedCategory`;
the generic site-module instances are not that one. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`Lc^*` along an étale surjection detects zero objects of `D(𝒪_Y)`**: the cohomology sheaves
of `Lc^* E` are the pullbacks `c^* Hⁿ(E)`, and `c^*` detects zero modules. -/
theorem isZero_of_isZero_smallEtaleDerivedModulePullback_of_isSurjective
    {W Y : AlgebraicSpaces B S hS} (c : W ⟶ Y) (hc : IsEtale B S hS c.hom)
    (hsurj : IsSurjective B S hS c.hom) (E : spaceDerivedCategory B S hS Y)
    (h : IsZero ((smallEtaleDerivedModulePullback B S hS c).obj E)) : IsZero E := by
  let := spaceHasDerivedCategory B S hS Y
  let := spaceHasDerivedCategory B S hS W
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W))
  refine Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj E fun q => ?_
  refine isZero_of_isZero_etaleModulePullback_of_isSurjective B S hS c hc hsurj _ ?_
  exact ((DerivedCategory.homologyFunctor _ q).map_isZero h).of_iso
    (((modulePullbackIsoEtaleModulePullback B S hS c hc).app _).symm ≪≫
      (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale c hc E q).symm)

/-- **Isomorphisms of `D_QCoh(𝒪_Y)` are detected by `RΓ(T, Rf_* Lc^* -)`** for `c : W ⟶ Y` étale
surjective and `f : W ⟶ T` an affine morphism to an affine scheme `T`. -/
theorem isIso_of_isIso_representedAffineDerivedSections_map
    {W Y : AlgebraicSpaces B S hS} (c : W ⟶ Y) (hc : IsEtale B S hS c.hom)
    (hsurj : IsSurjective B S hS c.hom) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (f : W ⟶ schemeSpace T)
    (hf : IsAffineHom B S hS f.hom) {E F : spaceDerivedCategory B S hS Y} (φ : E ⟶ F)
    (hE : spaceQuasicoherentProp B S hS Y E) (hF : spaceQuasicoherentProp B S hS Y F)
    (h : IsIso ((representedAffineDerivedSections B S hS T).map
      ((derivedModulePushforward B S hS f).map
        ((smallEtaleDerivedModulePullback B S hS c).map φ)))) :
    IsIso φ := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  obtain ⟨G, g, δ, hT⟩ := distinguished_cocone_triangle φ
  have hG : spaceQuasicoherentProp B S hS Y G := by
    let := spaceHasDerivedCategory B S hS Y
    let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    have hP : WeakSerre.IsWeakSerre P :=
      @WeakSerre.isWeakSerre_of_isWeakSerreClass _ _
        (modulesAbelianSmallEtale B S hS Y.1 Y.2) _
        (quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS Y.1 Y.2)
    have : (spaceQuasicoherentProp B S hS Y).IsTriangulated :=
      DerivedCategoryB.derivedCategoryB_isTriangulated P hP
    have : (spaceQuasicoherentProp B S hS Y).IsClosedUnderIsomorphisms :=
      DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms P hP
    exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT hE hF
  have h₁ := (smallEtaleDerivedModulePullback B S hS c).map_distinguished _ hT
  have h₂ := (derivedModulePushforward B S hS f).map_distinguished _ h₁
  have h₃ := (representedAffineDerivedSections B S hS T).map_distinguished _ h₂
  have hz₃ := (Triangle.isZero₃_iff_isIso₁ _ h₃).2 h
  have hcG := derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS c G hG
  have hfG := qcohDerived_derivedModulePushforward_obj B S hS f
    (isQuasiCompact_of_isAffineHom' B S hS f.hom W.2 (schemeSpace T).2 hf)
    (isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_isAffineHom B S hS f.hom W.2 (schemeSpace T).2 hf)) _ hcG
  have hz₂ := isZero_of_isZero_representedAffineDerivedSectionsQcoh_obj B S hS T ⟨_, hfG⟩ hz₃
  have hz₁ := isZero_of_isZero_derivedModulePushforward_of_isAffineHom B S hS f hf _ hcG
    ((ObjectProperty.ι _).map_isZero hz₂)
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_smallEtaleDerivedModulePullback_of_isSurjective c hc hsurj G hz₁)

end AlgebraicGeometry.Space

end
