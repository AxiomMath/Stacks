module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceTwistPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory

/-!
# Derived sections of an affine algebraic space over its terminal chart

Let `X` be an algebraic space over `S` with an isomorphism `e : X ≅ h_{T'}` onto the presheaf
represented by an affine object `T'` of the big fppf site, and let `h : X ⟶ h_T` be a morphism to
an affine object `T` with ring `A = Γ(T, 𝒪_T)`. The isomorphism makes `T'` an étale chart `U` of
`X` (`AlgebraicGeometry.Space.etaleChartOfIso`) whose chart morphism `h_{T'} ⟶ X` is `e⁻¹`. The
derived sections `RΓ_A(X, K)` of `K ∈ D(𝒪_X)` over `T` are then the derived sections
`RΓ(U, K) ∈ D(Γ(T', 𝒪))` over the chart, read as complexes of `A`-modules along the ring map of
`T' ⟶ T`:

`RΓ_A(X, K) ≅ RΓ(U, K)|_A`.

So the action of `Γ(X, 𝒪_X) = Γ(T', 𝒪)` on `RΓ(X, K)` is visible in `D(Γ(T', 𝒪))`.

## Main definitions

* `AlgebraicGeometry.Space.etaleChartOfIsoSpaceIso`: the chart morphism `h_{T'} ≅ X`.
* `AlgebraicGeometry.Space.etaleChartOfIsoBaseHom`: the morphism `T' ⟶ T` of the site with
  Yoneda image `e⁻¹ ≫ h`.
* `AlgebraicGeometry.Space.derivedPushforwardSectionsIsoEtaleChartOfIso`:
  `RΓ_A(X, K) ≅ RΓ(U, K)|_A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {T' : BigFppfOver B S hS} (e : X.1 ≅ yoneda.obj T')

/-- **The chart morphism of the chart given by an isomorphism `X ≅ h_{T'}` is an isomorphism**
`h_{T'} ≅ X` of algebraic spaces. -/
def etaleChartOfIsoSpaceIso :
    (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ≅ X where
  hom := chartToSpace B S hS X (etaleChartOfIso B S hS e)
  inv := ObjectProperty.homMk e.hom
  hom_inv_id := by ext1; exact e.inv_hom_id
  inv_hom_id := by ext1; exact e.hom_inv_id

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  (h : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)

/-- The scheme of the chart given by an isomorphism `X ≅ h_{T'}` with `T'` affine is affine. -/
instance isAffine_toScheme_etaleChartOfIso :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj (etaleChartOfIso B S hS e))) :=
  inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj T'))

/-- The morphism `T' ⟶ T` of the site whose Yoneda image is `e⁻¹ ≫ h`. -/
abbrev etaleChartOfIsoBaseHom : T' ⟶ T := yoneda.preimage (e.inv ≫ h.hom)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The chart morphism followed by `h` is the represented morphism of
`AlgebraicGeometry.Space.etaleChartOfIsoBaseHom`. -/
theorem representedChartToSpace_etaleChartOfIso_comp :
    representedChartToSpace X (etaleChartOfIso B S hS e) ≫ h =
      representedSpaceMap B S hS (etaleChartOfIsoBaseHom e h) := by
  ext1
  exact (Functor.map_preimage yoneda _).symm

attribute [local instance] hasRightDerivedFunctor_chartSections in
/-- **`RΓ_A(X, K) ≅ RΓ(U, K)|_A`** for the chart `U` given by an isomorphism `X ≅ h_{T'}`: the
derived sections over the affine base `T` of the derived direct image along `h` are the derived
sections over the chart, restricted along the ring map of `T' ⟶ T`. -/
def derivedPushforwardSectionsIsoEtaleChartOfIso (K : spaceDerivedCategory B S hS X) :
    (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS T).obj K ≅
      (StacksDraft.ringRestrictScalars
        (representedAffineCommRingCatHom B S hS (etaleChartOfIsoBaseHom e h)).hom).obj
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          (etaleChartOfIso B S hS e)).obj K) :=
  (representedAffineDerivedSections B S hS T).mapIso
      (derivedModulePushforwardCompPullbackIso (etaleChartOfIsoSpaceIso e) h K).symm ≪≫
    ((chartDerivedSectionsPushforwardIso X (etaleChartOfIso B S hS e) h
      (etaleChartOfIsoBaseHom e h) (representedChartToSpace_etaleChartOfIso_comp e h)).app K).symm

end AlgebraicGeometry.Space

end
