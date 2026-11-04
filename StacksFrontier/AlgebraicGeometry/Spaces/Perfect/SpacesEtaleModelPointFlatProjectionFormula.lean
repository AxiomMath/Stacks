module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointFlat

/-!
# The projection formula for a flat `X ⟶ Spec(R)` against a module placed in degree zero

Let `T` be an affine object of the big fppf site, `R = Γ(T, 𝒪_T)`, and `f : X ⟶ T` a flat
morphism from a quasi-compact and quasi-separated algebraic space, read as the morphism of ringed
topoi `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)`. For `E` with quasi-coherent cohomology and an
`R`-module `M`, combining the projection formula of [Stacks, Tag 08IN] at the point with
`Lf^*(M[0]) = (𝒪_X ⊗_R M)[0]` for flat `f` gives

  `Rf_*E ⊗^L_R M ≅ Rf_*(E ⊗^L_{𝒪_X} (𝒪_X ⊗_R M))`,

with no derived pullback on the right. This is the identity the source uses to read off the
Tor amplitude of `Rf_*E` in [Stacks, Tag 0DKJ] and [Stacks, Tag 0A1M], and the
`Hom(P, −)`-computation in the proof of [Stacks, Tag 0D3F].

## Main results

* `AlgebraicGeometry.Space.flatProjectionFormulaSingleIso`: the isomorphism above.

## References

* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 0A1M](https://stacks.math.columbia.edu/tag/0A1M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
  {T : BigFppfOver B S hS}

/-- **The projection formula for a flat `X ⟶ Spec(R)` against `M[0]`.** Let `T` be affine,
`R = Γ(T, 𝒪_T)` and `f : X ⟶ T` flat with `X` quasi-compact and quasi-separated, read as the
morphism `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)`. For `E` on the spaces-étale model whose image in
`D(𝒪_X)` has quasi-coherent cohomology and an `R`-module `M`,
`Rf_*E ⊗^L_R M ≅ Rf_*(E ⊗^L_{𝒪_X} (𝒪_X ⊗_R M)[0])`: the projection-formula map of
[Stacks, Tag 0B56], invertible by [Stacks, Tag 08IN]
(`AlgebraicGeometry.Space.isIso_projectionFormulaMap_spacesEtaleModelToBaseRing`), followed by
`Lf^*(M[0]) ≅ (𝒪_X ⊗_R M)[0]` for flat `f`
(`AlgebraicGeometry.Space.derivedPullbackToBaseRingSingleIso`). -/
def flatProjectionFormulaSingleIso (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : qcohDerivedProp B S hS X
      ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E))
    (M : ModuleCat.{u} (baseRing B S hS T)) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).O).obj
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of (baseRing B S hS T))).trans
          (pointModuleCatEquiv (R := baseRing B S hS T))).inverse.obj M)) ≅
    (derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (spacesEtaleModelRingedTopos B S hS X).O).obj E).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((spacesEtaleModelModulesEquiv B S hS X).inverse.obj
            ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj M)))) :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  haveI := isIso_projectionFormulaMap_spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
    hZ hXqc hXqs E hE ((DerivedCategory.singleFunctor _ 0).obj
      (((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of (baseRing B S hS T))).trans
        (pointModuleCatEquiv (R := baseRing B S hS T))).inverse.obj M))
  asIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
      (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))
      (isMorphismOfSites_spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) E _) ≪≫
    (derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).mapIso
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (spacesEtaleModelRingedTopos B S hS X).O).obj E).mapIso
        (derivedPullbackToBaseRingSingleIso f hflat hT M))

end AlgebraicGeometry.Space

end
