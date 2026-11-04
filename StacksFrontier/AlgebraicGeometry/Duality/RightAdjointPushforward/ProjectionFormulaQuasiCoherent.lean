module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalModels

/-!
# The tensorator of `Lf^*` at the two models, and the projection formula on `D_QCoh`

For a morphism of schemes `f : X ⟶ Y`, the oplax tensorator `Lf^*(K ⊗ᴸ L) ⟶ Lf^*K ⊗ᴸ Lf^*L` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal` at the locally small
model is the comparison of [Stacks, Tag 079U] at the standard model,
`Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison`, transported along the
comparison of the two models: `StacksDraft.DerivedModel.derivedPullbackModelIso` for `Lf^*` and
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso` for `⊗ᴸ`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **[Stacks, Tag 079U] at the two models.** For `K`, `L` in the standard model of `D(𝒪_Y)`,
the oplax tensorator of `Lf^*` at the locally small model, at the images `G K`, `G L`, is the
comparison `Lf^*(K ⊗ᴸ L) ⟶ Lf^*K ⊗ᴸ Lf^*L` of the standard model transported along the
comparisons `derivedPullbackModelIso` and `derivedTensorProductFunctorModelIso`. -/
theorem derivedPullbackCanonicalMonoidal_δ_model
    (K L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)) :
    @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
        (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
          f.toLRSHom.toShHom).toOplaxMonoidal
        ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj K)
        ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj L) =
      (derivedPullback f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Y.sheaf).hom.app
            K).app L) ≫
        (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv.app _ ≫
        (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map
          ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
            f.toLRSHom.toShHom).app (K, L)) ≫
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso X.sheaf).inv.app
            _).app _) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app K)).app _ ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).map
          ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app L) :=
  Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal_δ_model
    f.toLRSHom.toShHom K L

/-- **[Stacks, Tag 08EU] on `D_QCoh`**: for `f` quasi-compact and quasi-separated, the
projection-formula map `K ⊗ᴸ Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ E)` built from the monoidal structure of
`Lf^*` on `D_QCoh` is invertible. -/
theorem isIso_projectionFormulaMap_quasiCoherentDerivedPullbackTensorIso
    [QuasiCompact f] [QuasiSeparated f]
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    IsIso (projectionFormulaMap f hpush
      (quasiCoherentDerivedPullbackTensorIso f).hom E K) :=
  ProjectionFormulaMonoidal.isIso_projectionFormulaMap_of_comparison f hpush
    (derivedPullbackCanonicalMonoidal_δ_model f) E K

/-- **The projection maps of `Lf^* ⊣ Rf_*` on `D_QCoh` are invertible**, for `f` quasi-compact
and quasi-separated ([Stacks, Tag 08EU]). -/
theorem isIso_quasiCoherentDerivedAdjunction_projectionMap [QuasiCompact f] [QuasiSeparated f]
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory Y) (M : quasiCoherentDerivedCategory X) :
    IsIso ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      hpush).projectionMap K M) :=
  ProjectionFormulaMonoidal.isIso_projectionMap_of_comparison f hpush
    (derivedPullbackCanonicalMonoidal_δ_model f) K M

/-- `isIso_projectionFormulaMap_quasiCoherentDerivedPullbackTensorIso`, as an instance, at the
pushforward hypothesis `isQuasicoherent_homology_derivedPushforward_of_qcqs`. -/
instance isIso_projectionFormulaMap_of_qcqs [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    IsIso (projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (quasiCoherentDerivedPullbackTensorIso f).hom E K) :=
  isIso_projectionFormulaMap_quasiCoherentDerivedPullbackTensorIso f _ E K

/-- `isIso_quasiCoherentDerivedAdjunction_projectionMap`, as an instance, at the pushforward
hypothesis `isQuasicoherent_homology_derivedPushforward_of_qcqs`. -/
instance isIso_projectionMap_of_qcqs [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    (K : quasiCoherentDerivedCategory Y) (M : quasiCoherentDerivedCategory X) :
    IsIso ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).projectionMap K M) :=
  isIso_quasiCoherentDerivedAdjunction_projectionMap f _ K M

end Stacks.Duality
