module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.HomotopyColimitTensorSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso

/-!
# Derived sections of a pullback through the projection formula at the unit

Let `f : U ⟶ X` be a morphism of algebraic spaces and `p : X ⟶ T` a morphism to an affine
object `T` of the big fppf site, with ring of global functions `R`. For `G ∈ D(𝒪_X)` the
projection formula at the unit `Rf_*𝒪_U ⊗^𝐋 G ⟶ Rf_*(𝒪_U ⊗^𝐋 Lf^*G) ≅ Rf_*Lf^*G`, followed by
`RΓ(T, Rp_* -)` and the identification `Rp_* Rf_* ≅ R(f ≫ p)_*`, is a map

`RΓ(X, Rf_*𝒪_U ⊗^𝐋 G) ⟶ RΓ(U, Lf^*G)`

of `D(R)`, natural in `G`. It is an isomorphism for `f` quasi-compact and quasi-separated and `G`
with quasi-coherent cohomology, by [Stacks, Tag 08IN]. This is the map through which
[Stacks, Tag 0CRW] presents `RΓ(U, Lf^*G)` as a homotopy colimit of the `RΓ(X, Eₙ ⊗^𝐋 G)`.

## Main definitions

* `AlgebraicGeometry.Space.sectionsProjectionUnitNatTrans`.

## Main results

* `AlgebraicGeometry.Space.isIso_sectionsProjectionUnitNatTrans_app`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U X : AlgebraicSpaces B S hS} (T : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (f : U ⟶ X)
  (p : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)

/-- **`RΓ(X, Rf_*𝒪_U ⊗^𝐋 -) ⟶ RΓ(U, Lf^* -)`**: the projection formula at the unit
(`CategoryTheory.PullbackInternalHom.projectionUnitNatTrans`) followed by `RΓ(T, Rp_* -)` and the
identification `Rp_* Rf_* ≅ R(f ≫ p)_*`. -/
def sectionsProjectionUnitNatTrans :
    (smallEtaleDerivedTensor B S hS X).obj
        ((derivedModulePushforward B S hS f).obj (structureDerived U)) ⋙
      derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T ⟶
    smallEtaleDerivedModulePullback B S hS f ⋙ derivedModulePushforward B S hS (f ≫ p) ⋙
      representedAffineDerivedSections B S hS T :=
  Functor.whiskerRight (CategoryTheory.PullbackInternalHom.projectionUnitNatTrans
      (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedTensor B S hS X)
      (smallEtaleDerivedTensor B S hS U) (smallEtaleDerivedPullbackTensorIso f)
      (structureDerived U) (smallEtaleDerivedTensorLeftUnitor U))
      (derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T) ≫
    Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS f)
      (Functor.whiskerRight (smallEtaleDerivedPushforwardCompIsoToposHom B S hS f p).hom
        (representedAffineDerivedSections B S hS T))

/-- **`RΓ(X, Rf_*𝒪_U ⊗^𝐋 G) ≅ RΓ(U, Lf^*G)`** for `f` quasi-compact and quasi-separated and `G`
with quasi-coherent cohomology: the projection formula is an isomorphism by [Stacks, Tag 08IN]. -/
theorem isIso_sectionsProjectionUnitNatTrans_app (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (G : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hG : QcohDerived B S hS X G) :
    IsIso ((sectionsProjectionUnitNatTrans T f p).app G) := by
  let ρ := CategoryTheory.PullbackInternalHom.projectionUnitNatTrans
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedTensor B S hS U) (smallEtaleDerivedPullbackTensorIso f)
    (structureDerived U) (smallEtaleDerivedTensorLeftUnitor U)
  have hρ : IsIso (ρ.app G) := IsIso.comp_isIso'
    (isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs _
      (qcohDerived_singleFunctor_structureModule (X := U.1) (hX := U.2)) _ hG) inferInstance
  exact IsIso.comp_isIso'
    ((derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T).mapIso
      (@asIso _ _ _ _ (ρ.app G) hρ)).isIso_hom
    ((representedAffineDerivedSections B S hS T).mapIso
      ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS f p).app
        ((smallEtaleDerivedModulePullback B S hS f).obj G))).isIso_hom

end AlgebraicGeometry.Space

end
