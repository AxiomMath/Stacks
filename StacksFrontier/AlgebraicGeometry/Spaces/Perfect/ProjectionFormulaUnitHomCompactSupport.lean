module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProjectionFormulaUnitHomSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedModulePushforwardTotalRightDerived

/-!
# The projection formula on morphisms out of the structure sheaf, for an object with compact
support

Let `f : X ⟶ Y` be a quasi-separated morphism of algebraic spaces with `Y` quasi-separated, and
let `A ∈ D_QCoh(𝒪_X)` have its cohomology sheaves supported on a closed subset `T ⊆ |X|` which
is compact (for instance proper over a quasi-compact `Y`).  Then for `M ∈ D_QCoh(𝒪_Y)`

`Hom(𝒪_Y, Rf_*A ⊗^L M) ≅ Hom(𝒪_X, A ⊗^L Lf^*M)`,

naturally in `M`.  This is the step of the proof of Stacks 0A1M which combines the projection
formula Stacks 08IN with the passage to a quasi-compact open neighbourhood of `T` (as in the
proof of Stacks 08IS), which is what makes `f` quasi-compact there.

## Main results

* `AlgebraicGeometry.Space.exists_unitHomProjectionFormula_of_cohomologySupportedOn`.

## The proof

`T` lies in a quasi-compact open subspace `V ⊆ X`
(`AlgebraicGeometry.Space.exists_isQuasiCompactSpace_openSubspace_of_isCompact`), and
`(X ∖ T, V ⟶ X)` is an elementary distinguished square.  With `j : V ⟶ X`,
`Rf_*A ≅ R(j ≫ f)_*(Lj^*A)` (Stacks 08GG, 0D6E,
`AlgebraicGeometry.Space.nonempty_derivedModulePushforward_iso_of_cohomologySupportedOn`), and
`j ≫ f` is quasi-compact and quasi-separated, so the projection formula map of `j ≫ f`
(`AlgebraicGeometry.Space.unitHomProjectionFormulaEdsEtale`) is invertible on `D_QCoh(𝒪_Y)`;
restriction along `j` (`AlgebraicGeometry.Space.unitHomRestrictProjectionEdsEtale`) is
invertible on morphisms into objects supported on `T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback isGrothendieckAbelian_modules pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **The projection formula on morphisms out of the structure sheaf, for an object with compact
closed support.**  For `f : X ⟶ Y` quasi-separated with `Y` quasi-separated, `A ∈ D_QCoh(𝒪_X)`
supported on a compact closed `T ⊆ |X|`, there is a natural transformation
`Hom(𝒪_Y, Rf_*A ⊗^L -) ⟶ Hom(𝒪_X, A ⊗^L Lf^*-)` of functors `D(𝒪_Y) ⥤ Ab` which is an
isomorphism at every `M ∈ D_QCoh(𝒪_Y)`. -/
theorem exists_unitHomProjectionFormula_of_cohomologySupportedOn
    (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hTop Y.1)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hA : QcohDerived B S hS X A) (T : Set (points B S hS X.1)) (hTcl : IsClosed T)
    (hTc : IsCompact T) (hAT : CohomologySupportedOn B S hS X.1 X.2 T A) :
    ∃ θ : (smallEtaleDerivedTensor B S hS Y).obj
          ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj A) ⋙
          preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
        smallEtaleDerivedModulePullback B S hS f ⋙ (smallEtaleDerivedTensor B S hS X).obj A ⋙
          preadditiveCoyoneda.obj (op (structureDerived X)),
      ∀ M, QcohDerived B S hS Y M → IsIso (θ.app M) := by
  obtain ⟨V, hV, hVqc, hTV⟩ := exists_isQuasiCompactSpace_openSubspace_of_isCompact B S hS X.2 T
    hTc
  have hsq := isElementaryDistinguishedSquare_openSubspaceOfPoints B S hS X.2 T hTcl V hV hTV
  have hcompl : edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Tᶜ) = T := by
    rw [edsComplementPoints, range_pointsMap_ι_openSubspaceOfPoints, compl_compl]
  have hAT' : CohomologySupportedOn B S hS X.1 X.2
      (edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Tᶜ)) A := by
    rw [hcompl]; exact hAT
  obtain ⟨eR⟩ := nonempty_derivedModulePushforward_iso_of_cohomologySupportedOn B S hS hsq f A
    hAT'
  let j := edsEtaleHom B S hS hsq
  have hj : IsEtale B S hS j.hom := isEtale_edsEtaleHom B S hS hsq
  have hf'qc : IsQuasiCompact B S hS (j ≫ f).hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hTop Y.2 hYqs hVqc (j ≫ f).hom
  have hf'qs : IsQuasiSeparated B S hS (j ≫ f).hom :=
    isQuasiSeparated_comp B S hS hsq.isAlgebraicSpace X.2 j.hom f.hom
      (isQuasiSeparated_of_mono B S hS j.hom (inferInstanceAs (Mono V.ι))) hfqs
  let φ := smallEtaleDerivedModulePullbackIsoEtale B S hS j hj
  let e : (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj A ≅
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS (j ≫ f))).obj
          ((smallEtaleDerivedModulePullback B S hS j).obj A) :=
    eR ≪≫ (totalRightDerivedModulePushforwardIso B S hS (j ≫ f)).app _ ≪≫
      (derivedModulePushforward B S hS (j ≫ f)).mapIso (φ.app A).symm
  have hLA : QcohDerived B S hS (edsEtale B S hS hsq)
      ((smallEtaleDerivedModulePullback B S hS j).obj A) :=
    (QcohDerived B S hS (edsEtale B S hS hsq)).prop_of_iso (φ.app A).symm
      (qcohDerived_etaleModulePullback_mapDerivedCategory B S hS j hj A hA)
  have : ∀ M, IsIso ((unitHomRestrictProjectionEdsEtale B S hS hsq f A).app M) :=
    fun M => isIso_unitHomRestrictProjectionEdsEtale_app B S hS hsq f A hAT' M
  have : IsIso (unitHomRestrictProjectionEdsEtale B S hS hsq f A) :=
    NatIso.isIso_of_isIso_app _
  refine ⟨unitHomProjectionFormulaEdsEtale B S hS hsq f A _ e ≫
    inv (unitHomRestrictProjectionEdsEtale B S hS hsq f A), fun M hM => ?_⟩
  have := isIso_unitHomProjectionFormulaEdsEtale_app B S hS hsq f A hf'qc hf'qs hLA _ e M hM
  have := NatIso.isIso_app_of_isIso (inv (unitHomRestrictProjectionEdsEtale B S hS hsq f A)) M
  exact (IsIso.comp_isIso : IsIso ((unitHomProjectionFormulaEdsEtale B S hS hsq f A _ e).app M ≫
    (inv (unitHomRestrictProjectionEdsEtale B S hS hsq f A)).app M))

end AlgebraicGeometry.Space

end
