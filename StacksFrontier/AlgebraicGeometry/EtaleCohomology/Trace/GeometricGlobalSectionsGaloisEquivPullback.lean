module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsGaloisEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricTrivialRepresentationCounit

/-!
# `Γ(X_k̄, ℱ_ρ) = M`, with `X_k̄` written as a pullback

`AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv` and its Galois equivariance, restated with
`X_k̄ = X ×_{Spec k} Spec k̄` written as `pullback f (specAlgebraMap k k̄)` and the projection
as `pullback.fst`, the form in which the smooth projective model of `X_k̄` and its trace are
stated. The Galois action is written out as the twist of `pr^{-1} ℱ_ρ` along `id_X × Spec σ`
followed by `Γ(X_k̄, (id × Spec σ)_* -) ≅ Γ(X_k̄, -)`.

## Main definitions

* `AlgebraicGeometry.geometricGlobalSectionsTrivialEquivPullback`.

## Main results

* `AlgebraicGeometry.geometricGlobalSectionsTrivialEquivPullback_galois`.
* `AlgebraicGeometry.isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- `AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv` with `X_k̄` written as the pullback
`X ×_k Spec k̄` and `pr` as its first projection. -/
def geometricGlobalSectionsTrivialEquivPullback
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    letI := connectedSpace_of_isCurve B X f
    ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) ≃ₗ[Λ]
      ρ.obj.obj.obj.V :=
  geometricGlobalSectionsTrivialEquiv B X f kbar Λ y ρ hρ

/-- **`Γ(X_k̄, ℱ_ρ|_{X_k̄}) ≅ M` is Galois-equivariant**, in the pullback form: the action of
`σ ∈ Aut_k(k̄)` through the twist of `pr^{-1} ℱ_ρ` along `id_X × Spec σ` is `ρ(γ)` for `γ` lifting
`σ`. -/
theorem geometricGlobalSectionsTrivialEquivPullback_galois
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (z : letI := connectedSpace_of_isCurve B X f
      ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ
        (((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).map
            ((selfMapTwist.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))
              (galoisBaseChange (Over.mk f) kbar
                (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)))
              (galoisBaseChange_comp_fst (Over.mk f) kbar
                (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)))).app
                ((representationSheaf B X _ Λ).obj ρ)) ≫
          (etaleModuleGlobalSectionsDirectImageIso.{u, 0}
            (galoisBaseChange (Over.mk f) kbar
              (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))) Λ).hom.app
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
              ((representationSheaf B X _ Λ).obj ρ))).hom z) =
      (finiteTypeContinuousModuleRepresentation Λ _ ρ) γ
        (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ z) :=
  geometricGlobalSectionsTrivialEquiv_galois B X f kbar Λ y ρ hρ γ z

/-- `AlgebraicGeometry.isIso_constantSheafΓAdj_counit_geometricRepresentationSheaf` in the pullback
form: `ℱ_ρ|_{X_k̄}` is the constant sheaf on its global sections when `π₁(X_k̄)` acts trivially. -/
theorem isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    letI := connectedSpace_of_isCurve B X f
    IsIso ((constantSheafΓAdj (pullback f (specAlgebraMap k kbar)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).counit.app
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) :=
  isIso_constantSheafΓAdj_counit_geometricRepresentationSheaf B X f kbar Λ y ρ
    (fun g => CategoryTheory.End.ext (ModuleCat.hom_ext (hρ g)))

/-- The global sections of `ℱ_ρ|_{X_k̄}` are finite when `π₁(X_k̄)` acts trivially. -/
theorem finite_geometricGlobalSectionsPullback
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    letI := connectedSpace_of_isCurve B X f
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) := by
  let := connectedSpace_of_isCurve B X f
  have : Module.Finite Λ ρ.obj.obj.obj.V := ρ.property
  have : Finite ρ.obj.obj.obj.V := Module.finite_of_finite Λ
  exact Finite.of_equiv _
    (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).symm.toEquiv

end AlgebraicGeometry

end
