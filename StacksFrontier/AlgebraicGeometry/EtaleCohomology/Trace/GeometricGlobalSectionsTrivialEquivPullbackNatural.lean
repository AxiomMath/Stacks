module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsGaloisEquivPullback

/-!
# `Γ(X_k̄, ℱ_ρ|_{X_k̄}) ≅ M` is natural in `ρ`, in the pullback form

`AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv_naturality` with `X_k̄` written as the
pullback `X ×_k Spec k̄` and `pr` as its first projection, the spelling of
`AlgebraicGeometry.geometricGlobalSectionsTrivialEquivPullback`.

## Main results

* `AlgebraicGeometry.geometricGlobalSectionsTrivialEquivPullback_naturality`,
  `AlgebraicGeometry.geometricGlobalSectionsTrivialEquivPullback_comp_naturality`.
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

omit [Smooth f] [IsAlgClosed kbar] in
/-- **`Γ(X_k̄, ℱ_ρ|_{X_k̄}) ≅ M` is natural in `ρ`**, in the pullback form: for a morphism
`φ : ρ ⟶ ρ'` of representations trivial on `π₁(X_k̄)`, it carries `Γ(X_k̄, pr^{-1} ℱ_φ)` to the
underlying linear map of `φ`. -/
theorem geometricGlobalSectionsTrivialEquivPullback_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))}
    (φ : ρ ⟶ ρ')
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hρ' : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ')
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (z : letI := connectedSpace_of_isCurve B X f
      ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ' hρ'
        (((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ))).hom z) =
      φ.hom.hom.hom.hom.hom (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ z) :=
  geometricGlobalSectionsTrivialEquiv_naturality B X f kbar Λ y φ hρ hρ' z

omit [Smooth f] [IsAlgClosed kbar] in
/-- `AlgebraicGeometry.geometricGlobalSectionsTrivialEquivPullback_naturality` as an equation of
linear maps. -/
theorem geometricGlobalSectionsTrivialEquivPullback_comp_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))}
    (φ : ρ ⟶ ρ')
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hρ' : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ')
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    letI := connectedSpace_of_isCurve B X f
    (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ' hρ').toLinearMap ∘ₗ
        ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ))).hom =
      φ.hom.hom.hom.hom.hom ∘ₗ
        (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).toLinearMap :=
  LinearMap.ext fun z => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
    exact geometricGlobalSectionsTrivialEquivPullback_naturality B X f kbar Λ y φ hρ hρ' z

end AlgebraicGeometry

end
