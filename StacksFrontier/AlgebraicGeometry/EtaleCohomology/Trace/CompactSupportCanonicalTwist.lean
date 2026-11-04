module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveExtensionByZeroSheafTrace
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelGaloisCompat
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelOpenRestriction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsGaloisEquivPullback
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportNormalCoinvariantsReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceRootChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RootsOfUnityHomTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.Remark03VL

/-!
# The trace `Ξ : H²_c(X_k̄, ℱ_ρ) ≅ M(-1)` for `ρ` trivial on `π₁(X_k̄)`, and its Galois law

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure,
`Λ` a finite ring with `n = #Λ` invertible, and `ℱ_ρ` the sheaf on `X_étale` attached to a finite
`Λ`-module `M` with a continuous action `ρ` of `π₁(X, η̄)` on which `π₁(X_k̄, η̄)` acts trivially.
Then `Ξ_ζ : H²_c(X_k̄, ℱ_ρ) ≅ M` is the smooth model `H²_c(X_k̄, ℱ) ≅ H²(C, q^{-1}(j_! ℱ))`, the
trace through a primitive `n`-th root of unity `ζ` on the smooth projective model `C` of `X_k̄`
onto `Γ(X_k̄, ℱ|_{X_k̄})`, and `Γ(X_k̄, ℱ_ρ|_{X_k̄}) ≅ M` by evaluation at `η̄`. It satisfies
`Ξ_{σ(ζ)}(σ x) = ρ(γ) Ξ_ζ(x)` for `γ` lifting `σ ∈ Aut_k(k̄)` and `Ξ_{ζ^b} = b Ξ_ζ`, so
`x ↦ (ζ ↦ Ξ_ζ(x))` is a choice-free isomorphism onto `Hom(μ_n(k̄), M) = M(-1)` intertwining `σ`
with `g ↦ ρ(γ) ∘ g ∘ σ⁻¹`. This is the constant-on-`X_k̄` case of Tag 03VK
(the general case reduces to it through the largest quotient of `ℱ_ρ` constant on `X_k̄`).

## Main definitions

* `AlgebraicGeometry.compactSupportTrivialTrace` — `Ξ_ζ`.
* `AlgebraicGeometry.compactSupportTrivialTwistEquiv` — `H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M)`.

## Main results

* `AlgebraicGeometry.compactSupportTrivialTrace_galois` — `Ξ_{σ(ζ)}(σ x) = ρ(γ) Ξ_ζ(x)`.
* `AlgebraicGeometry.compactSupportTrivialTrace_of_pow_eq` — `Ξ_{ζ^b} = b Ξ_ζ`.
* `AlgebraicGeometry.compactSupportTrivialTwistEquiv_apply_ofMul` — the value of the twisted `Ξ`
  at a primitive `ζ` is `Ξ_ζ`.
* `AlgebraicGeometry.compactSupportTrivialTwistEquiv_galois` — the twisted `Ξ` intertwines `σ`
  with `g ↦ ρ(γ) ∘ g ∘ σ⁻¹`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace AlgebraicGeometry

section SmoothModel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ]

/-- **`H^i_c(X_k̄, ℱ) ≅ H^i(C, q^{-1}(j_! ℱ))`**: the smooth model iso
`Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso` followed by
`j_{C!}(ℱ|_{X_k̄}) ≅ q^{-1}(j_! ℱ)`. -/
def galoisCompactSupportSmoothModelInverseImageEquiv (F : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i ≃ₗ[Λ]
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).obj ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) :=
  (galoisCompactSupportSmoothModelIso f j kbar Λ F i).toLinearEquiv ≪≫ₗ
    ((((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
      i).mapIso (geometricSmoothModelInverseImageIso f j kbar Λ F)).symm.toLinearEquiv)

/-- `galoisCompactSupportSmoothModelInverseImageEquiv` is the smooth model iso followed by the
inverse of `j_{C!}(ℱ|_{X_k̄}) ≅ q^{-1}(j_! ℱ)` on `H^i(C, -)`. -/
theorem galoisCompactSupportSmoothModelInverseImageEquiv_apply (F : EtaleModules.{u, 0} Λ X)
    (i : ℤ) (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i) :
    galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F i x =
      (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).map (geometricSmoothModelInverseImageIso f j kbar Λ F).inv).hom
        ((galoisCompactSupportSmoothModelIso f j kbar Λ F i).hom.hom x) :=
  rfl

/-- **The Galois action on `H^i_c(X_k̄, ℱ)` is pullback along `s̃_σ` on `H^i(C, q^{-1}(j_! ℱ))`**,
through the canonical twist of `q^{-1}(j_! ℱ)` (`s̃_σ` lies over `X̄`). -/
theorem galoisCompactSupportSmoothModelInverseImageEquiv_galois (σ : kbar ≃ₐ[k] kbar)
    (F : EtaleModules.{u, 0} Λ X) (i : ℤ) (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i) :
    galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F i
        ((galoisCompactSupportGroupAction Λ f j kbar σ
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i).hom x) =
      (integralSelfMapCohomologyEndo Λ (geometricSmoothModelGaloisAut f j kbar σ)
            ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))
        ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
          (geometricSmoothModelGaloisAut f j kbar σ)
          (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i).hom
        (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F i x) := by
  rw [galoisCompactSupportSmoothModelInverseImageEquiv_apply,
    galoisCompactSupportSmoothModelInverseImageEquiv_apply]
  have h1 := congrArg (fun φ => φ.hom x)
    (galoisCompactSupportSmoothModelIso_hom_galoisAction f j kbar Λ σ F i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, geometricSmoothModelGaloisAction, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply
      (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
        i).map (geometricSmoothModelInverseImageIso f j kbar Λ F).inv).hom, ← ModuleCat.hom_comp,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

end SmoothModel

section Trivial

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- **The trace `H²(C, q^{-1}(j_! ℱ_ρ)) ≅ Γ(X_k̄, ℱ_ρ|_{X_k̄})`** through `ζ` on the smooth
projective model `C` of `X_k̄`, for `ρ` on which `π₁(X_k̄)` acts trivially
(`Stacks.EtaleCohomology.curveExtensionByZeroRestrictionTrace` for `j_C^{-1} q^{-1}(j_! ℱ) ≅
ℱ|_{X_k̄}`). -/
def geometricSmoothModelTrivialTrace
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) :
    letI := connectedSpace_of_isCurve B X f
    ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          ((2 : ℕ) : ℤ)).obj
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) ≃ₗ[Λ]
            ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) :=
  letI := connectedSpace_of_isCurve B X f
  curveExtensionByZeroRestrictionTrace (geometricSmoothModel f j kbar).q Λ hn hζ
    (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
    ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
    (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                  (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
    (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ hρ)
    (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ hρ)

/-- **The trace on the smooth model under `σ ∈ Aut_k(k̄)`**: the trace through `σ(ζ)` of the
pullback along `s̃_σ` is the Galois action on `Γ(X_k̄, ℱ|_{X_k̄})` applied to the trace through
`ζ`. -/
theorem geometricSmoothModelTrivialTrace_galois
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (σ : kbar ≃ₐ[k] kbar) {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (z : letI := connectedSpace_of_isCurve B X f
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
            ((2 : ℕ) : ℤ)).obj
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ hρ
        (hζ.map_of_injective σ.toRingEquiv.injective) ((integralSelfMapCohomologyEndo Λ
                (geometricSmoothModelGaloisAut f j kbar σ)
                ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))
        ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
          (geometricSmoothModelGaloisAut f j kbar σ)
          (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
                  ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))
                ((2 : ℕ) : ℤ)).hom z) =
      (((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).map
            ((selfMapTwist.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))
              (galoisBaseChange (Over.mk f) kbar σ)
              (galoisBaseChange_comp_fst (Over.mk f) kbar σ)).app
                  ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ≫
          (etaleModuleGlobalSectionsDirectImageIso.{u, 0}
            (galoisBaseChange (Over.mk f) kbar σ) Λ).hom.app
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
                  ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))).hom
                (geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ hρ hζ z) := by
  let := connectedSpace_of_isCurve B X f
  unfold geometricSmoothModelTrivialTrace
  have h := curveExtensionByZeroRestrictionTrace_integralSelfMapCohomologyEndo_of_twist
    (geometricSmoothModel f j kbar).q Λ hn hζ (geometricSmoothModel f j kbar).j
    (geometricSmoothModel f j kbar).finite_compl (galoisBaseChange (Over.mk f) kbar σ)
    (geometricSmoothModelGaloisAut f j kbar σ)
    (isPullback_geometricSmoothModelGaloisAut_j f j kbar σ)
    σ.toRingEquiv (geometricSmoothModelGaloisAut_q f j kbar σ) _ _
    (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ _)
    (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ hρ)
    (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ hρ) _ _
    (geometricSmoothModelInverseImageRestrictionIso_selfMapTwist f j kbar Λ σ _) z
  convert h using 3

/-- **`Ξ_ζ : H²_c(X_k̄, ℱ_ρ) ≅ M`** for `ρ` on which `π₁(X_k̄)` acts trivially: the smooth model
`H²_c(X_k̄, ℱ) ≅ H²(C, q^{-1}(j_! ℱ))`, the trace through `ζ` onto `Γ(X_k̄, ℱ|_{X_k̄})`, and
`Γ(X_k̄, ℱ|_{X_k̄}) ≅ M`. -/
def compactSupportTrivialTrace
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) :
    letI := connectedSpace_of_isCurve B X f
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X
                  (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
            ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      ρ.obj.obj.obj.V :=
  letI := connectedSpace_of_isCurve B X f
  (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)
        ((2 : ℕ) : ℤ)).trans
    ((geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ hρ hζ).trans
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ))

/-- `Ξ_ζ(x)` is the evaluation `Γ(X_k̄, ℱ_ρ|_{X_k̄}) ≅ M` of the trace through `ζ` of the image of
`x` under `H²_c(X_k̄, ℱ_ρ) ≅ H²(C, q^{-1}(j_! ℱ_ρ))`. -/
theorem compactSupportTrivialTrace_apply
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X
                  (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
            ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ x =
      geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ
        (geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ hρ hζ
          (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ
                ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)
                ((2 : ℕ) : ℤ) x)) := by
  unfold compactSupportTrivialTrace
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]

/-- **`Ξ` is Galois-equivariant.** For `γ ∈ π₁(X, η̄)` with image `σ ∈ Aut_k(k̄)`, `Ξ` through
`σ(ζ)` of `σ x` is `ρ(γ)` applied to `Ξ` through `ζ` of `x`. -/
theorem compactSupportTrivialTrace_galois
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
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X
                  (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
            ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ
        (hζ.map_of_injective (geometricQuotientGaloisEquiv B X f kbar y
                (QuotientGroup.mk γ)).toRingEquiv.injective)
        ((galoisCompactSupportGroupAction Λ f j kbar
                (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
              ((2 : ℕ) : ℤ)).hom x) =
      (finiteTypeContinuousModuleRepresentation Λ _ ρ) γ
        (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ x) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  rw [compactSupportTrivialTrace_apply, compactSupportTrivialTrace_apply,
    galoisCompactSupportSmoothModelInverseImageEquiv_galois,
    geometricSmoothModelTrivialTrace_galois]
  exact geometricGlobalSectionsTrivialEquivPullback_galois B X f kbar Λ y ρ hρ γ _

/-- **The trace on the smooth model for `ζ^b` is `b` times the one for `ζ`.** -/
theorem geometricSmoothModelTrivialTrace_of_pow_eq
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ ζ' : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (hζ' : IsPrimitiveRoot ζ' (Fintype.card Λ)) {b : ℕ} (hb : ζ ^ b = ζ')
    (z : letI := connectedSpace_of_isCurve B X f
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
            ((2 : ℕ) : ℤ)).obj
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)))) :
    geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ hρ hζ' z =
      b • geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ hρ hζ z := by
  let := connectedSpace_of_isCurve B X f
  unfold geometricSmoothModelTrivialTrace
  have h := curveExtensionByZeroRestrictionTrace_of_pow_eq (geometricSmoothModel f j kbar).q Λ hn hζ
    (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl hζ' hb _ _
    (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ _)
    (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ hρ)
    (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ hρ) z
  convert h using 3

/-- **`Ξ_{ζ^b}` is `b` times `Ξ_ζ`.** -/
theorem compactSupportTrivialTrace_of_pow_eq
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ ζ' : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (hζ' : IsPrimitiveRoot ζ' (Fintype.card Λ)) {b : ℕ} (hb : ζ ^ b = ζ')
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X
                  (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
            ((2 : ℕ) : ℤ)) :
    compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ' x =
      b • compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ x := by
  rw [compactSupportTrivialTrace_apply, compactSupportTrivialTrace_apply,
    geometricSmoothModelTrivialTrace_of_pow_eq B X f kbar Λ y j hn ρ hρ hζ hζ' hb, map_nsmul]

/-- **`Ξ : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n(k̄), M) = M(-1)`, with no root of unity chosen in its
values**, for `ρ` on which `π₁(X_k̄)` acts trivially: `x ↦ (ζ ↦ Ξ_ζ(x))` for primitive `ζ`
(`AlgebraicGeometry.compactSupportTrivialTwistEquiv_apply_ofMul`), built with one primitive
root `ζ₀`. -/
def compactSupportTrivialTwistEquiv
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
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X
                  (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
            ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar) →+ ρ.obj.obj.obj.V) :=
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ
      (exists_isPrimitiveRoot_of_isUnit hn).choose_spec).trans
    (rootsOfUnityHomEvalEquiv (exists_isPrimitiveRoot_of_isUnit hn).choose_spec Λ
      (card_nsmul_eq_zero_of_module Λ)).symm

/-- **The twisted `Ξ` does not depend on a root of unity**: its value at every primitive `ζ` is
`Ξ_ζ`. -/
theorem compactSupportTrivialTwistEquiv_apply_ofMul
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X
                  (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
            ((2 : ℕ) : ℤ)) :
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportTrivialTwistEquiv B X f kbar Λ y j hn ρ hρ x (Additive.ofMul hζ.toRootsOfUnity) =
      compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ x := by
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have h₀ := (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
  obtain ⟨b, -, hb⟩ := h₀.eq_pow_of_pow_eq_one hζ.pow_eq_one
  rw [compactSupportTrivialTrace_of_pow_eq B X f kbar Λ y j hn ρ hρ h₀ hζ hb]
  exact rootsOfUnityHomEvalEquiv_symm_apply_of_pow_eq h₀ Λ (card_nsmul_eq_zero_of_module Λ) _ b _
    (by simp [hb])

/-- **The twisted `Ξ` is Galois-equivariant.** For `γ ∈ π₁(X, η̄)` with image
`σ ∈ Aut_k(k̄)`, `Ξ(σ x) = ρ(γ) ∘ Ξ(x) ∘ σ⁻¹` on `μ_n(k̄)`. -/
theorem compactSupportTrivialTwistEquiv_galois
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
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X
                  (y.map (fieldBaseChangeObjProj B X f kbar
                      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
            ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportTrivialTwistEquiv B X f kbar Λ y j hn ρ hρ
        ((galoisCompactSupportGroupAction Λ f j kbar
                (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))
              ((2 : ℕ) : ℤ)).hom x) =
      ((finiteTypeContinuousModuleRepresentation Λ _ ρ γ).toAddMonoidHom.comp
        ((compactSupportTrivialTwistEquiv B X f kbar Λ y j hn ρ hρ x).comp
          (galoisRootsOfUnity k kbar (Fintype.card Λ)
            (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))⁻¹).toAdditive)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have h₀ := (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
  have h₁ := h₀.map_of_injective
    (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)).toRingEquiv.injective
  refine addMonoidHom_rootsOfUnity_ext h₁ Λ (card_nsmul_eq_zero_of_module Λ) ?_
  rw [compactSupportTrivialTwistEquiv_apply_ofMul B X f kbar Λ y j hn ρ hρ h₁,
    compactSupportTrivialTrace_galois B X f kbar Λ y j hn ρ hρ γ h₀, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply]
  have hz : (galoisRootsOfUnity k kbar (Fintype.card Λ)
      (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))⁻¹).toAdditive
        (Additive.ofMul h₁.toRootsOfUnity) = Additive.ofMul h₀.toRootsOfUnity := by
    refine congrArg Additive.ofMul (rootsOfUnity.coe_injective ?_)
    simp [AlgEquiv.aut_inv]
  rw [hz, compactSupportTrivialTwistEquiv_apply_ofMul B X f kbar Λ y j hn ρ hρ h₀,
    LinearMap.toAddMonoidHom_coe]

omit [Fintype Λ] [Smooth f] in
/-- `π₁(X_k̄)` acts trivially on `ρ_N = M_N`. -/
theorem geometricNormalCoinvariants_representation_map_eq_one
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ∀ g, (finiteTypeContinuousModuleRepresentation Λ _
          (geometricNormalCoinvariants B X f kbar Λ y ρ))
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1 := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  intro g
  exact Representation.IsTrivial.out (ρ := (normalCoinvariantsRepresentation
    (finiteTypeContinuousModuleRepresentation Λ _ ρ)
    (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)
    ⟨_, g, rfl⟩

omit [Fintype Λ] in
/-- The residual Galois action on `M_N` at the image of `γ` is the action of `γ` on `ρ_N`. -/
theorem geometricCoinvariantsGaloisRepresentation_mk
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (w : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      Stacks.Trace.coinvariants ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricCoinvariantsGaloisRepresentation B X f kbar Λ y ρ
        (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)) w =
      (finiteTypeContinuousModuleRepresentation Λ _ (geometricNormalCoinvariants B X f kbar Λ y ρ))
        γ w := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  obtain ⟨m, rfl⟩ := (Stacks.Trace.coinvariantsKer _).mkQ_surjective w
  exact galoisCoinvariantsRepresentation_apply_mk _ _ _ γ m

end Trivial

end AlgebraicGeometry

end
