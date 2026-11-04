module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGroupHomologyUniversal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariantsEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCohomology
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalSuccBijective

/-!
# `H_c^{2-i}(X_k̄, ℱ_ρ)` and the homology of `π₁(X_k̄)`

Let `T` be the homological δ-functor `Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)` and `H` the homology
`Hᵢ(π₁(X_k̄), M)` (`AlgebraicGeometry.geometricGroupHomology`), a universal δ-functor. Tag 03VK
identifies `T₀ = H²_c` with the coinvariants `H₀ = (-)_{π₁(X_k̄)}`, naturally; this extends
uniquely to a morphism `γ : T ⟶ H`, which is bijective in degree one (both sides being
coeffaceable there).

## Main definitions

* `AlgebraicGeometry.compactSupportRepresentationHomologyZeroCoinvariantsIso` — `T₀ ≅ (-)_{π₁}`.
* `AlgebraicGeometry.compactSupportGroupHomologyComparison` — `γ : T ⟶ H`.

## Main results

* `AlgebraicGeometry.bijective_compactSupportGroupHomologyComparison_app_one`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [IsAlgClosure k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  [CompactSpace X.1] [QuasiSeparatedSpace X.1] (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
  {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))

omit [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- The component of `T₀ ≅ (-)_{π₁(X_k̄)}` at `ρ`. -/
def compactSupportRepresentationHomologyZeroCoinvariantsIsoApp
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 0).obj ρ ≅
      (restrictedCoinvariantsFunctor Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y)).obj ρ :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ ≪≫
    (compactSupportGeometricCoinvariantsEquiv B X f kbar Λ y j hn hζ ρ).toModuleIso

omit [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- The component of `T₀ ≅ (-)_{π₁(X_k̄)}` at `ρ`, on elements: the map of Tag 03VK on geometric
coinvariants (`AlgebraicGeometry.compactSupportGeometricCoinvariantsMap`) after
`AlgebraicGeometry.compactSupportRepresentationHomologyZeroIso`. -/
lemma compactSupportRepresentationHomologyZeroCoinvariantsIsoApp_hom_apply
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (a : letI := connectedSpace_of_isCurve B X f
      ((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 0).obj ρ) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
    (compactSupportRepresentationHomologyZeroCoinvariantsIsoApp B X f kbar Λ y j hn hζ ρ).hom.hom
        a =
      compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ
        ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).hom.hom a) :=
  rfl

omit [Smooth f] [IsAlgClosed kbar] [Fintype Λ] [IsAlgClosure k kbar] [CompactSpace X.1]
  [QuasiSeparatedSpace X.1] in
/-- The coinvariants functor on a morphism is the map of Tag 03VK on geometric coinvariants. -/
lemma restrictedCoinvariantsFunctor_map_hom_eq_geometricCoinvariantsMap
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))}
    (v : ρ ⟶ ρ') :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ((restrictedCoinvariantsFunctor Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y)).map v).hom =
      geometricCoinvariantsMap B X f kbar Λ y v :=
  rfl

omit [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- **`T₀ = H²_c(X_k̄, -) ≅ (-)_{π₁(X_k̄)}`**, naturally (Tag 03VK, for the primitive root `ζ`). -/
def compactSupportRepresentationHomologyZeroCoinvariantsIso :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (compactSupportRepresentationHomology B X _ Λ f j kbar).functor 0 ≅
      restrictedCoinvariantsFunctor Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  NatIso.ofComponents
    (compactSupportRepresentationHomologyZeroCoinvariantsIsoApp B X f kbar Λ y j hn hζ)
    (fun {ρ ρ'} v ↦ by
      have h1 := compactSupportRepresentationHomologyZeroIso_hom_naturality B X _ Λ f j kbar v
      have h2 := compactSupportGeometricCoinvariantsMap_naturality B X f kbar Λ y j hn hζ v
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      have e1 := congrArg (fun φ ↦ ModuleCat.Hom.hom φ a) h1
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at e1
      have e2 := congrArg (fun φ ↦ φ
        ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).hom.hom a)) h2
      simp only [LinearMap.coe_comp, Function.comp_apply] at e2
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
      rw [compactSupportRepresentationHomologyZeroCoinvariantsIsoApp_hom_apply,
        compactSupportRepresentationHomologyZeroCoinvariantsIsoApp_hom_apply, e1,
        restrictedCoinvariantsFunctor_map_hom_eq_geometricCoinvariantsMap]
      exact e2)

variable (hcompOp : letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    IsIso (geometricComparison B X Λᵐᵒᵖ f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y))

include hn hζ hcompOp j in
/-- **The comparison `γ : H_c^{2-i}(X_k̄, -) ⟶ H_i(π₁(X_k̄), -)`**: the unique morphism of
homological δ-functors into the universal homology extending Tag 03VK in degree zero. -/
def compactSupportGroupHomologyComparison :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportRepresentationHomology B X _ Λ f j kbar ⟶ geometricGroupHomology B X f kbar Λ y :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI := isUniversal_geometricGroupHomology B X f kbar Λ y j hn hcompOp
  Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.lift
    (compactSupportRepresentationHomologyZeroCoinvariantsIso B X f kbar Λ y j hn hζ ≪≫
      (restrictedHomologyZeroIso Λ _).symm).hom

include hn hζ hcompOp j in
/-- In degree zero `γ` is the natural isomorphism `T₀ ≅ (-)_{π₁(X_k̄)} ≅ H₀` it extends. -/
lemma compactSupportGroupHomologyComparison_app_zero :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (compactSupportGroupHomologyComparison B X f kbar Λ y j hn hζ hcompOp).app 0 =
      (compactSupportRepresentationHomologyZeroCoinvariantsIso B X f kbar Λ y j hn hζ ≪≫
        (restrictedHomologyZeroIso Λ _).symm).hom := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have := isUniversal_geometricGroupHomology B X f kbar Λ y j hn hcompOp
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.lift_app_zero _

include hn hζ hcompOp j in
/-- `γ₀` is bijective. -/
theorem bijective_compactSupportGroupHomologyComparison_app_zero
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Bijective (((compactSupportGroupHomologyComparison B X f kbar Λ y j hn hζ hcompOp).app
      0).app M) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  rw [compactSupportGroupHomologyComparison_app_zero]
  exact ConcreteCategory.bijective_of_isIso _

include hn hζ hcompOp j in
/-- **`γ₁ : H_c^1(X_k̄, -) ⟶ H_1(π₁(X_k̄), -)` is bijective**: both sides are coeffaceable in
degree one and `γ₀` is bijective. -/
theorem bijective_compactSupportGroupHomologyComparison_app_one
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Bijective (((compactSupportGroupHomologyComparison B X f kbar Λ y j hn hζ hcompOp).app
      1).app M) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have := coeffaceable_geometricGroupHomology B X f kbar Λ y j hn hcompOp
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.bijective_app_succ _ 0
    (bijective_compactSupportGroupHomologyComparison_app_zero B X f kbar Λ y j hn hζ hcompOp)
    (coeffacement_compactSupportRepresentationHomology_zero B X f kbar Λ y j hn hcompOp)
    (fun N ↦ Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.nonempty N 0) M

end AlgebraicGeometry

end
