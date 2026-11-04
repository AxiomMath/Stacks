module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCoinvariantsBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceRootChange

/-!
# `H²_c(X_k̄, ℱ_ρ) ≅ M_{π₁(X_k̄)}` and `≅ M_{π₁(X_k̄)}(-1)`

The map `θ_ρ` of `AlgebraicGeometry.compactSupportGeometricCoinvariantsMap` is bijective: it is
`ψ` (bijective, `Stacks.EtaleCohomology.bijective_curveRepresentationCoinvariantsMap`) after two
isomorphisms.  So it is a `Λ`-linear isomorphism `H²_c(X_k̄, ℱ_ρ) ≃ M_π` for each primitive
`n`-th root of unity `ζ`, and the choice-free map `H²_c(X_k̄, ℱ_ρ) ⟶ Hom(μ_n(k̄), M_π)` of
`AlgebraicGeometry.compactSupportGeometricTwistMap` is an isomorphism onto `M_π(-1)`.

## Main definitions

* `AlgebraicGeometry.compactSupportGeometricCoinvariantsEquiv` — `θ_ρ` as an isomorphism.
* `AlgebraicGeometry.compactSupportGeometricTwistEquiv` — `H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M_π)`,
  with no choice of root of unity in its values
  (`AlgebraicGeometry.compactSupportGeometricTwistEquiv_apply_ofMul`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- A composite of three bijective linear maps is bijective. -/
theorem bijective_linearMap_comp_comp {R : Type*} [Ring R] {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module R A] [Module R B] [Module R C]
    [Module R E] {ψ : C →ₗ[R] E} {P : B →ₗ[R] C} {S : A →ₗ[R] B} (h1 : Function.Bijective ψ)
    (h2 : Function.Bijective P) (h3 : Function.Bijective S) :
    Function.Bijective (ψ ∘ₗ P ∘ₗ S) :=
  h1.comp (h2.comp h3)

section Theta

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
  {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))

/-- **`θ_ρ` is bijective.** -/
theorem bijective_compactSupportGeometricCoinvariantsMap
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Bijective (compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have h1 := bijective_curveRepresentationCoinvariantsMap (geometricSmoothModel f j kbar).q Λ B
      (fieldBaseChangeObj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)) y hn hζ
      (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
      ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
        (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
          y)).obj ρ)
  have h2 : Function.Bijective (((etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((representationSheafFieldBaseChangeIso B X f kbar Λ y).hom.app ρ))).hom :=
    (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
      ((2 : ℕ) : ℤ)).mapIso ((etaleModuleExtensionByZero.{u, 0} Λ
        (geometricSmoothModel f j kbar).j).mapIso
          ((representationSheafFieldBaseChangeIso B X f kbar Λ y).app ρ))).toLinearEquiv.bijective
  rw [compactSupportGeometricCoinvariantsMap_eq]
  refine bijective_linearMap_comp_comp ?_ h2
    (galoisCompactSupportSmoothModelIso f j kbar Λ _ ((2 : ℕ) : ℤ)).toLinearEquiv.bijective
  convert h1 using 3

/-- **`θ_ρ : H²_c(X_k̄, ℱ_ρ) ≃ M_{π₁(X_k̄, η̄)}`**, `Λ`-linearly, for a primitive `n`-th root of
unity `ζ` (`n = #Λ`). -/
def compactSupportGeometricCoinvariantsEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ) :=
  LinearEquiv.ofBijective (compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ)
    (bijective_compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ)

/-- The isomorphism `compactSupportGeometricCoinvariantsEquiv` acts as
`compactSupportGeometricCoinvariantsMap`. -/
@[simp]
theorem compactSupportGeometricCoinvariantsEquiv_apply
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    compactSupportGeometricCoinvariantsEquiv B X f kbar Λ y j hn hζ ρ x =
      compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ x := rfl

omit hζ in
/-- **`H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M_π) = M_π(-1)`**, `Λ`-linearly; its underlying map is the
choice-free `AlgebraicGeometry.compactSupportGeometricTwistMap`. -/
def compactSupportGeometricTwistEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar) →+
        Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ)) :=
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  (compactSupportGeometricCoinvariantsEquiv B X f kbar Λ y j hn
      (exists_isPrimitiveRoot_of_isUnit hn).choose_spec ρ).trans
    (rootsOfUnityHomEvalEquiv (exists_isPrimitiveRoot_of_isUnit hn).choose_spec Λ
      (card_nsmul_eq_zero_of_module Λ)).symm

omit hζ in
/-- The linear map underlying `compactSupportGeometricTwistEquiv` is
`compactSupportGeometricTwistMap`. -/
theorem compactSupportGeometricTwistEquiv_toLinearMap
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    (compactSupportGeometricTwistEquiv B X f kbar Λ y j hn ρ).toLinearMap =
      compactSupportGeometricTwistMap B X f kbar Λ y j hn ρ := rfl

/-- **The isomorphism onto `M_π(-1)` does not depend on a root of unity**: at every primitive
`ζ` its value is `θ_ρ(x)` for `ζ`. -/
theorem compactSupportGeometricTwistEquiv_apply_ofMul
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportGeometricTwistEquiv B X f kbar Λ y j hn ρ x (Additive.ofMul hζ.toRootsOfUnity) =
      compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ x :=
  compactSupportGeometricTwistMap_apply_ofMul B X f kbar Λ y j hn hζ ρ x

end Theta

end AlgebraicGeometry

end
