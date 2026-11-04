module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariantsEquiv

/-!
# The degree-zero part of `(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` and coinvariants

The homological δ-functor `Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)`
(`AlgebraicGeometry.compactSupportRepresentationHomology`) has `T₀(ρ) = H²_c(X_k̄, ℱ_ρ)`, and
Lemma 03VK identifies this with the coinvariants `M_{π₁(X_k̄)}`, naturally in `ρ`. For the
counting argument behind the coeffaceability of `T₁` (Stacks 03VM) only the following consequence
is used: for a morphism `v : ρ ⟶ ρ'` the kernel of `T₀(v)` has as many elements as the kernel of
the induced map on coinvariants. This is a statement about cardinalities, so it does not depend on
which natural isomorphism of Lemma 03VK is used.

## Main definitions

* `AlgebraicGeometry.compactSupportRepresentationHomologyZeroIso`: `T₀(ρ) ≅ H²_c(X_k̄, ℱ_ρ)`.

## Main results

* `AlgebraicGeometry.compactSupportRepresentationHomologyZeroIso_hom_naturality`.
* `AlgebraicGeometry.natCard_ker_compactSupportRepresentationHomology_map_zero`:
  `#ker T₀(v) = #ker (v_{π₁(X_k̄)} : M_{π₁(X_k̄)} → M'_{π₁(X_k̄)})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Iso

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar]

/-- **`T₀(ρ) ≅ H²_c(X_k̄, ℱ_ρ)`** for the homological δ-functor
`AlgebraicGeometry.compactSupportRepresentationHomology`. -/
def compactSupportRepresentationHomologyZeroIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
    ((compactSupportRepresentationHomology B X x Λ f j kbar).functor 0).obj M ≅
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X x Λ).obj M)) ((2 : ℕ) : ℤ) :=
  letI := etaleModules_enoughInjectives.{u, 0} Λ (geometricSmoothModel f j kbar).Vb
  letI := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  (Stacks.DerivedIndexing.rightDerivedIso _ 2).app _ ≪≫
    (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M)
      ((2 : ℕ) : ℤ)).symm

/-- **`T₀(ρ) ≅ H²_c(X_k̄, ℱ_ρ)` is natural in `ρ`.** -/
theorem compactSupportRepresentationHomologyZeroIso_hom_naturality
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (v : M ⟶ M') :
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
    ((compactSupportRepresentationHomology B X x Λ f j kbar).functor 0).map v ≫
        (compactSupportRepresentationHomologyZeroIso B X x Λ f j kbar M').hom =
      (compactSupportRepresentationHomologyZeroIso B X x Λ f j kbar M).hom ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X x Λ).map v))) := by
  let := etaleModules_enoughInjectives.{u, 0} Λ (geometricSmoothModel f j kbar).Vb
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  have h₁ := (Stacks.DerivedIndexing.rightDerivedIso
    (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) 2).hom.naturality
      ((compactSupportRepresentationSheaf B X x Λ f j kbar).map v)
  have h₂ := galoisCompactSupportSmoothModelIso_hom_naturality f j kbar Λ
    ((representationSheaf B X x Λ).map v) ((2 : ℕ) : ℤ)
  have h₂' : (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M)
      ((2 : ℕ) : ℤ)).inv ≫ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ)
        ((2 : ℕ) : ℤ)).map (galoisCompactSupportCohomologyMap Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
            ((representationSheaf B X x Λ).map v))) =
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          ((2 : ℕ) : ℤ)).map ((compactSupportRepresentationSheaf B X x Λ f j kbar).map v) ≫
        (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M')
          ((2 : ℕ) : ℤ)).inv := by
    refine (Iso.inv_comp_eq _).2 ?_
    exact ((Iso.eq_comp_inv _).2 h₂).trans (Category.assoc _ _ _)
  simp only [compactSupportRepresentationHomologyZeroIso]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂'.symm)))

end Iso

section Coinvariants

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- Kernels of two linear maps intertwined by linear equivalences have the same cardinality. -/
theorem natCard_ker_eq_of_comp_eq {R : Type*} [Ring R] {A A' C C' : Type*} [AddCommGroup A]
    [Module R A] [AddCommGroup A'] [Module R A'] [AddCommGroup C] [Module R C] [AddCommGroup C']
    [Module R C'] (g : A →ₗ[R] C) (g' : A' →ₗ[R] C') (e : A ≃ₗ[R] A') (e' : C ≃ₗ[R] C')
    (h : g' ∘ₗ e.toLinearMap = e'.toLinearMap ∘ₗ g) :
    Nat.card (LinearMap.ker g) = Nat.card (LinearMap.ker g') := by
  refine Nat.card_congr ((e.ofSubmodules _ _ ?_).toEquiv)
  ext a'
  have key := congrArg (fun φ ↦ φ (e.symm a')) h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply] at key
  simp [Submodule.mem_map_equiv, key]

include hn in
/-- **`#ker T₀(v) = #ker (v_{π₁(X_k̄)})`**: the kernel of `H²_c(X_k̄, ℱ_v)` has as many elements as
the kernel of the map `v` induces on coinvariants of the geometric fundamental group
(Lemma 03VK). -/
theorem natCard_ker_compactSupportRepresentationHomology_map_zero
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ') :
    letI := connectedSpace_of_isCurve B X f
    Nat.card (LinearMap.ker
        (((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 0).map v).hom) =
      Nat.card (LinearMap.ker (geometricCoinvariantsMap B X f kbar Λ y v)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  have hnat := compactSupportRepresentationHomologyZeroIso_hom_naturality B X _ Λ f j kbar v
  have hθ := compactSupportGeometricCoinvariantsMap_naturality B X f kbar Λ y j hn hζ v
  refine natCard_ker_eq_of_comp_eq _ _
    ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).toLinearEquiv ≪≫ₗ
      compactSupportGeometricCoinvariantsEquiv B X f kbar Λ y j hn hζ ρ)
    ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ').toLinearEquiv ≪≫ₗ
      compactSupportGeometricCoinvariantsEquiv B X f kbar Λ y j hn hζ ρ') ?_
  apply LinearMap.ext
  intro a
  have h1 := congrArg (fun φ ↦ φ.hom a) hnat
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
  have h2 := congrArg (fun φ ↦ φ ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar
    ρ).hom.hom a)) hθ
  simp only [LinearMap.coe_comp, Function.comp_apply] at h2
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, compactSupportGeometricCoinvariantsEquiv,
    LinearEquiv.ofBijective_apply]
  rw [h1]
  exact h2.symm

end Coinvariants

end AlgebraicGeometry

end
