module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpECyclotomicDerivedIsoOfIsUnit
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus

/-!
# `H⁰(Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀)))` has as many elements as `Hom_{π₁(X_k̄)}(M, μ_n)`

For a member `(M, I)` of the Poincaré family of Tag 03VM and an injective resolution `K₀` of
`j_! μ_n` on the compactification, `n = #Λ`, the complex `E = Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀))`
represents `RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))` (`AlgebraicGeometry.galoisHomOpERepresentationDerivedIso`).
So `H⁰(E) = Γ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`, whose underlying group is
`Γ(X_k̄, ℱ_{Hom(M, μ_n)}|) = Hom(M, μ_n)^{π₁(X_k̄)}`
(`AlgebraicGeometry.representationSheafHomOpIso`,
`AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv`).

## Main results

* `AlgebraicGeometry.natCard_homology_zero_galoisHomOpE_poincare`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

/-- Isomorphic objects of a concrete category have underlying types of equal cardinality. -/
private theorem natCard_obj_eq_of_iso {C : Type*} [Category C] (F : C ⥤ Type*) {X Y : C}
    (e : X ≅ Y) : Nat.card (F.obj X) = Nat.card (F.obj Y) :=
  Nat.card_congr (F.mapIso e).toEquiv

namespace Stacks.ContinuousCohomology

/-- **Cohomology of the underlying complex of abelian groups** of a complex of discrete
`R`-`Q`-modules has the cardinality of the cohomology of the complex: forgetting is exact. -/
theorem natCard_underlyingAb_homology {R : Type} [Ring R] {Q : Type u} [Group Q]
    [TopologicalSpace Q]
    (V : CochainComplex (Stacks.Injectives.ContinuousModule.{0, u, u + 1} R Q) ℤ) (i : ℤ) :
    Nat.card ((underlyingAb.{0, u, u + 1} R V).homology i) =
      Nat.card ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} R Q).obj
        (V.homology i)) := by
  have := Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{0, u, u + 1}
    R Q
  have := Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{0, u, u + 1}
    R Q
  have := Stacks.GroupCohomology.additive_continuousModuleToModuleCat.{0, u, u + 1} R Q
  let U := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} R Q
  have e₁ : (underlyingAb.{0, u, u + 1} R V).homology i ≅
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj
        (((U.mapHomologicalComplex _).obj V).homology i) :=
    (((U.mapHomologicalComplex _).obj V).sc i).mapHomologyIso
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  have e₂ : ((U.mapHomologicalComplex _).obj V).homology i ≅ U.obj (V.homology i) :=
    (V.sc i).mapHomologyIso U
  exact (natCard_obj_eq_of_iso (forget AddCommGrpCat) e₁).trans
    (natCard_obj_eq_of_iso (forget (ModuleCat R)) e₂)

end Stacks.ContinuousCohomology

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology Stacks.AbelianInternalHom Stacks.ConstantSheaf

attribute [local instance] HasDerivedCategory.standard

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the
coefficient universe `0`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_bc2Count (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- The cardinality of a finite ring is nonzero. -/
local instance neZero_fintypeCard_bc2Count (Λ : Type) [Ring Λ] [Fintype Λ] :
    NeZero (Fintype.card Λ) :=
  ⟨Fintype.card_ne_zero⟩

section Generic

variable {Λ : Type} [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

/-- **`H⁰` of a complex representing `RΓ^Gal(Y, H)` is `Γ^Gal(Y, H)`**, for a sheaf `H` of
`Λ`-modules on `Y_étale`. -/
def homologyZeroIsoGaloisGlobalSectionsOfDerivedIso (E : CochainComplex (GaloisModules Λ k kbar) ℤ)
    (H : EtaleModules.{u, 0} Λ Y.left)
    (e : DerivedCategory.Q.obj E ≅ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      galoisDerivedGlobalSections Λ Y kbar ⋙ DerivedCategory.Plus.ι).obj H) :
    E.homology 0 ≅ (galoisGlobalSections Λ Y kbar).obj H :=
  ((DerivedCategory.homologyFunctorFactors _ 0).app E).symm ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
    (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (galoisGlobalSections Λ Y kbar)).app H

end Generic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (Λ : Type) [Ring Λ] [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod (Fintype.card Λ)) j.immersion).obj
          ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))))
  [K₀.cocomplex.IsStrictlyGE 0]

omit [Smooth f] [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- `Γ(X_k̄, ℋom_ℤ(ℱ_M, ℱ_μ)|)` has as many elements as `Hom_{π₁(X_k̄)}(M, μ_n)`. -/
theorem natCard_globalSections_homOpSheaf_cyclotomic
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    Nat.card ((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ (Fintype.card Λ)
              (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))).obj (Opposite.op M)))) =
      Nat.card ((geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op M)) := by
  let := connectedSpace_of_isCurve B X f
  refine (natCard_obj_eq_of_iso (forget _)
    ((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar)).mapIso
      ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj (Over.mk f) kbar)).mapIso
        (representationSheafHomOpIso B X _ Λ (Fintype.card Λ)
          (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)) M)))).trans ?_
  exact Nat.card_congr
    (geometricGlobalSectionsInvariantsEquiv B X f kbar Λᵐᵒᵖ y
      ((cyclotomicDual B X f kbar y (Fintype.card Λ) Λ).obj (Opposite.op M))).toEquiv

/-- **(BC2-count)** `H⁰` of the underlying complex of `Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀))` has as many
elements as `Hom_{π₁(X_k̄)}(M, μ_n)` (the target of `geometricCyclotomicDualHomEquiv`). -/
theorem natCard_homology_zero_galoisHomOpE_poincare (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
    (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j) :
    letI := connectedSpace_of_isCurve B X f
    Nat.card ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).homology 0) =
      Nat.card ((geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op i.M)) := by
  let := connectedSpace_of_isCurve B X f
  refine (Stacks.ContinuousCohomology.natCard_underlyingAb_homology _ 0).trans ?_
  refine (natCard_obj_eq_of_iso (forget _)
    ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λᵐᵒᵖ (kbar ≃ₐ[k] kbar)).mapIso
      (homologyZeroIsoGaloisGlobalSectionsOfDerivedIso (Over.mk f) kbar _ _
        (galoisHomOpECyclotomicDerivedIsoOfIsUnit B X f kbar y (Fintype.card Λ) j K₀ Λ hn i.M
          i.I)))).trans ?_
  exact natCard_globalSections_homOpSheaf_cyclotomic B X f kbar Λ y i.M

/-- `H⁰` of the underlying complex of `Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀))` is finite. -/
theorem finite_homology_zero_galoisHomOpE_poincare (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
    (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j) :
    letI := connectedSpace_of_isCurve B X f
    Finite ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).homology 0) := by
  let := connectedSpace_of_isCurve B X f
  refine Nat.finite_of_card_ne_zero ?_
  rw [natCard_homology_zero_galoisHomOpE_poincare B X f kbar Λ y j K₀ hn i]
  let := connectedSpace_fieldBaseChange f kbar
  have hfin : Finite ((geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op i.M)) :=
    finite_pullbackRepresentationHomInvariants_obj (B := B) (X := X)
      (g := (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
      (y := y) (Λ := Λ) (n := Fintype.card Λ)
      (W := cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)) (ρ := i.M)
  exact Nat.card_ne_zero.2 ⟨inferInstance, hfin⟩

end AlgebraicGeometry

end
