module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionReduction
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonResolved
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.DiagonalTransport

/-!
# Detecting the derived-Hom base-change morphism by the tensor--Hom diagonal

For a Tor-independent square of commutative rings `R → A`, `R → R'`, `A' = A ⊗_R R'`, the
base-change morphism `RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')` of Stacks 0E29 is invertible
exactly when the tensor--Hom diagonal `RHom_R(A, K) ⊗ᴸ_R R' ⟶ RHom_R(A, K ⊗ᴸ_R R')` of Stacks 0BYN
is (Stacks 0E2A). The diagonal is read over `ULift R` through the scalar equivalence of
Stacks 0E1W.

## Main definitions

* `Dualizing.DiagonalLiftInvariance`: the diagonal `Dualizing.derivedTensorHomDiagonalOverRing`
  over `R` is invertible at the lift universe `max v uR uA uRp` exactly when it is at
  `max v uA uRp`.

## Main results

* `Dualizing.isIso_derivedTensorHomDiagonalModel_iff`: `Dualizing.derivedTensorHomDiagonalModel` is
  invertible exactly when the diagonal of Stacks 0BYN over `ULift R` is.
* `Dualizing.isIso_derivedHomBaseChange_app_iff_of_projectionCompatibility`: under
  `Dualizing.ProjectionFormulaCompatibility`, the morphism of Stacks 0E29 is invertible at `K`
  exactly when the derived-Hom base-change morphism of Stacks 0E1X along `R → R'` is invertible at
  the algebra and at `K`.
* `Dualizing.isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonal`: under
  `Dualizing.ProjectionFormulaCompatibility`, the morphism of Stacks 0E29 is invertible at `K`
  exactly when the diagonal of Stacks 0BYN over `ULift R` is.
* `Dualizing.isIso_derivedHomBaseChange_app_iff_diagonal`: Stacks 0E2A, with no compatibility
  hypothesis.
* `Dualizing.isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel`,
  `Dualizing.isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel_canonical` and
  `Dualizing.isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel_of_isZero`: the same
  equivalence with `Dualizing.derivedTensorHomDiagonalModel`, under
  `Dualizing.ProjectionFormulaCompatibility`, under its canonical form, and when the derived base
  change of the algebra vanishes.
* `Dualizing.derivedHomBaseChange_isIso_iff_diagonal`: the same equivalence with
  `Dualizing.derivedTensorHomDiagonalOverRing`, assuming `Dualizing.DiagonalLiftInvariance`.
* `Dualizing.diagonalLiftInvariance_ringUniverseEqAlgebra`,
  `Dualizing.diagonalLiftInvariance_ringUniverseEqBaseChange` and
  `Dualizing.diagonalLiftInvariance_ringUniverseEqModule`: `Dualizing.DiagonalLiftInvariance` holds
  when the ring universe of `R` is that of the algebra, of the base-change ring, or of the module
  size.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

universe uR uA uRp v

namespace Dualizing

/-- A morphism flanked by two isomorphisms is invertible exactly when the morphism is. -/
private theorem isIso_comp_comp_iff {C : Type*} [Category C] {X Y Z W : C}
    (a : X ⟶ Y) [IsIso a] (g : Y ⟶ Z) (b : Z ⟶ W) [IsIso b] :
    IsIso (a ≫ g ≫ b) ↔ IsIso g := by
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- A morphism `e.hom ≫ g ≫ e'.inv` is invertible exactly when `g` is. -/
private theorem isIso_hom_comp_comp_inv_iff {C : Type*} [Category C] {X Y Z W : C}
    (e : X ≅ Y) (g : Y ⟶ Z) (e' : W ≅ Z) :
    IsIso (e.hom ≫ g ≫ e'.inv) ↔ IsIso g :=
  isIso_comp_comp_iff e.hom g e'.inv

/-- If `F.map f` is `e.hom ≫ g ≫ e'.inv` and `f` is invertible whenever `F.map f` is, then `f` is
invertible exactly when `g` is. -/
private theorem isIso_iff_of_map_eq_hom_comp_comp_inv {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {f : X ⟶ Y} (hF : IsIso (F.map f) → IsIso f) {P Q : D} {g : P ⟶ Q}
    (e : F.obj X ≅ P) (e' : F.obj Y ≅ Q) (heq : F.map f = e.hom ≫ g ≫ e'.inv) :
    IsIso f ↔ IsIso g := by
  rw [← isIso_hom_comp_comp_inv_iff e g e', ← heq]
  exact ⟨fun _ => inferInstance, hF⟩

section Model

attribute [local instance] HasDerivedCategory.standard

/-- `Dualizing.derivedTensorHomDiagonalModel K L M` is invertible exactly when the canonical
diagonal of Stacks 0BYN over `ULift R`, at the images of `K`, `L` and `M` under the scalar
equivalence of Stacks 0E1W, is invertible. -/
theorem isIso_derivedTensorHomDiagonalModel_iff {R : Type uR} [CommRing R]
    (K L M : DerivedCategory (ModuleCat.{max uR v} R)) :
    IsIso (derivedTensorHomDiagonalModel.{uR, v} K L M) ↔
      IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v} R).functor.obj K)
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v} R).functor.obj L)
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v} R).functor.obj
          M)) := by
  rw [derivedTensorHomDiagonalModel]
  refine Iff.trans ?_ (isIso_comp_comp_iff
    (derivedTensorHomDiagonalModelSource.{uR, v} K L M).hom
    (DerivedInternalHom.Model.diagonal
      ((derivedScalarEquivalence.{uR, v} R).inverse.obj K)
      ((derivedScalarEquivalence.{uR, v} R).inverse.obj L)
      ((derivedScalarEquivalence.{uR, v} R).inverse.obj M))
    (derivedTensorHomDiagonalModelTarget.{uR, v} K L M).hom)
  exact isIso_iff_of_reflects_iso _ (derivedScalarEquivalence.{uR, v} R).functor

end Model

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

/-- Under `Dualizing.ProjectionFormulaCompatibility`, the base-change morphism of Stacks 0E29 is
invertible at `K` exactly when the derived-Hom base-change morphism of Stacks 0E1X along `R → R'`
is invertible at the algebra and at `K`. -/
theorem isIso_derivedHomBaseChange_app_iff_of_projectionCompatibility
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K) ↔
      IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
        (algebraMap R R')
        baseChangeR comparisonR
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K) := by
  have heq := restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility
    hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    Ff alphaf Fi alphai K hProj
  exact isIso_iff_of_map_eq_hom_comp_comp_inv _ (isIso_derivedHomBaseChange_app_of_restrictScalars
    hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA K) _ _ heq

/-- Under `Dualizing.ProjectionFormulaCompatibility`, the base-change morphism of Stacks 0E29 is
invertible at `K` exactly when the tensor--Hom diagonal
`StacksDraft.DerivedHom.derivedTensorHomDiagonal` of Stacks 0BYN at `R'`, `K` and `A` is, with `R'`
and `A` read as degree-zero complexes of `R`-modules and all three read over `ULift R` through the
scalar equivalence of Stacks 0E1W. -/
theorem isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonal
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K) ↔
      (let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA
        uRp} R
       IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
         (E.functor.obj ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
           ((ModuleCat.restrictScalars (algebraMap R R')).obj
             (ModuleCat.of R' (ULift.{max v uR uA} R')))))
         (E.functor.obj K)
         (E.functor.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) : Prop) := by
  refine Iff.trans (isIso_derivedHomBaseChange_app_iff_of_projectionCompatibility hTor
    baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    Ff alphaf Fi alphai K hProj) ?_
  have := isLeftDerivedR
  exact isIso_derivedHomBaseChange_iff_derivedTensorHomDiagonal.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR
    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K

/-- For `R → A` and `R → R'` with `A` and `R'` Tor independent over `R`, and `A' = A ⊗_R R'`, the
base-change morphism `RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')` of Stacks 0E29 is an
isomorphism exactly when the morphism `RHom_R(A, K) ⊗ᴸ_R R' ⟶ RHom_R(A, K ⊗ᴸ_R R')` of Stacks 0BYN
is, read over `ULift R` through the scalar equivalence of Stacks 0E1W. -/
@[stacks 0E2A]
theorem isIso_derivedHomBaseChange_app_iff_diagonal
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K) ↔
      (let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA
        uRp} R
       IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
         (E.functor.obj ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
           ((ModuleCat.restrictScalars (algebraMap R R')).obj
             (ModuleCat.of R' (ULift.{max v uR uA} R')))))
         (E.functor.obj K)
         (E.functor.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) : Prop) := by
  have := isLeftDerivedR
  have := isLeftDerivedA
  obtain ⟨sIso, tIso, heq⟩ := exists_restrictScalars_map_derivedHomBaseChange_app_eq.{uR, uA, uRp,
    v} hTor baseChangeR comparisonR baseChangeA comparisonA K
  refine (isIso_iff_of_map_eq_hom_comp_comp_inv _
    (isIso_derivedHomBaseChange_app_of_restrictScalars hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K) _ _ heq).trans ?_
  exact isIso_derivedHomBaseChange_iff_derivedTensorHomDiagonal.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR
    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K

/-- Under `Dualizing.ProjectionFormulaCompatibility`, the base-change morphism of Stacks 0E29 is
invertible at `K` exactly when `Dualizing.derivedTensorHomDiagonalModel` is invertible at the
base-change ring, at `K` and at the algebra. -/
theorem isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K) ↔
      IsIso (derivedTensorHomDiagonalModel.{uR, max v uR uA uRp}
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
          ((ModuleCat.restrictScalars (algebraMap R R')).obj
            (ModuleCat.of R' (ULift.{max v uR uA} R')))) K
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) :=
  (isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonal hTor baseChangeR comparisonR
      isLeftDerivedR baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K hProj).trans
    (isIso_derivedTensorHomDiagonalModel_iff.{uR, max v uR uA uRp} _ _ _).symm

/-- `Dualizing.isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel` at the canonical
derived extension models, under `Dualizing.ProjectionFormulaCompatibilityCanonical`. -/
theorem isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel_canonical
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K) ↔
      IsIso (derivedTensorHomDiagonalModel.{uR, max v uR uA uRp}
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
          ((ModuleCat.restrictScalars (algebraMap R R')).obj
            (ModuleCat.of R' (ULift.{max v uR uA} R')))) K
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) :=
  @isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel R A R' _ _ _ _ _ hTor
    baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived
    K hProj

/-- If the derived base change of the algebra to `R'` vanishes, the base-change morphism of
Stacks 0E29 is invertible at `K` exactly when `Dualizing.derivedTensorHomDiagonalModel` is
invertible at the base-change ring, at `K` and at the algebra. -/
theorem isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel_of_isZero
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hz : Limits.IsZero
      (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K) ↔
      IsIso (derivedTensorHomDiagonalModel.{uR, max v uR uA uRp}
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
          ((ModuleCat.restrictScalars (algebraMap R R')).obj
            (ModuleCat.of R' (ULift.{max v uR uA} R')))) K
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) :=
  isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel_canonical hTor baseChangeR
    comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA K
    (projectionFormulaCompatibilityCanonical_of_isZero_baseChangeAlgebra hTor baseChangeR
      comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA hz K)

section Presentation

/-- For all `K`, `L`, `M` in `D(R)`, the diagonal `Dualizing.derivedTensorHomDiagonalOverRing` of
the adjunction of Stacks 0A63, transported from the lift of `R` at universe `max v uR uA uRp`, is
invertible exactly when the one transported from the lift at universe `max v uA uRp` is. -/
def DiagonalLiftInvariance (R : Type uR) [CommRing R] : Prop :=
  ∀ K L M : DerivedCategory (ModuleCat.{max v uR uA uRp} R),
    IsIso (derivedTensorHomDiagonalOverRing.{uR, max v uR uA uRp} K L M) ↔
      IsIso (derivedTensorHomDiagonalOverRing.{uR, max v uA uRp} K L M)

/-- Under `Dualizing.DiagonalLiftInvariance` and `Dualizing.ProjectionFormulaCompatibility`, the
base-change morphism of Stacks 0E29 is invertible at `K` exactly when the tensor--Hom diagonal
`Dualizing.derivedTensorHomDiagonalOverRing` is invertible at the base-change ring, at `K` and at
the algebra. -/
theorem derivedHomBaseChange_isIso_iff_diagonal
    (hlift : DiagonalLiftInvariance.{uR, uA, uRp, v} R)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj : ProjectionFormulaCompatibility hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA Ff alphaf Fi alphai K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K) ↔
      IsIso (derivedTensorHomDiagonalOverRing.{uR, max v uA uRp}
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
          ((ModuleCat.restrictScalars (algebraMap R R')).obj
            (ModuleCat.of R' (ULift.{max v uR uA} R')))) K
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) := by
  refine Iff.trans (isIso_derivedHomBaseChange_app_iff_derivedTensorHomDiagonalModel hTor
    baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    Ff alphaf Fi alphai K hProj) ?_
  rw [derivedTensorHomDiagonalModel_eq_overRing.{uR, max v uR uA uRp}]
  exact hlift _ _ _

end Presentation

section LiftInvarianceWitnesses

attribute [local instance] HasDerivedCategory.standard

/-- `Dualizing.DiagonalLiftInvariance` holds when the ring universe of `R` is the universe of the
algebra. -/
theorem diagonalLiftInvariance_ringUniverseEqAlgebra {R : Type uA} [CommRing R] :
    DiagonalLiftInvariance.{uA, uA, uRp, v} R :=
  fun _ _ _ => Iff.rfl

/-- `Dualizing.DiagonalLiftInvariance` holds when the ring universe of `R` is the universe of the
base-change ring `R'`. -/
theorem diagonalLiftInvariance_ringUniverseEqBaseChange {R : Type uRp} [CommRing R] :
    DiagonalLiftInvariance.{uRp, uA, uRp, v} R :=
  fun _ _ _ => Iff.rfl

/-- `Dualizing.DiagonalLiftInvariance` holds when the ring universe of `R` is the module-size
universe. -/
theorem diagonalLiftInvariance_ringUniverseEqModule {R : Type v} [CommRing R] :
    DiagonalLiftInvariance.{v, uA, uRp, v} R :=
  fun _ _ _ => Iff.rfl

end LiftInvarianceWitnesses

end Dualizing

end
