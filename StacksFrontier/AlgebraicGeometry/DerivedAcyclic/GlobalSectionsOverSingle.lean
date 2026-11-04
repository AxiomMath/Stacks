module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOverABase
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers

/-!
# Derived global sections of an acyclic quasi-coherent module

Let `X` be a quasi-compact quasi-separated scheme over a commutative ring `A` and let `F` be a
quasi-coherent `𝒪_X`-module with `Hⁱ(X, F) = 0` for all `i > 0`. Then `RΓ(X, F[0])` is the
module `Γ(X, F)` placed in degree zero, in `D(A)`.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsOverSingleIso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology (sectionsFunctor)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]

/-- **`RΓ(X, F[0]) = Γ(X, F)[0]`** for a quasi-coherent module `F` without higher cohomology,
in `D(A)`: the module is acyclic for global sections, so global sections of `F[0]` compute the
derived global sections ([Stacks, Tag 0G9P]). -/
def derivedGlobalSectionsOverSingleIso (F : X.Modules) [hqcF : F.IsQuasicoherent]
    (hF : ∀ p : ℕ, 0 < p → IsZero (((sectionsFunctor X ⊤).rightDerived p).obj F)) :
    (derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj ((globalSectionsOver f).obj F) := by
  let K := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F
  have hqc : ∀ n, (K.X n).IsQuasicoherent := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm hqcF
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have hacyclic : ∀ n, (sectionsFunctor X ⊤).rightAcyclic (K.X n) := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · exact (sectionsFunctor X ⊤).rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm
        ((CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ F).2 hF)
    · refine (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp => ?_
      have := (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn).injective
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      exact (sectionsFunctor X ⊤).isZero_rightDerived_obj_injective_succ q (K.X n)
  have hiso := isIso_derivedGlobalSectionsOverUnit_app_of_termwise_acyclic f K hqc hacyclic
  exact (derivedGlobalSectionsOver f).mapIso
      (((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F) ≪≫
        ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm) ≪≫
    (asIso ((derivedGlobalSectionsOverUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K))).symm ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (globalSectionsOver f)
        (ComplexShape.up ℤ) 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app _).symm

end AlgebraicGeometry

end
