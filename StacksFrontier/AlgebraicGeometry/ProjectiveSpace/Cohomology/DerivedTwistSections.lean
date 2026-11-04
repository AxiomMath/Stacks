module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOverSingle
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.RingTheory.MvPolynomial.HomogeneousBasis
import all StacksFrontier.Homology.RelativelyPerfect.FlatComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived global sections of the twists `𝒪(e)`, `-n ≤ e`, on `ℙⁿ_A`

Let `A` be a ring and `X = ℙⁿ_A`. For `e ≥ -n` the twist `𝒪(e)` has no higher cohomology
([Stacks, Tag 01XT]), so `RΓ(X, 𝒪(e)[0])` is the finite free `A`-module `Γ(X, 𝒪(e))` placed in
degree zero: it lies in `D^{≤ 0}(A)` and is pseudo-coherent.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.isZero_rightDerived_twistingSheaf`
* `Stacks.ProjectiveSpace.Cohomology.isLE_derivedGlobalSectionsOver_twistingSheaf`
* `Stacks.ProjectiveSpace.Cohomology.isPseudoCoherent_derivedGlobalSectionsOver_twistingSheaf`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.Cohomology

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The underlying space of `ℙⁿ_A = Proj A[X₀, …, Xₙ]` is compact. -/
instance compactSpace_proj_polyGrading :
    CompactSpace (AlgebraicGeometry.Proj (polyGrading A n)) :=
  QuasiCompact.compactSpace_of_compactSpace (AlgebraicGeometry.Proj.toSpecZero (polyGrading A n))

/-- The underlying space of `ℙⁿ_A = Proj A[X₀, …, Xₙ]` is quasi-separated. -/
instance quasiSeparatedSpace_proj_polyGrading :
    QuasiSeparatedSpace (AlgebraicGeometry.Proj (polyGrading A n)) :=
  (quasiSeparatedSpace_iff_quasiSeparated _).2 inferInstance

/-- **`Hᵖ(ℙⁿ_A, 𝒪(e)) = 0` for `p > 0` and `e ≥ -n`** ([Stacks, Tag 01XT]). -/
theorem isZero_rightDerived_twistingSheaf (e : ℤ) (he : -(n : ℤ) ≤ e) (p : ℕ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading A n))
      ⊤).rightDerived p).obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) e)) := by
  have h : IsZero (twistCohomology A n e p) := by
    by_cases hpn : p = n ∧ e < 0
    · obtain ⟨rfl, he'⟩ := hpn
      refine (twistCohomologyIsoNegative A p e he').isZero_iff.2 ?_
      have : Subsingleton (negativeTwistPart A p e) := by
        rw [negativeTwistPart_eq_bot_of_le (R := A) (n := p) (d := e) he]
        infer_instance
      exact ModuleCat.isZero_of_subsingleton _
    · exact isZero_twistCohomology A n e p (by omega)
  have hs : Subsingleton (twistCohomology A n e p) := ModuleCat.subsingleton_of_isZero h
  exact ModuleCat.isZero_iff_subsingleton.2 hs

/-- `Γ(ℙⁿ_A, 𝒪(e))` as an `A`-module through the structure morphism is `H⁰(ℙⁿ_A, 𝒪(e))` of
[Stacks, Tag 01XT]. -/
def globalSectionsOverTwistingSheafIso (e : ℤ) :
    (globalSectionsOver (projToSpecCoeff A n)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) e) ≅
      twistCohomology A n e 0 :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A n)).mapIso
    ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading A n))
      ⊤).rightDerivedZeroIsoSelf.app _).symm

/-- **`RΓ(ℙⁿ_A, 𝒪(e)[0]) = Γ(ℙⁿ_A, 𝒪(e))[0]`** for `e ≥ -n`. -/
@[ega "III 2.1.12" "(i), special case"]
def derivedGlobalSectionsOverTwistingSheafIso (e : ℤ) (he : -(n : ℤ) ≤ e) :
    (derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) e)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (twistCohomology A n e 0) :=
  derivedGlobalSectionsOverSingleIso (projToSpecCoeff A n) _
      (hqcF := Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf A n e)
      (isZero_rightDerived_twistingSheaf A n e he) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (globalSectionsOverTwistingSheafIso A n e)

/-- `RΓ(ℙⁿ_A, 𝒪(e)[0])` is concentrated in degrees `≤ 0` for `e ≥ -n`. -/
@[ega "III 2.1.12" "(i), special case"]
theorem isLE_derivedGlobalSectionsOver_twistingSheaf (e : ℤ) (he : -(n : ℤ) ≤ e) :
    ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) e))).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso
    (derivedGlobalSectionsOverTwistingSheafIso A n e he).symm 0

/-- `RΓ(ℙⁿ_A, 𝒪(e)[0])` is a pseudo-coherent object of `D(A)` for `e ≥ -n`: it is a finite free
module in degree zero, the module of degree-`e` forms for `e ≥ 0` and zero for `e < 0`. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_twistingSheaf (e : ℤ) (he : -(n : ℤ) ≤ e) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) e))) := by
  refine StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso ?_
    (derivedGlobalSectionsOverTwistingSheafIso A n e he).symm
  rcases le_or_gt 0 e with h | h
  · exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
      (PseudoCoherence.pseudoCoherent_single_of_finite_free
        (ModuleCat.of A (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A e.toNat)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (twistCohomologyIsoHomogeneous A n e h).symm)
  · refine (StacksDraft.PseudoCoherence.pseudoCoherent_of_isZero _ ?_).1
    refine (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map_isZero ?_
    exact isZero_twistCohomology A n e 0 (by omega)

end Stacks.ProjectiveSpace.Cohomology

end
