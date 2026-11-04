module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.TwistHom
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CanonicalTwistDerived

/-!
# The trace of `ℙⁿ_R ⟶ Spec R` with coefficients

For an `R`-module `M`, write `G_M = (𝒪(-n-1) ⊗ p^*M~)[n]` on `ℙⁿ_R`. Derived global sections
of `G_M` are `M` placed in degree zero: the cohomology of `𝒪(-n-1) ⊗ p^*M~` is concentrated in
degree `n`, where it is `M`.

## Main definitions

* `Stacks.Duality.ProjCoeff.Gsingle`: The complex `(𝒪(-n-1) ⊗ p^*M~)[0]` on `ℙⁿ_R`.
* `Stacks.Duality.ProjCoeff.homologyRΓTopIso`: `Hⁿ(RΓ(ℙⁿ_R, (𝒪(-n-1) ⊗ p^*M~)[0])) ≅ M`.

## Main results

* `Stacks.Duality.ProjCoeff.isZero_homology_RΓ_Gsingle`: For `q ≠ n`, the `q`-th cohomology of
  `RΓ(ℙⁿ_R, (𝒪(-n-1) ⊗ p^*M~)[0])` vanishes.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable (R : Type u) [CommRing R] (n : ℕ)

/-- `(𝒪(-n-1) ⊗ p^*M~)[0]`, as an object of the derived category of `𝒪_{ℙⁿ_R}`-modules. -/
abbrev Gsingle (M : ModuleCat.{u} R) : DerivedCategory (P R n).Modules :=
  (DerivedCategory.singleFunctor (P R n).Modules 0).obj ((T R n (-(n : ℤ) - 1)).obj M)

/-- The cohomology of `RΓ(ℙⁿ_R, (𝒪(-n-1) ⊗ p^*M~)[0])` is that of the module, as `R`-modules. -/
def homologyRΓIso (M : ModuleCat.{u} R) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (q : ℤ)).obj
        ((derivedGlobalSectionsOver (projToSpecCoeff R n)).obj (Gsingle R n M)) ≅
      (ModuleCat.restrictScalars.{u} (Stacks.ProjectiveSpace.Cohomology.coeffScalar R n)).obj
        ((H R n q).obj ((T R n (-(n : ℤ) - 1)).obj M)) :=
  ((Stacks.Duality.rightDerivedGlobalSectionsIsoDerivedCohomology
      (projToSpecCoeff R n) q).app _).symm ≪≫
    ((Stacks.Duality.rightDerivedCompRestrictScalarsIso
      (Stacks.ProjectiveSpace.Cohomology.coeffScalar R n)
      (Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n)) ⊤)
      (hE := Stacks.Cohomology.sectionsFunctor_additive _ _)
      (AlgebraicGeometry.globalSectionsOver (projToSpecCoeff R n))
      (hH := AlgebraicGeometry.globalSectionsOver_additive _)
      (eqToIso (Stacks.ProjectiveSpace.Cohomology.globalSectionsOver_projToSpecCoeff R n).symm)
      q).app _).symm

/-- For `q ≠ n`, the `q`-th cohomology of `RΓ(ℙⁿ_R, (𝒪(-n-1) ⊗ p^*M~)[0])` vanishes. -/
theorem isZero_homology_RΓ_Gsingle (M : ModuleCat.{u} R) (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
      ((derivedGlobalSectionsOver (projToSpecCoeff R n)).obj (Gsingle R n M))) := by
  rcases lt_or_ge q 0 with h | h
  · have := Stacks.ProjectiveSpace.Cohomology.isGE_singleFunctor_obj (P R n)
      ((T R n (-(n : ℤ) - 1)).obj M)
    exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (AlgebraicGeometry.globalSectionsOver (projToSpecCoeff R n)) (Gsingle R n M) 0 q h
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = (m : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg h).symm⟩
    refine (homologyRΓIso R n M m).isZero_iff.2 ?_
    have hm : m ≠ n := by exact_mod_cast hq
    have h0 : IsZero ((H R n m).obj ((T R n (-(n : ℤ) - 1)).obj M)) := by
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · exact isZero_H_T_canonical_of_lt R n m hlt M
      · exact isZero_H_T_canonical_of_gt R n m hgt M
    rw [ModuleCat.isZero_iff_subsingleton] at h0 ⊢
    exact h0

/-- `Hⁿ(RΓ(ℙⁿ_R, (𝒪(-n-1) ⊗ p^*M~)[0])) ≅ M`. -/
def homologyRΓTopIso (M : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
        ((derivedGlobalSectionsOver (projToSpecCoeff R n)).obj (Gsingle R n M)) ≅ M :=
  homologyRΓIso R n M n ≪≫ topFunctorObjIso R n M

end Stacks.Duality.ProjCoeff
