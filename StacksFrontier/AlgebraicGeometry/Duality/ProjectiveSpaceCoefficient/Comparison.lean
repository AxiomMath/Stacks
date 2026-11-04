module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.Trace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistedInverseImageProjToSpec
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# The trace `Rp_*((𝒪(-n-1) ⊗ p^*M~)[n]) ≅ M~`

## Main definitions

* `Stacks.Duality.ProjCoeff.Gqc`: `(𝒪(-n-1) ⊗ p^*M~)[n]` in `D_QCoh(ℙⁿ_R)`.
* `Stacks.Duality.ProjCoeff.Mqc`: `M~` in `D_QCoh(Spec R)`, as derived sheafification of `M[0]`.
* `Stacks.Duality.ProjCoeff.RΓ_Mqc_iso`: `RΓ(Spec R, M~) ≅ M[0]`.

## Main results

* `Stacks.Duality.ProjCoeff.nonempty_RΓ_Gqc_iso`: `RΓ(ℙⁿ_R, (𝒪(-n-1) ⊗ p^*M~)[n]) ≅ M[0]`.
* `Stacks.Duality.ProjCoeff.nonempty_trace`: `Rp_*((𝒪(-n-1) ⊗ p^*M~)[n]) ≅ M~` in `D_QCoh(Spec R)`.

The trace isomorphism `Stacks.Duality.ProjCoeff.traceIso` and its adjoint, the comparison map
`Stacks.Duality.ProjCoeff.comparison : (𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)`, are built from these in
`StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.ComparisonIso`.
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

/-- The `j`-th cohomology of `X⟦n⟧` is the `m`-th cohomology of `X`, where `n + j = m`. -/
private def homologyShiftIso {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X : DerivedCategory C) (n j m : ℤ) (h : n + j = m) :
    (DerivedCategory.homologyFunctor C j).obj (X⟦n⟧) ≅
      (DerivedCategory.homologyFunctor C m).obj X :=
  ((DerivedCategory.homologyFunctor C 0).shiftIso n j m h).app X

/-- Every cohomology sheaf of `(𝒪(-n-1) ⊗ p^*M~)[n]` on `ℙⁿ_R` is quasi-coherent. -/
theorem isQuasicoherent_homology_Gshift (M : ModuleCat.{u} R) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (P R n).Modules i).obj
      ((Gsingle R n M)⟦(n : ℤ)⟧)).IsQuasicoherent := by
  have hX := Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj
    ((T R n (-(n : ℤ) - 1)).obj M) (isQuasicoherent_T R n _ M)
  exact (SheafOfModules.isQuasicoherent (P R n).ringCatSheaf).prop_of_iso
    (homologyShiftIso (Gsingle R n M) n i (n + i) rfl).symm (hX (n + i))

/-- `(𝒪(-n-1) ⊗ p^*M~)[n]`, as an object of `D_QCoh(ℙⁿ_R)`. -/
def Gqc (M : ModuleCat.{u} R) : Stacks.Duality.quasiCoherentDerivedCategory (P R n) :=
  ⟨(Gsingle R n M)⟦(n : ℤ)⟧, isQuasicoherent_homology_Gshift R n M⟩

/-- `M~`, as an object of `D_QCoh(Spec R)`: the derived sheafification of `M[0]`. -/
def Mqc (M : ModuleCat.{u} R) : Stacks.Duality.quasiCoherentDerivedCategory (Spec (.of R)) :=
  (derivedTilde (.of R)).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)

/-- An object of `D(R)` whose cohomology is concentrated in degree `0`, where it is `M`, is
`M[0]`. -/
theorem nonempty_iso_single_of_homology {X : DerivedCategory (ModuleCat.{u} R)}
    {M : ModuleCat.{u} R}
    (h : ∀ j : ℤ, j ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj X))
    (e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X ≅ M) :
    Nonempty (X ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  obtain ⟨e'⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero X 0 h
  exact ⟨e' ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e⟩

/-- `RΓ(ℙⁿ_R, (𝒪(-n-1) ⊗ p^*M~)[n]) ≅ M[0]`. -/
theorem nonempty_RΓ_Gqc_iso (M : ModuleCat.{u} R) :
    Nonempty ((derivedGlobalSectionsOver (projToSpecCoeff R n)).obj (Gqc R n M).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  let F := derivedGlobalSectionsOver (projToSpecCoeff R n)
  let e₁ : F.obj (Gqc R n M).obj ≅ (F.obj (Gsingle R n M))⟦(n : ℤ)⟧ :=
    (F.commShiftIso (n : ℤ)).app (Gsingle R n M)
  refine ⟨e₁ ≪≫ (nonempty_iso_single_of_homology R ?_ ?_).some⟩
  · intro j hj
    exact (homologyShiftIso (F.obj (Gsingle R n M)) n j (n + j) rfl).isZero_iff.2
      (isZero_homology_RΓ_Gsingle R n M (n + j) (by omega))
  · exact homologyShiftIso (F.obj (Gsingle R n M)) n 0 n (by omega) ≪≫ homologyRΓTopIso R n M

/-- `RΓ(Spec R, M~) ≅ M[0]`. -/
def RΓ_Mqc_iso (M : ModuleCat.{u} R) :
    (derivedGlobalSectionsQuasicoherent (.of R)).obj (Mqc R M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M :=
  have := derivedTilde_isEquivalence (.of R)
  have := derivedGlobalSectionsQuasicoherent_isEquivalence (.of R)
  (asIso ((derivedTildeQuasicoherentAdjunction (.of R)).unit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))).symm

/-- Pullback of sheaves of modules along the flat morphism `ℙⁿ_R ⟶ Spec R` preserves finite
limits. -/
instance : Limits.PreservesFiniteLimits (Scheme.Modules.pullback (projToSpecCoeff R n)) :=
  AlgebraicGeometry.preservesFiniteLimits_pullback_of_flat (projToSpecCoeff R n)

/-- **The trace with coefficients**, `Rp_*((𝒪(-n-1) ⊗ p^*M~)[n]) ≅ M~` in `D_QCoh(Spec R)`. -/
theorem nonempty_trace (M : ModuleCat.{u} R) :
    Nonempty ((Stacks.ProjectiveSpace.Cohomology.quasiCoherentDerivedPushforwardProjToSpec R n).obj
      (Gqc R n M) ≅ Mqc R M) := by
  have := derivedGlobalSectionsQuasicoherent_isEquivalence (.of R)
  let E := derivedGlobalSectionsQuasicoherent (.of R)
  have e₁ : E.obj ((Stacks.ProjectiveSpace.Cohomology.quasiCoherentDerivedPushforwardProjToSpec
      R n).obj (Gqc R n M)) ≅ (derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
        (Gqc R n M).obj :=
    ((derivedGlobalSectionsOverIsoDerivedPushforward (projToSpecCoeff R n)).app
      (Gqc R n M).obj).symm
  exact ⟨E.preimageIso (e₁ ≪≫ (nonempty_RΓ_Gqc_iso R n M).some ≪≫ (RΓ_Mqc_iso R M).symm)⟩

end Stacks.Duality.ProjCoeff
