module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.ProjTwistCommonMultiple.Basic

/-!
# The twisted inverse image of `P^n_A → Spec A` on the affine chart `D₊(T₀)`

Let `A` be a ring, `π : P^n_A = Proj A[T₀, …, Tₙ] ⟶ Spec A` the structure morphism, `a` the right
adjoint of `Rπ_*` on `D_QCoh`, and `j : D₊(T₀) ⟶ P^n_A` the inclusion of the standard open
`D₊(T₀)`, which is the affine space `Spec A[x₁, …, xₙ]` over `Spec A`. Then
`Lj^* a(𝒪_{Spec A}) ≅ 𝒪_{D₊(T₀)}[n]`: by `a(𝒪) ≅ 𝒪(-n-1)[n]` and the triviality of `𝒪(-n-1)` on
`D₊(T₀)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace Stacks.Duality.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (n : ℕ)

local notation "𝐏" => AlgebraicGeometry.Proj (polyGrading A n)

/-- The standard open `D₊(T₀)` of `P^n_A`. -/
abbrev chartOpen : (𝐏).Opens :=
  AlgebraicGeometry.Proj.basicOpen (polyGrading A n) (MvPolynomial.X 0)

/-- The open immersion `D₊(T₀) ⟶ P^n_A`. -/
abbrev chartι : (chartOpen A n).toScheme ⟶ 𝐏 := (chartOpen A n).ι

/-- The ring isomorphism `A[x₁, …, xₙ] ≅ A[T₀, …, Tₙ]_{(T₀)}`, `xⱼ ↦ Tⱼ/T₀`. -/
def chartRingIso : CommRingCat.of (MvPolynomial (Fin n) A) ≅
    CommRingCat.of (HomogeneousLocalization.Away (polyGrading A n) (MvPolynomial.X 0)) :=
  (MvPolynomial.renameEquiv A (finSuccAboveEquiv (0 : Fin (n + 1)))).toRingEquiv.toCommRingCatIso
    ≪≫ (chartEquiv A n 0).toCommRingCatIso

/-- **`D₊(T₀) ≅ Spec A[x₁, …, xₙ]`**: the degree-zero part of `A[T₀, …, Tₙ][1/T₀]` is the
polynomial ring in the `n` coordinates `Tⱼ/T₀`, `j ≠ 0`. -/
def chartIsoAffineSpace :
    (chartOpen A n).toScheme ≅ Spec (CommRingCat.of (MvPolynomial (Fin n) A)) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec (polyGrading A n) (MvPolynomial.X 0)
      (X_mem_one A n 0) Nat.one_pos ≪≫ Scheme.Spec.mapIso (chartRingIso A n).op

/-- **The chart is compatible with the projections to `Spec A`**: under `D₊(T₀) ≅ 𝔸ⁿ_A`, the
restriction of `π` is the projection `Spec A[x₁, …, xₙ] ⟶ Spec A`. -/
theorem chartIsoAffineSpace_hom_comp :
    (chartIsoAffineSpace A n).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)) =
      chartι A n ≫ projToSpecCoeff A n := by
  have hι : chartι A n = (AlgebraicGeometry.Proj.basicOpenIsoSpec (polyGrading A n)
      (MvPolynomial.X 0) (X_mem_one A n 0) Nat.one_pos).hom ≫
        AlgebraicGeometry.Proj.awayι (polyGrading A n) (MvPolynomial.X 0) (X_mem_one A n 0)
          Nat.one_pos := by
    rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have hring : CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) ≫
      (chartRingIso A n).hom = CommRingCat.ofHom (coeffToAway A n 0) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    change chartEquiv A n 0 (MvPolynomial.rename _ (MvPolynomial.C r)) = coeffToAway A n 0 r
    rw [MvPolynomial.rename_C, chartEquiv_apply, chartHom_C]
  rw [hι, Category.assoc, Stacks.AlgebraicGeometry.ProjBaseChange.awayι_comp_projToSpecCoeff,
    ← hring, Spec.map_comp]
  rfl

/-- **`𝒪(m)|_{D₊(T₀)} ≅ 𝒪_{D₊(T₀)}`**, trivialized by `T₀^m` ([Stacks, Tag 01MS]). -/
def twistRestrictChartIsoUnit (m : ℤ) :
    (Scheme.Modules.restrictFunctor (chartι A n)).obj (twist A n m) ≅
      SheafOfModules.unit (chartOpen A n).toScheme.ringCatSheaf :=
  Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit (chartOpen A n)
    (twist A n m)
    (Stacks.AlgebraicGeometry.ProjTwistCommonMultiple.twistingSheafOverBasicOpenIsoUnitOfMul
      (polyGrading A n) (X_mem_one A n 0) m (by simp))

/-- **`Lj^* a(𝒪_{Spec A}) ≅ 𝒪_{D₊(T₀)}[n]`** for the inclusion `j : D₊(T₀) ⟶ P^n_A` and `a` the
twisted inverse image along `π : P^n_A ⟶ Spec A`, with any proof `hpush` that `Rπ_*` preserves
quasi-coherent cohomology. -/
def chartPullbackTwistedInverseImageIso
    (hpush : ∀ (K : quasiCoherentDerivedCategory 𝐏) (i : ℤ),
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
        ((derivedPushforward (projToSpecCoeff A n)).obj K.obj)).IsQuasicoherent) :
    (quasiCoherentDerivedPullback' (chartι A n)).obj
        ((twistedInverseImage (projToSpecCoeff A n) hpush).obj
          (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of A)))) ≅
      (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (chartOpen A n).toScheme)⟦(n : ℤ)⟧ :=
  (quasiCoherentDerivedPullback' (chartι A n)).mapIso
      (topTwistIsoTwistedInverseImage A n hpush).symm ≪≫
    ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback (chartι A n)).app _).symm ≪≫
    ObjectProperty.isoMk _
      (((Scheme.Modules.restrictFunctor (chartι A n)).mapDerivedCategorySingleFunctor
          (-(n : ℤ))).app (twist A n (-(n : ℤ) - 1)) ≪≫
        (DerivedCategory.singleFunctor _ (-(n : ℤ))).mapIso
          (twistRestrictChartIsoUnit A n (-(n : ℤ) - 1)) ≪≫
        (((DerivedCategory.singleFunctors _).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).app
          _).symm ≪≫
        (((ObjectProperty.ι _).commShiftIso (n : ℤ)).app
          (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (chartOpen A n).toScheme)).symm)

end Stacks.Duality.ProjectiveSpace
