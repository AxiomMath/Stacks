module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.AffineChart
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition

/-!
# The twisted inverse image of `Pⁿ_R → Spec R` on the chart `𝔸ⁿ_R`, for every `K`

Let `π : Pⁿ_R ⟶ Spec R` be the structure morphism, `a` the twisted inverse image along `π`,
`j : D₊(T₀) ⟶ Pⁿ_R` the standard chart and `D₊(T₀) ≅ 𝔸ⁿ_R`. Wherever the map
`Lπ^*K ⊗ᴸ a(𝒪) ⟶ a(K)` of [Stacks, Tag 0A9S] is an isomorphism, `Lj^*a(K) ≅ Lp^*K[n]` on `𝔸ⁿ_R`,
where `p : 𝔸ⁿ_R ⟶ Spec R` is the projection: `Lj^*` is monoidal and `Lj^*a(𝒪) ≅ 𝒪[n]`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace Stacks.Duality.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On the chart, `𝔸ⁿ_R ⟶ D₊(T₀) ⟶ Pⁿ_R ⟶ Spec R` is the projection `𝔸ⁿ_R ⟶ Spec R`. -/
theorem chartIsoAffineSpace_inv_comp (R : CommRingCat.{u}) (n : ℕ) :
    (chartIsoAffineSpace R n).inv ≫ chartι R n ≫ projToSpecCoeff R n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) := by
  rw [← chartIsoAffineSpace_hom_comp, Iso.inv_hom_id_assoc]

/-- **`a_π(K)` on the chart `D₊(T₀) ≅ 𝔸ⁿ_R` is `Lp^*K[n]`**, for `π : Pⁿ_R ⟶ Spec R` and
`p : 𝔸ⁿ_R ⟶ Spec R`, wherever the comparison map `Lπ^*K ⊗ᴸ a_π(𝒪) ⟶ a_π(K)` of
[Stacks, Tag 0A9S] is invertible (built from the monoidal structure of `Lπ^*` and the right
unitor). -/
theorem nonempty_chart_twistedInverseImage_iso_of_isIso (R : CommRingCat.{u}) (n : ℕ)
    (K : quasiCoherentDerivedCategory (Spec R))
    (hK : IsIso (twistedInverseImageCompareWithPullback (projToSpecCoeff R n)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (quasiCoherentDerivedPullbackTensorIso (projToSpecCoeff R n)).hom
      (quasiCoherentDerivedTensorRightUnitor _) K)) :
    Nonempty ((OpenImmersion.restrictedDerivedRestrict (chartIsoAffineSpace R n).inv).obj
        ((quasiCoherentDerivedPullback' (chartι R n)).obj
          ((twistedInverseImage (projToSpecCoeff R n)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≅
      ((quasiCoherentDerivedPullback' (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)))).obj K)⟦(n : ℤ)⟧) := by
  let π := projToSpecCoeff R n
  let a := chartι R n
  let eA := chartIsoAffineSpace R n
  let hpush := isQuasicoherent_homology_derivedPushforward_of_qcqs π
  let A := twistedInverseImage π hpush
  let O := DerivedPushforward.derivedStructureSheaf (Spec R)
  let c := asIso (twistedInverseImageCompareWithPullback π hpush
    (quasiCoherentDerivedPullbackTensorIso π).hom (quasiCoherentDerivedTensorRightUnitor _) K)
  let i₁ : (quasiCoherentDerivedPullback' a).obj (A.obj K) ≅
      ((quasiCoherentDerivedTensor _).obj
        ((quasiCoherentDerivedPullback' (a ≫ π)).obj K)).obj
        ((DerivedPushforward.derivedStructureSheaf (chartOpen R n).toScheme)⟦(n : ℤ)⟧) :=
    (quasiCoherentDerivedPullback' a).mapIso c.symm ≪≫
      (quasiCoherentDerivedPullbackTensorIso a).app
        (A.obj O, (quasiCoherentDerivedPullback' π).obj K) ≪≫
      ((quasiCoherentDerivedTensor _).obj _).mapIso
        (chartPullbackTwistedInverseImageIso R n hpush) ≪≫
      ((quasiCoherentDerivedTensor _).mapIso
        ((quasiCoherentDerivedPullbackCompIso a π).app K)).app _
  exact ⟨(OpenImmersion.restrictedDerivedRestrict eA.inv).mapIso
      (i₁ ≪≫ quasiCoherentDerivedTensorStructureSheafShiftIso _ _ (n : ℤ)) ≪≫
    ((OpenImmersion.restrictedDerivedRestrict eA.inv).commShiftIso (n : ℤ)).app _ ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso
      ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback eA.inv).app _ ≪≫
        (quasiCoherentDerivedPullbackCompIso eA.inv (a ≫ π)).app K ≪≫
        eqToIso (congrArg (fun g => (quasiCoherentDerivedPullback' g).obj K)
          (chartIsoAffineSpace_inv_comp R n)))⟩

/-- **`a_π(K)` on the chart `D₊(T₀) ≅ 𝔸ⁿ_R` is `Lp^*K[n]`** for a Noetherian ring `R`: the map
of [Stacks, Tag 0A9S] for `π : Pⁿ_R ⟶ Spec R` is invertible over the affine base `Spec R`. -/
theorem nonempty_chart_twistedInverseImage_iso (R : CommRingCat.{u}) [IsNoetherianRing R]
    (n : ℕ)
    (K : quasiCoherentDerivedCategory (Spec R)) :
    Nonempty ((OpenImmersion.restrictedDerivedRestrict (chartIsoAffineSpace R n).inv).obj
        ((quasiCoherentDerivedPullback' (chartι R n)).obj
          ((twistedInverseImage (projToSpecCoeff R n)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≅
      ((quasiCoherentDerivedPullback' (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)))).obj K)⟦(n : ℤ)⟧) := by
  have : IsProper (projToSpecCoeff R n) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R n
  have : AlgebraicGeometry.Smooth (projToSpecCoeff R n) := smooth_projToSpecCoeff R n
  exact nonempty_chart_twistedInverseImage_iso_of_isIso R n K
    (isIso_twistedInverseImageCompareWithPullback_of_specTarget (projToSpecCoeff R n) _ _
      (quasiCoherentDerivedTensorRightUnitor _) (fun _ _ => rfl) K)

end Stacks.Duality.ProjectiveSpace

end
