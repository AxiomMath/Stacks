module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.ComparisonIso
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.InvertibleTwistDerived
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertible modules, isomorphisms and projective space in Example 0AAC

Four inputs to [Stacks, Example 0AAC], all at the locally small model of the derived categories.

* For `h : Z ⟶ W` and an invertible `𝒪_W`-module `L`, the complex `L[0]` is K-flat, so
  `Lh^*(L[0])` is computed termwise and is `(h^*L)[0]`; in particular it lies in `D^{≥ 0}`.
* For an isomorphism `ψ : Z ⟶ W` of qcqs schemes, `Rψ_*` is an equivalence of the
  quasi-coherent derived categories with quasi-inverse `R(ψ⁻¹)_*`. Hence `R(ψ⁻¹)_*` is both the
  right adjoint `ψ^×` and the left adjoint `Lψ^*` of `Rψ_*`, so `ψ^× ≅ Lψ^*`.
* On `ℙⁿ_R = Proj R[T₀, …, Tₙ]`, the geometric factor `𝒪(d) ⊗ p^*R~` is isomorphic to `𝒪(d)`,
  hence invertible.
* If `R` is Noetherian, `ℙⁿ_R` is covered by the standard opens `D₊(Tᵢ)`, whose rings of
  sections are polynomial rings over `R`; so `ℙⁿ_R` is locally Noetherian.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality

/-- Derived pullback of an invertible module placed in degree zero lies in `D^{≥ 0}`. -/
theorem isGE_derivedPullback_singleFunctor_of_isInvertibleModule {Z W : Scheme.{u}}
    (h : Z ⟶ W) (L : W.Modules) [Stacks.Ample.IsInvertibleModule W L] :
    ((derivedPullback h).obj ((DerivedCategory.singleFunctor W.Modules 0).obj L)).IsGE 0 := by
  let M : Z.Modules :=
    (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).obj L
  let e : (derivedPullback h).obj ((DerivedCategory.singleFunctor W.Modules 0).obj L) ≅
      (DerivedCategory.singleFunctor Z.Modules 0).obj M :=
    (derivedPullback h).mapIso ((DerivedCategory.singleFunctorIsoCompQ W.Modules 0).app L) ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat h.toLRSHom.toShHom _
      (Stacks.AmpleNonvanishing.kFlat_single_of_isInvertibleModule W L) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom)
      (ComplexShape.up ℤ) 0).app L) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ Z.Modules 0).app _).symm
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm 0

/-- The twisted inverse image along an isomorphism is derived pullback along it. -/
def twistedInverseImageIsoQuasiCoherentDerivedPullbackOfIsIso {Z W : Scheme.{u}} (ψ : Z ⟶ W)
    [IsIso ψ] [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace W]
    [QuasiSeparatedSpace W] :
    twistedInverseImage ψ (isQuasicoherent_homology_derivedPushforward_of_qcqs ψ) ≅
      quasiCoherentDerivedPullback' ψ :=
  twistedInverseImageIsoOfIsIso ψ _ (isQuasicoherent_homology_derivedPushforward_of_qcqs (inv ψ))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 Z))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 W)) ≪≫
    Adjunction.leftAdjointUniq
      (quasiCoherentDerivedPushforwardEquivalenceOfIsIso ψ
        (isQuasicoherent_homology_derivedPushforward_of_qcqs ψ)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (inv ψ))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 Z))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 W))).symm.toAdjunction
      (quasiCoherentDerivedAdjunction ψ (isQuasicoherent_homology_derivedPullback' ψ)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs ψ))

/-- The geometric factor `𝒪(d) ⊗ p^*R~` of `ℙⁿ_R` at `R` is invertible. -/
theorem isInvertibleModule_geometricFactor (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj (polyGrading R n))
      ((ProjCoeff.T R n d).obj (ModuleCat.of R R)) :=
  Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaObjSelfIso R
      (ProjCoeff.W R n) (ProjCoeff.O R n d)).symm

/-- `ℙⁿ_R` is locally Noetherian over a Noetherian ring. -/
@[ega "II 2.7.1" "locally Noetherian"]
theorem isLocallyNoetherian_proj_polyGrading (R : Type u) [CommRing R] [IsNoetherianRing R]
    (n : ℕ) : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading R n)) := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun i : Fin (n + 1) =>
      ⟨AlgebraicGeometry.Proj.basicOpen (polyGrading R n) (MvPolynomial.X i),
        AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (X_mem_one R n i) Nat.one_pos⟩)
    ?_ Stacks.ProjectiveChart.isNoetherianRing_sections
  exact Stacks.AlgebraicGeometry.ProjPolyChart.iSup_basicOpen_X_eq_top R n

end Stacks.Duality
