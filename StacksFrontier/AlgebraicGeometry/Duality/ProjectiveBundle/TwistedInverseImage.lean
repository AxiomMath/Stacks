module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveBundle.DualizingTrace
public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImageStructureSheafQcqs
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedTwistAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.LocalModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.GradedIsoCohomology
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BundleTwistVanishing

/-!
# The twisted inverse image of the structure sheaf on a projective bundle

Let `Y` be a quasi-compact and quasi-separated scheme, `ℰ` a finite locally free `𝒪_Y`-module of
rank `n + 1` with determinant `𝓛 = ⋀ⁿ⁺¹ ℰ`, `π : X = 𝐏(ℰ) ⟶ Y` the projection and `a` the right
adjoint of `R π_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. Then
`π^*𝓛(-n-1)[n] ≅ a(𝒪_Y)` ([Stacks, Tag 0A9W]).

The trace `R π_*(π^*𝓛(-n-1)[n]) ≅ 𝒪_Y` determines `c : π^*𝓛(-n-1)[n] ⟶ a(𝒪_Y)`. Over an affine
open `V` on which `ℰ` and `𝓛` are trivial, the part of `X` over `V` is the projective space
`Proj Γ(Y, V)[T₀, …, Tₙ]` over `Spec Γ(Y, V) ≅ V`, and `π^*𝓛(-n-1)` restricts to `𝒪(-n-1)`; the
restriction of `c` is then invertible by the case of projective space over an affine base, read
through these isomorphisms.

## References

* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjectiveBundleCohomology (bundle bundlePushforward negTwist)

universe u

namespace Stacks.Duality.ProjectiveBundleDualizing

/-! ### The comparison map -/

section Comparison

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (E : S.Modules)
  [E.IsQuasicoherent] (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))

include hfree in
omit [CompactSpace S] [QuasiSeparatedSpace S] [E.IsQuasicoherent] in
/-- The projection of the projective bundle of a finite locally free module is proper. -/
theorem isProper_proj : IsProper (proj E hqc) :=
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (n + 1)).mp hfree
  Stacks.ProjectiveBundle.isProper_toBase E hqc n

include hfree in
omit [CompactSpace S] [QuasiSeparatedSpace S] [E.IsQuasicoherent] in
/-- The projection of the projective bundle of a finite locally free module is quasi-compact. -/
theorem quasiCompact_proj : AlgebraicGeometry.QuasiCompact (proj E hqc) :=
  have := isProper_proj E hqc hfree
  inferInstance

/-- **`π^*𝓛(-n-1)[n]`**, as an object of `D_QCoh(𝒪_X)`. -/
def dualizingObject : quasiCoherentDerivedCategory (bundle E hqc) :=
  have := isQuasicoherent_dualizingModule E hqc D n hfree
  ⟨(shiftFunctor _ (n : ℤ)).obj
    ((DerivedCategory.singleFunctor (bundle E hqc).Modules 0).obj (dualizingModule E hqc D n)),
    Stacks.Duality.ProjectiveSpace.derivedCategoryB_shift_single _ _⟩

/-- **The trace `R π_*(π^*𝓛(-n-1)[n]) ≅ 𝒪_S`**, in `D_QCoh(𝒪_S)`. -/
def dualizingObjectTraceIso :
    haveI := quasiCompact_proj E hqc hfree
    (quasiCoherentDerivedPushforward (proj E hqc)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (proj E hqc))).obj
        (dualizingObject E hqc D hfree) ≅ DerivedPushforward.derivedStructureSheaf S :=
  have := quasiCompact_proj E hqc hfree
  ObjectProperty.isoMk _
    (((derivedPushforward (proj E hqc)).commShiftIso (n : ℤ)).app _ ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso
        (nonempty_derivedPushforward_dualizingModule_iso E hqc D hfree).some ≪≫
      ((DerivedCategory.singleFunctors S.Modules).shiftIso (n : ℤ) 0 (n : ℤ) (by simp)).app _)

/-- **The comparison map `c : π^*𝓛(-n-1)[n] ⟶ a(𝒪_S)`** of the proof of [Stacks, Tag 0A9W]: the
transpose of the trace under `R π_* ⊣ a`. -/
def dualizingComparison :
    haveI := quasiCompact_proj E hqc hfree
    haveI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
    dualizingObject E hqc D hfree ⟶ (twistedInverseImage (proj E hqc)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (proj E hqc))).obj
        (DerivedPushforward.derivedStructureSheaf S) :=
  have := quasiCompact_proj E hqc hfree
  have := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
  (twistedInverseImageAdjunction (proj E hqc)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (proj E hqc))).homEquiv _ _
      (dualizingObjectTraceIso E hqc D hfree).hom

end Comparison

/-! ### The chart over a trivializing affine open is the polynomial model -/

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) {V : S.Opens} (hV : IsAffineOpen V) {n : ℕ}
  (b : Module.Basis (Fin (n + 1)) Γ(S, V) Γ(E, V))

/-- The constant `r` of the polynomial ring is carried to the structure map of the section ring. -/
theorem ofPolyGrading_C (r : Γ(S, V)) :
    Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading E hqc hV b
        (MvPolynomial.C r) =
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).strHom V r := by
  let := Stacks.SymGraded.AffinePieces.sectionAlgebra E hqc (V := V)
  have h1 := (Stacks.SymGraded.AffinePieces.symSectionAlgEquiv E hV hqc).symm.commutes r
  rw [Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra] at h1
  rw [← h1]
  change (Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc).symm
      ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.C r)) = _
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
  rfl

/-- The isomorphism `Proj Γ(V, Sym ℰ) ≅ Proj Γ(S, V)[T₀, …, Tₙ]` induced by a basis of
`Γ(ℰ, V)`. -/
abbrev chartPolyMap :
    AlgebraicGeometry.Proj ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) ⟶
      AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n) :=
  AlgebraicGeometry.Proj.map
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading E hqc hV b)
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.irrelevant_le_map_of_inverse _
      (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.toPolyGrading E hqc hV b)
      (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading_toPolyGrading E hqc hV b))

/-- The morphism `chartPolyMap` is an isomorphism. -/
instance isIso_chartPolyMap : IsIso (chartPolyMap E hqc hV b) :=
  Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_projMap_of_inverse _ _
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading_toPolyGrading E hqc hV b)
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.toPolyGrading_ofPolyGrading E hqc hV b)

/-- **The chart over `V` lies over `Spec Γ(S, V) ≅ V`**: through `chartPolyMap`, the structure
morphism of the polynomial model is the chart's projection to `V`. -/
theorem chartPolyMap_comp_projToSpecCoeff :
    chartPolyMap E hqc hV b ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n =
      projInclusionToOpen (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc) V hV ≫
        hV.isoSpec.hom := by
  have hRHS : projInclusionToOpen (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc) V hV ≫
      hV.isoSpec.hom =
      Proj.toSpecZero ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) ≫
        Spec.map ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).toGradedAlgebra.strZero
          ⟨V, hV⟩) :=
    (Iso.eq_comp_inv hV.isoSpec).mp (Category.assoc _ _ _).symm
  rw [hRHS]
  simp only [Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff, Proj.map_toSpecZero_assoc,
    ← Spec.map_comp]
  refine congrArg (fun φ => Proj.toSpecZero _ ≫ Spec.map φ) ?_
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  have hz : ((GradedRing.projZeroRingHom' (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n)
        (MvPolynomial.C r) : Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n 0) :
      MvPolynomial (Fin (n + 1)) Γ(S, V)) = MvPolynomial.C r := by
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply]
    exact DirectSum.decompose_of_mem_same _
      (MvPolynomial.C_mem_homogeneousSubmodule_zero (Fin (n + 1)) Γ(S, V) r)
  change Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading E hqc hV b
      ((GradedRing.projZeroRingHom' (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n)
        (algebraMap Γ(S, V) (MvPolynomial (Fin (n + 1)) Γ(S, V)) r) :
          Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n 0) :
        MvPolynomial (Fin (n + 1)) Γ(S, V)) = _
  rw [MvPolynomial.algebraMap_eq, hz, ofPolyGrading_C]
  exact (Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.coe_strZero_apply
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).toGradedAlgebra ⟨V, hV⟩ r).symm

end Chart

/-! ### `π^*𝓛(-n-1)` on the chart over a trivializing affine open -/

section LocalTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {V : S.Opens}
  (hV : IsAffineOpen V) {n : ℕ} (b : Module.Basis (Fin (n + 1)) Γ(S, V) Γ(E, V))

omit [E.IsQuasicoherent] in
/-- The chart of `𝐏(ℰ)` over `V` is an open immersion, being a base change of `V ⟶ S`. -/
theorem isOpenImmersion_chart :
    IsOpenImmersion ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) :=
  MorphismProperty.of_isPullback
    ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart_isPullback V hV).flip
    inferInstance

/-- **The polynomial chart** `Proj Γ(S, V)[T₀, …, Tₙ] ≅ Proj Γ(V, Sym ℰ) ⟶ 𝐏(ℰ)` over `V`. -/
abbrev polyChart :
    AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n) ⟶ bundle E hqc :=
  inv (chartPolyMap E hqc hV b) ≫
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV

/-- The polynomial chart `polyChart` is an open immersion. -/
instance isOpenImmersion_polyChart : IsOpenImmersion (polyChart E hqc hV b) :=
  have := isOpenImmersion_chart E hqc hV
  inferInstance

/-- **The polynomial chart is the inverse image of `Spec Γ(S, V) ≅ V`.** -/
theorem isPullback_polyChart :
    IsPullback (polyChart E hqc hV b)
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n) (proj E hqc)
      (hV.isoSpec.inv ≫ V.ι) := by
  have hiso : IsPullback hV.isoSpec.hom V.ι (hV.isoSpec.inv ≫ V.ι) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Iso.hom_inv_id_assoc, Category.comp_id]⟩
  have h := ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart_isPullback
    V hV).paste_vert hiso.flip
  rw [Category.comp_id] at h
  have hw : inv (chartPolyMap E hqc hV b) ≫
      (projInclusionToOpen (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc) V hV ≫
        hV.isoSpec.hom) = Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n := by
    rw [← chartPolyMap_comp_projToSpecCoeff, IsIso.inv_hom_id_assoc]
  have h0 : IsPullback (inv (chartPolyMap E hqc hV b))
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n)
      (projInclusionToOpen (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc) V hV ≫
        hV.isoSpec.hom) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hw]⟩
  have h1 := h0.paste_horiz h
  rwa [Category.id_comp] at h1

variable (eL : (Scheme.Modules.restrictFunctor V.ι).obj (det E n) ≅
  SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- `π^*𝓛` is trivial on the polynomial chart over an open on which `𝓛` is trivial. -/
def restrictPullbackDetIso :
    (Scheme.Modules.restrictFunctor (polyChart E hqc hV b)).obj
        ((Scheme.Modules.pullback (proj E hqc)).obj (det E n)) ≅
      SheafOfModules.unit
        (AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n)).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫
    (Scheme.Modules.pullbackComp (polyChart E hqc hV b) (proj E hqc)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (isPullback_polyChart E hqc hV b).w).app _ ≪≫
    ((Scheme.Modules.pullbackComp (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n)
      (hV.isoSpec.inv ≫ V.ι)).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso
      (((Scheme.Modules.pullbackComp hV.isoSpec.inv V.ι).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso
          (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫ eL) ≪≫
        Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso _) ≪≫
    Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso _

/-- The twist `𝒪(d)` of `𝐏(ℰ)` restricts on the polynomial chart to the twist `𝒪(d)`. -/
def restrictPieceIso (d : ℤ) :
    (Scheme.Modules.restrictFunctor (polyChart E hqc hV b)).obj (D.algebra.piece d) ≅
      twistingSheaf (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n) d :=
  have := isOpenImmersion_chart E hqc hV
  have := Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_twistMap_of_inverse
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading E hqc hV b)
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.toPolyGrading E hqc hV b)
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading_toPolyGrading E hqc hV b)
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.toPolyGrading_ofPolyGrading E hqc hV b) d
  (Scheme.Modules.restrictFunctorComp (inv (chartPolyMap E hqc hV b))
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)).app
        (D.algebra.piece d) ≪≫
    (Scheme.Modules.restrictFunctor (inv (chartPolyMap E hqc hV b))).mapIso
      (D.chartData.chartIso V hV d) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (inv (chartPolyMap E hqc hV b))).app _ ≪≫
    (Scheme.Modules.pullback (inv (chartPolyMap E hqc hV b))).mapIso
      (asIso (Stacks.ProjTwistComparison.twistMap
      (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading E hqc hV b)
      (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.irrelevant_le_map_of_inverse _
        (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.toPolyGrading E hqc hV b)
        (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ofPolyGrading_toPolyGrading
          E hqc hV b)) d)).symm ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id (chartPolyMap E hqc hV b))).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

/-- **`π^*𝓛(-n-1)` restricts on the polynomial chart to `𝒪(-n-1)`**, over an affine open on
which `ℰ` and `𝓛` are trivial. -/
def restrictDualizingModuleIso :
    (Scheme.Modules.restrictFunctor (polyChart E hqc hV b)).obj (dualizingModule E hqc D n) ≅
      twistingSheaf (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n) (-(n : ℤ) - 1) :=
  (Scheme.Modules.restrictFunctorIsoPullback (polyChart E hqc hV b)).app _ ≪≫
    (Scheme.Modules.pullback (polyChart E hqc hV b)).mapIso
      (eqToIso (Stacks.ProjectionFormula.tensorRightInvertible_obj _ _ _)) ≪≫
    Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (polyChart E hqc hV b)
      (negTwist E hqc D (n + 1)) ((Scheme.Modules.pullback (proj E hqc)).obj (det E n)) ≪≫
    Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
      (((Scheme.Modules.restrictFunctorIsoPullback _).app _).symm ≪≫
        restrictPieceIso E hqc D hV b _)
      (((Scheme.Modules.restrictFunctorIsoPullback _).app _).symm ≪≫
        restrictPullbackDetIso E hqc hV b eL) ≪≫
    Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor _ _ ≪≫
    eqToIso (congrArg (twistingSheaf (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n))
      (by push_cast; ring))

end LocalTwist

/-! ### The comparison map on a polynomial chart -/

section LocalComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (E : S.Modules)
  [E.IsQuasicoherent] (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) {V : S.Opens}
  (hV : IsAffineOpen V) (b : Module.Basis (Fin (n + 1)) Γ(S, V) Γ(E, V))
  (eL : (Scheme.Modules.restrictFunctor V.ι).obj (det E n) ≅
    SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- `π^*𝓛(-n-1)[n]` restricts on the polynomial chart to `𝒪(-n-1)[n]`. -/
def restrictDualizingObjectIso :
    Stacks.Duality.ProjectiveSpace.topTwist Γ(S, V) n ≅
      (OpenImmersion.restrictedDerivedRestrict (polyChart E hqc hV b)).obj
        (dualizingObject E hqc D hfree) :=
  let e₀ : ((OpenImmersion.restrictedDerivedRestrict (polyChart E hqc hV b)).obj
      (dualizingObject E hqc D hfree)).obj ≅
        (Stacks.Duality.ProjectiveSpace.topTwist Γ(S, V) n).obj :=
    ((Scheme.Modules.restrictFunctor (polyChart E hqc hV b)).mapDerivedCategory.commShiftIso
        (n : ℤ)).app _ ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso
        (((Scheme.Modules.restrictFunctor (polyChart E hqc hV b)).mapDerivedCategorySingleFunctor
            0).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            (restrictDualizingModuleIso E hqc D hV b eL)) ≪≫
      ((DerivedCategory.singleFunctors _).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).app _
  (ObjectProperty.isoMk _ e₀).symm

include eL in
/-- **The comparison map restricted to a polynomial chart is invertible**: the map of
[Stacks, Tag 0A9L] for the cartesian square of the chart over `Spec Γ(S, V) ≅ V` is invertible at
`𝒪_S` ([Stacks, Tag 0A9P] (1)), and on `P^n_{Γ(S, V)}` a morphism out of `𝒪(-n-1)[n]` with
invertible transpose is invertible. -/
theorem isIso_restrict_dualizingComparison :
    haveI := quasiCompact_proj E hqc hfree
    haveI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
    IsIso ((OpenImmersion.restrictedDerivedRestrict (polyChart E hqc hV b)).map
      (dualizingComparison E hqc D hfree)) := by
  have := isProper_proj E hqc hfree
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (n + 1)).mp hfree
  have := Stacks.ProjectiveBundle.smooth_toBase E hqc n
  have : CompactSpace (bundle E hqc) := QuasiCompact.compactSpace_of_compactSpace (proj E hqc)
  have : QuasiSeparatedSpace (bundle E hqc) := quasiSeparatedSpace_of_quasiSeparated (proj E hqc)
  have := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
  have : CompactSpace (AlgebraicGeometry.Proj
      (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n)) :=
    QuasiCompact.compactSpace_of_compactSpace
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n)
  have : QuasiSeparatedSpace (AlgebraicGeometry.Proj
      (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n)) :=
    quasiSeparatedSpace_of_quasiSeparated
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n)
  refine Stacks.Duality.ProjectiveSpace.isIso_restrict_of_isIso_homEquiv_symm
    (polyChart E hqc hV b) (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff Γ(S, V) n)
    (proj E hqc) (hV.isoSpec.inv ≫ V.ι) (isPullback_polyChart E hqc hV b) _
    (KoszulRegular.isBoundedBelow_singleFunctor_obj _) _ ?_
    (restrictDualizingObjectIso E hqc D hfree hV b eL)
    (fun g hg => Stacks.Duality.ProjectiveSpace.isIso_of_isIso_pushTwistedAdj_homEquiv_symm n
      Γ(S, V) g hg)
  rw [show ((twistedInverseImageAdjunction (proj E hqc)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).homEquiv _ _).symm
        (dualizingComparison E hqc D hfree) = (dualizingObjectTraceIso E hqc D hfree).hom from
      Equiv.symm_apply_apply _ _]
  infer_instance

end LocalComparison

/-! ### Tag 0A9W -/

section Main

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (E : S.Modules)
  [E.IsQuasicoherent] (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))

include hfree in
omit [CompactSpace S] [QuasiSeparatedSpace S] [E.IsQuasicoherent] in
/-- Every point of the base lies in an affine open over which `ℰ` is free, with a basis of its
sections, and `𝓛` is trivial. -/
theorem exists_trivializing_affineOpen (y : S) :
    ∃ (V : S.affineOpens) (_ : y ∈ (V : S.Opens)),
      Nonempty (Module.Basis (Fin (n + 1)) Γ(S, (V : S.Opens)) Γ(E, (V : S.Opens))) ∧
      Nonempty ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).obj (det E n) ≅
        SheafOfModules.unit (V : S.Opens).toScheme.ringCatSheaf) := by
  have := isInvertible_det_of_rank E hfree
  obtain ⟨U, hU, hUL⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible (det E n)
  have hyU : y ∈ ⨆ y, U y := by
    rw [hU]
    trivial
  obtain ⟨y', hy'⟩ := TopologicalSpace.Opens.mem_iSup.mp hyU
  obtain ⟨V, ⟨hV, ⟨eE⟩⟩, hyV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.isBasis_trivializing E hfree) hy'
  obtain ⟨b⟩ := Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.nonempty_basis_sections E eE
  exact ⟨⟨V, hV⟩, hyV, ⟨b.reindex Equiv.ulift⟩,
    ⟨(Scheme.Modules.restrictFunctorCongr (S.homOfLE_ι hVU).symm).app _ ≪≫
      (Scheme.Modules.restrictFunctorComp (S.homOfLE hVU) (U y').ι).app _ ≪≫
      (Scheme.Modules.restrictFunctor (S.homOfLE hVU)).mapIso (hUL y').some ≪≫
      Scheme.Modules.restrictUnitIso _⟩⟩

/-- **The comparison map `c : π^*𝓛(-n-1)[n] ⟶ a(𝒪_S)` is an isomorphism.** Whether a morphism of
`D(𝒪_X)` is invertible is local on `X`, and the polynomial charts over the affine opens of `S` on
which `ℰ` and `𝓛` are trivial cover `X`. -/
theorem isIso_dualizingComparison :
    haveI := quasiCompact_proj E hqc hfree
    haveI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
    IsIso (dualizingComparison E hqc D hfree) := by
  have := quasiCompact_proj E hqc hfree
  have := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
  let P := DerivedCategoryB.derivedCategoryB (A := (bundle E hqc).Modules)
    (SheafOfModules.isQuasicoherent (bundle E hqc).ringCatSheaf)
  suffices h : IsIso (dualizingComparison E hqc D hfree).hom by
    have : IsIso ((ObjectProperty.ι P).map (dualizingComparison E hqc D hfree)) := h
    exact (ObjectProperty.fullyFaithfulι P).isIso_of_isIso_map _
  let I := Σ V : S.affineOpens,
    Module.Basis (Fin (n + 1)) Γ(S, (V : S.Opens)) Γ(E, (V : S.Opens)) ×
      ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).obj (det E n) ≅
        SheafOfModules.unit (V : S.Opens).toScheme.ringCatSheaf)
  refine QcqsGeneration.isIso_of_isIso_derivedRestrict _
    (fun i : I => polyChart E hqc i.1.2 i.2.1) (fun x => ?_) (fun i => ?_)
  · obtain ⟨V, hyV, ⟨b⟩, ⟨eL⟩⟩ := exists_trivializing_affineOpen E hfree (proj E hqc x)
    have hV : IsAffineOpen (V : S.Opens) := V.2
    have sq := isPullback_polyChart E hqc hV b
    have hx : x ∈ Set.range (pullback.fst (proj E hqc) (hV.isoSpec.inv ≫ (V : S.Opens).ι)) := by
      rw [Scheme.Pullback.range_fst]
      obtain ⟨v, hv⟩ : proj E hqc x ∈ Set.range (V : S.Opens).ι := by
        rwa [Scheme.Opens.range_ι]
      refine ⟨hV.isoSpec.hom v, ?_⟩
      have h : hV.isoSpec.hom ≫ hV.isoSpec.inv ≫ (V : S.Opens).ι = (V : S.Opens).ι :=
        Iso.hom_inv_id_assoc _ _
      rw [← hv]
      exact (Scheme.Hom.comp_apply _ _ v).symm.trans (congrArg (fun φ => φ v) h)
    obtain ⟨w, rfl⟩ := hx
    refine ⟨⟨V, b, eL⟩, sq.isoPullback.inv w, ?_⟩
    change (polyChart E hqc hV b) (sq.isoPullback.inv w) = _
    exact (Scheme.Hom.comp_apply _ _ w).symm.trans
      (congrArg (fun φ => φ w) sq.isoPullback_inv_fst)
  · have := isIso_restrict_dualizingComparison E hqc D hfree i.1.2 i.2.1 i.2.2
    exact Functor.map_isIso (ObjectProperty.ι _)
      ((OpenImmersion.restrictedDerivedRestrict _).map (dualizingComparison E hqc D hfree))

/-- **[Stacks, Tag 0A9W].** Let `S` be a quasi-compact and quasi-separated scheme, `ℰ` a finite
locally free `𝒪_S`-module of rank `n + 1` with determinant `𝓛 = ⋀ⁿ⁺¹ ℰ`, `π : 𝐏(ℰ) ⟶ S` the
projection and `a` the right adjoint of `R π_* : D_QCoh(𝒪_{𝐏(ℰ)}) ⥤ D_QCoh(𝒪_S)` of
[Stacks, Tag 0A9E]. Then `π^*𝓛(-n-1)[n] ≅ a(𝒪_S)`, for every `n ≥ 0`; the isomorphism is the
transpose `dualizingComparison` of the trace `R π_*(π^*𝓛(-n-1)[n]) ≅ 𝒪_S`.

For `ℰ = 𝒪_S^{⊕ n+1}` and projective space in the model `projectiveSpaceOver`, the statement
`a(𝒪_S) ≅ 𝒪(-n-1)[n]` is
`Stacks.Duality.ProjectiveSpace.nonempty_twistedInverseImage_derivedStructureSheaf_iso_of_qcqs`. -/
@[stacks 0A9W "the projective bundle P(E) is the relative Proj of Sym(E) with twists O(d) of a \
twist datum D, and f^*L(-n-1) is written O(-n-1) ⊗ π^*(∧^(n+1) E); the special case E = O^(n+1) \
on projectiveSpaceOver is nonempty_twistedInverseImage_derivedStructureSheaf_iso_of_qcqs"]
theorem nonempty_dualizingObject_iso_twistedInverseImage :
    haveI := quasiCompact_proj E hqc hfree
    haveI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
    Nonempty (dualizingObject E hqc D hfree ≅ (twistedInverseImage (proj E hqc)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (proj E hqc))).obj
        (DerivedPushforward.derivedStructureSheaf S)) := by
  have := quasiCompact_proj E hqc hfree
  have := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (proj E hqc)
  have := isIso_dualizingComparison E hqc D hfree
  exact ⟨asIso (dualizingComparison E hqc D hfree)⟩

end Main

end Stacks.Duality.ProjectiveBundleDualizing

end
