module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamCohomology

/-!
# De Rham cohomology of a morphism whose relative differentials vanish

Let `p : X ⟶ S` be a morphism of schemes with `Ωᵏ_{X/S} = 0` for every `k ≥ 1`, for instance
`ℙ⁰_A ⟶ Spec A`. Then the relative de Rham complex `Ω^•_{X/S}` is `Ω⁰_{X/S} = 𝒪_X`, read over
`p⁻¹𝒪_S`, placed in degree zero, and de Rham cohomology is the cohomology of `Ω⁰_{X/S}`:
the projection `σ^{≥0}Ω^• ⟶ Ω⁰[0]` of the brutal filtration is bijective on hypercohomology,
because `σ^{≥1}Ω^•` has zero terms. This is the degenerate case of the Hodge-to-de Rham spectral
sequence of [Stacks, Section 0FM6].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyEquivFormsZero`: the identification
  `H^q_{dR}(X/S) ≅ H^q(X, Ω⁰_{X/S})`, the right side computed for `Ω⁰_{X/S}` as an
  `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyEquivFormsZero_smul`: it is semilinear along
  `Γ(p⁻¹𝒪_S) ⟶ Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyEquivFormsZero_deRhamUnit`: it carries the unit
  `1 ∈ H⁰_{dR}(X/S)` to the class of the section `1` of `Ω⁰_{X/S}`.
* `AlgebraicGeometry.Scheme.Hom.isZero_deRhamCohomologyBaseModule_of_isZero`: de Rham cohomology
  vanishes in the degrees where the cohomology of `Ω⁰_{X/S}` does.
* `AlgebraicGeometry.Scheme.Hom.isZero_deRhamCohomologyBaseModule_of_neg`: de Rham cohomology
  vanishes in negative degrees (for every morphism).

## References

* [Stacks Project, Section 0FM6](https://stacks.math.columbia.edu/tag/0FM6)
* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cech.Hypercohomology
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)
open Stacks.Cohomology.InvertibleDerived (smulHom)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] AlgebraicGeometry.SheafOfModules.sectionCommRingTopCat

variable {X S : Scheme.{u}} (p : X ⟶ S)
  (hΩ : ∀ k : ℕ, 0 < k → IsZero (relativeDifferentialForms p (k : ℤ)))

include hΩ in
/-- The terms of the relative de Rham complex vanish in positive degrees. -/
theorem isZero_deRhamComplexInt_X_of_pos (q : ℤ) (hq : 0 < q) :
    IsZero ((SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).X q) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
  rw [SheafOfModules.deRhamComplexInt_X_of_nonneg _ _ _ (Int.natCast_nonneg k)]
  exact Functor.map_isZero _ (hΩ k (by omega))

include hΩ in
/-- **The projection `σ^{≥0}Ω^•_{X/S} ⟶ Ω⁰_{X/S}[0]` is bijective on hypercohomology** when
`Ωᵏ_{X/S} = 0` for `k ≥ 1`. -/
theorem bijective_hypercohomologyMap_truncPlusπ_deRham (k : ℤ) :
    Function.Bijective (hypercohomologyMap ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj
      S.sheaf) (truncPlusπ (SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) 0) k).hom := by
  have hz : ∀ j, IsZero (hypercohomology ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj
      S.sheaf) (truncPlus _ (SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) (0 + 1)) j) := fun j =>
    isZero_hypercohomology_of_isZero_X _ _
      (isZero_truncPlus_X _ _ (fun q hq => isZero_deRhamComplexInt_X_of_pos p hΩ q (by omega))) j
  exact bijective_hypercohomologyMap_truncSC_g _ _ 0 k (hz k) (hz (k + 1))

/-- The term of degree zero of the relative de Rham complex is `Ω⁰_{X/S}` read over `p⁻¹𝒪_S`. -/
theorem deRhamComplexInt_X_zero :
    (SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).X 0 =
      (_root_.SheafOfModules.restrictScalars
        (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj
        (relativeDifferentialForms p 0) :=
  SheafOfModules.deRhamComplexInt_X_of_nonneg _ _ 0 le_rfl

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- Čech cohomology computes the cohomology of `Ω⁰_{X/S}` read over `p⁻¹𝒪_S`. -/
theorem cechComputes_restrictScalars_formsZero :
    CechComputes ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
      (singlePlus ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
        ((_root_.SheafOfModules.restrictScalars
          (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj
          (relativeDifferentialForms p 0)) 0) :=
  have := isQuasicoherent_relativeDifferentialForms p 0
  cechComputesSheaf_restrictScalars_of_isQuasicoherent X _ _

/-- Čech cohomology computes the cohomology of `Ω⁰_{X/S}`. -/
theorem cechComputesSheaf_formsZero :
    CechComputesSheaf X.sheaf (relativeDifferentialForms p 0) :=
  have := isQuasicoherent_relativeDifferentialForms p 0
  cechComputesSheaf_of_isQuasicoherent X _

/-- **The identification `H^q_{dR}(X/S) ≅ H^q(X, Ω⁰_{X/S})`** when `Ωᵏ_{X/S} = 0` for `k ≥ 1`,
induced by the projection `Ω^•_{X/S} ⟶ Ω⁰_{X/S}[0]`. -/
def deRhamCohomologyEquivFormsZero (q : ℕ) :
    deRhamCohomologyBaseModule p (q : ℤ) ≃+
      hypercohomology X.sheaf (singlePlus X.sheaf (relativeDifferentialForms p 0) 0) q :=
  (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) (q : ℤ)).symm.toLinearEquiv.toAddEquiv
    |>.trans (hypercohomologyMapIso _ (truncPlusIso _ (SheafOfModules.deRhamComplexPlus
      (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) 0)
        (q : ℤ)).symm.toLinearEquiv.toAddEquiv
    |>.trans (LinearEquiv.ofBijective _
      (bijective_hypercohomologyMap_truncPlusπ_deRham p hΩ (q : ℤ))).toAddEquiv
    |>.trans (hypercohomologyMapIso _ (eqToIso (congrArg
      (fun F => singlePlus ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf) F 0)
      (deRhamComplexInt_X_zero p))) (q : ℤ)).toLinearEquiv.toAddEquiv
    |>.trans (eqToIso (congrArg (hypercohomology
      ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
      (singlePlus ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
        ((_root_.SheafOfModules.restrictScalars
          (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj
          (relativeDifferentialForms p 0)) 0)) (add_zero (q : ℤ)).symm)).toLinearEquiv.toAddEquiv
    |>.trans (restrictScalarsCechEquiv
      (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
      (relativeDifferentialForms p 0) 0
      (cechComputes_restrictScalars_formsZero p) (cechComputesSheaf_formsZero p) q)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- Restricting the scalars of multiplication by the image in `Γ(X, 𝒪_X)` of a global section `t`
of `p⁻¹𝒪_S` gives multiplication by `t`. -/
theorem restrictScalars_map_smulHom_inverseImage
    (t : ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf).obj.obj (op ⊤))
    (F : X.Modules) :
    (_root_.SheafOfModules.restrictScalars
        (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).map
        (smulHom (X := X.toRingedSpace)
          (((SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p)).hom.app
            (op ⊤)).hom t) F) =
      smulHom (X := SheafOfModules.baseRingedSpace (X := X.toRingedSpace)
          ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)) t
        ((_root_.SheafOfModules.restrictScalars
          (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj F) := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
  have h := ConcreteCategory.congr_hom
    ((SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p)).hom.naturality
      (homOfLE (le_top : V.unop ≤ ⊤)).op) t
  exact (congrArg (fun r : (ringSheaf X.sheaf).obj.obj V =>
    (r • (show F.val.obj V from y) : F.val.obj V)) h).symm

/-- **The identification of Čech cocycles across restriction of scalars is semilinear** along the
structure map `Γ(p⁻¹𝒪_S) ⟶ Γ(X, 𝒪_X)`, for `Ω⁰_{X/S}` placed in degree zero. -/
theorem restrictScalarsCechEquiv_formsZero_smul (q : ℕ)
    (t : SectionRing (ringSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)) ⊤)
    (x : hypercohomology ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
      (singlePlus ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
        ((_root_.SheafOfModules.restrictScalars
          (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj
          (relativeDifferentialForms p 0)) 0) ((q : ℤ) + 0)) :
    restrictScalarsCechEquiv (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
        (relativeDifferentialForms p 0) 0
        (cechComputes_restrictScalars_formsZero p)
        (cechComputesSheaf_formsZero p) q (t • x) =
      (((SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p)).hom.app
          (op ⊤)).hom t) •
        restrictScalarsCechEquiv
          (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
          (relativeDifferentialForms p 0) 0
          (cechComputes_restrictScalars_formsZero p)
          (cechComputesSheaf_formsZero p) q x := by
  have hF' := cechComputes_restrictScalars_formsZero p
  have hF := cechComputesSheaf_formsZero p
  have h1 := restrictScalarsCechEquiv_hypercohomologyMap
    (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
    (relativeDifferentialForms p 0) 0
    (smulHom (X := X.toRingedSpace)
      (((SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p)).hom.app
        (op ⊤)).hom t) (relativeDifferentialForms p 0))
    hF' hF hF' hF q x
  have h2 := hypercohomologyMap_smulHom
    (X := SheafOfModules.baseRingedSpace (X := X.toRingedSpace)
      ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf))
    t ((_root_.SheafOfModules.restrictScalars
      (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj
      (relativeDifferentialForms p 0)) 0 hF' _ x
  have h3 := hypercohomologyMap_smulHom (X := X.toRingedSpace)
    (((SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p)).hom.app
      (op ⊤)).hom t) (relativeDifferentialForms p 0) 0 hF q
    (restrictScalarsCechEquiv (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
      (relativeDifferentialForms p 0) 0 hF' hF q x)
  rw [restrictScalars_map_smulHom_inverseImage] at h1
  exact (congrArg _ h2.symm).trans (h1.trans h3)

include hΩ in
/-- **The identification `H^q_{dR}(X/S) ≅ H^q(X, Ω⁰_{X/S})` is semilinear** along the structure
map `Γ(p⁻¹𝒪_S) ⟶ Γ(X, 𝒪_X)`. -/
theorem deRhamCohomologyEquivFormsZero_smul (q : ℕ)
    (t : SectionRing (ringSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)) ⊤)
    (x : ↥(SheafOfModules.deRhamCohomology (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) (q : ℤ))) :
    deRhamCohomologyEquivFormsZero p hΩ q (t • x) =
      (((SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p)).hom.app
          (op ⊤)).hom t) • deRhamCohomologyEquivFormsZero p hΩ q x := by
  let L₁ := (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) (q : ℤ)).symm.toLinearEquiv
  let L₂ := (hypercohomologyMapIso _ (truncPlusIso _ (SheafOfModules.deRhamComplexPlus
    (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) 0)
      (q : ℤ)).symm.toLinearEquiv
  let L₃ := LinearEquiv.ofBijective _ (bijective_hypercohomologyMap_truncPlusπ_deRham p hΩ (q : ℤ))
  let L₄ := (hypercohomologyMapIso _ (eqToIso (congrArg
    (fun F => singlePlus ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf) F 0)
    (deRhamComplexInt_X_zero p))) (q : ℤ)).toLinearEquiv
  let L₅ := (eqToIso (congrArg (hypercohomology
    ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
    (singlePlus ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
      ((_root_.SheafOfModules.restrictScalars
        (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj
        (relativeDifferentialForms p 0)) 0)) (add_zero (q : ℤ)).symm)).toLinearEquiv
  have h : L₅ (L₄ (L₃ (L₂ (L₁ (t • x))))) = t • L₅ (L₄ (L₃ (L₂ (L₁ x)))) := by
    rw [L₁.map_smul, L₂.map_smul]
    exact (congrArg L₅ ((congrArg L₄ (L₃.map_smul t _)).trans (L₄.map_smul t _))).trans
      (L₅.map_smul t _)
  exact (congrArg _ h).trans (restrictScalarsCechEquiv_formsZero_smul p q t _)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **The unit of the de Rham complex projects to the class of the unit section** of its term in
degree zero. -/
theorem hypercohomologyMap_truncPlusπ_truncatedUnitClass_zero :
    hypercohomologyMap ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
        (truncPlusπ (SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) 0) 0
        (SheafOfModules.truncatedUnitClass (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) =
      sectionClass ((SheafOfModules.deRhamComplexInt (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).X 0)
        ((SheafOfModules.deRhamDifferentialGradedAlgebra (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).one.eval (op ⊤)) := by
  have e := congrArg (fun f => hypercohomologyMap
      ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf) f 0
      (sectionClass (unitSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf))
        (oneSection ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf))))
    (globalCocycleHom_comp_truncPlusπ
      (O := (TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
      (SheafOfModules.deRhamComplexPlus (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
      _ (unitHom_comp_d_eq_zero (SheafOfModules.deRhamDifferentialGradedAlgebra
        (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))))
  simp only [hypercohomologyMap_comp, ConcreteCategory.comp_apply] at e
  exact e.trans ((hypercohomologyMap_sectionClass _ _).trans (congrArg _ (one_smul _ _)))

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **The unit of the de Rham complex is the unit form**: under the identification of the term of
degree zero of the de Rham complex with `Ω⁰_{X/S}` read over `p⁻¹𝒪_S`, the unit section is the
section `1` of `Ω⁰_{X/S} = 𝒪_X`. -/
theorem eqToHom_deRhamUnit_eq_formsZeroOne :
    (eqToHom (deRhamComplexInt_X_zero p)).val.app (op ⊤)
        ((SheafOfModules.deRhamDifferentialGradedAlgebra (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).one.eval (op ⊤)) =
      (relativeDifferentialFormsZeroIso p).inv.val.app (op ⊤) (1 : Γ(X, ⊤)) := by
  have key : ∀ {M N : _root_.SheafOfModules.{u}
      (ringSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf))} (h : M = N)
      (z : M.val.obj (op ⊤)), HEq ((eqToHom h).val.app (op ⊤) z) z := by
    rintro M N rfl z
    rfl
  have hu : (relativeDifferentialFormsZeroIso p).inv.val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (deRhamAlgebras p).exterior.one.eval (op ⊤) := by
    have h1 := (deRhamAlgebras p).exteriorPieceZeroIsoUnit_one (op ⊤)
    have h2 : ((deRhamAlgebras p).exteriorPieceZeroIsoUnit.inv.val.app (op ⊤)).hom
        (((deRhamAlgebras p).exteriorPieceZeroIsoUnit.hom.val.app (op ⊤)).hom
          ((deRhamAlgebras p).exterior.one.eval (op ⊤))) =
        (deRhamAlgebras p).exterior.one.eval (op ⊤) := by
      show (((deRhamAlgebras p).exteriorPieceZeroIsoUnit.hom ≫
        (deRhamAlgebras p).exteriorPieceZeroIsoUnit.inv).val.app (op ⊤)).hom _ = _
      rw [Iso.hom_inv_id]
      rfl
    rwa [h1] at h2
  rw [hu]
  exact eq_of_heq ((key _ _).trans (SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ _))

include hΩ in
/-- **The identification `H⁰_{dR}(X/S) ≅ H⁰(X, Ω⁰_{X/S})` carries the unit `1 ∈ H⁰_{dR}(X/S)` to
the class of the section `1` of `Ω⁰_{X/S} = 𝒪_X`.** -/
theorem deRhamCohomologyEquivFormsZero_deRhamUnit :
    deRhamCohomologyEquivFormsZero p hΩ 0 (deRhamUnit p) =
      sectionClass (relativeDifferentialForms p 0)
        ((relativeDifferentialFormsZeroIso p).inv.val.app (op ⊤) (1 : Γ(X, ⊤))) := by
  have h1 := Iso.hom_inv_id_apply (SheafOfModules.hypercohomologyIsoDeRhamCohomology
    (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 0)
    (differentialGradedUnitClass (SheafOfModules.deRhamDifferentialGradedAlgebra
      (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) 0)
  have h4 := hypercohomologyMap_sectionClass
    (O := (TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
    (eqToHom (deRhamComplexInt_X_zero p))
    ((SheafOfModules.deRhamDifferentialGradedAlgebra (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).one.eval (op ⊤))
  rw [eqToHom_deRhamUnit_eq_formsZeroOne] at h4
  have heq : ∀ {a b : ℤ} (h : a = b) z,
      HEq ((eqToHom (congrArg (hypercohomology
        ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
        (singlePlus ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)
          ((_root_.SheafOfModules.restrictScalars
            (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))).obj
            (relativeDifferentialForms p 0)) 0)) h)).hom z) z := by
    rintro a b rfl z
    rfl
  refine Eq.trans ?_ (restrictScalarsCechEquiv_sectionClass
    (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
    (relativeDifferentialForms p 0) (cechComputes_restrictScalars_formsZero p)
    (cechComputesSheaf_formsZero p)
    ((relativeDifferentialFormsZeroIso p).inv.val.app (op ⊤) (1 : Γ(X, ⊤))))
  refine congrArg (restrictScalarsCechEquiv
    (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap p))
    (relativeDifferentialForms p 0) 0 (cechComputes_restrictScalars_formsZero p)
    (cechComputesSheaf_formsZero p) 0) ?_
  refine eq_of_heq ((heq (add_zero ((0 : ℕ) : ℤ)).symm _).trans (heq_of_eq ?_))
  show hypercohomologyMap _ (eqToIso _).hom 0 (hypercohomologyMap _ (truncPlusπ _ 0) 0
    (hypercohomologyMap _ (truncPlusIso _ _ 0).inv 0
      ((SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 0).inv
        ((SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 0).hom
          (differentialGradedUnitClass (SheafOfModules.deRhamDifferentialGradedAlgebra
            (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) 0))))) = _
  rw [h1]
  show hypercohomologyMap _ (eqToIso _).hom 0 (hypercohomologyMap _ (truncPlusπ _ 0) 0
    (SheafOfModules.truncatedUnitClass (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))) = _
  rwa [hypercohomologyMap_truncPlusπ_truncatedUnitClass_zero p, eqToIso.hom,
    ← singlePlusMapAt_eqToHom
      (O := (TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf) 0
      (deRhamComplexInt_X_zero p)]

include hΩ in
/-- **De Rham cohomology vanishes wherever the cohomology of `Ω⁰_{X/S}` does**, when
`Ωᵏ_{X/S} = 0` for `k ≥ 1`. -/
theorem isZero_deRhamCohomologyBaseModule_of_isZero (q : ℕ)
    (h : IsZero
      (hypercohomology X.sheaf (singlePlus X.sheaf (relativeDifferentialForms p 0) 0) q)) :
    IsZero (deRhamCohomologyBaseModule p (q : ℤ)) :=
  have := (deRhamCohomologyEquivFormsZero p hΩ q).toEquiv.subsingleton_congr.mpr
    (ModuleCat.subsingleton_of_isZero h)
  ModuleCat.isZero_of_subsingleton _

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- De Rham cohomology vanishes in negative degrees. -/
theorem isZero_deRhamCohomologyBaseModule_of_neg (k : ℤ) (hk : k < 0) :
    IsZero (deRhamCohomologyBaseModule p k) :=
  have : Subsingleton ↥(SheafOfModules.deRhamCohomology (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) k) :=
    (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p))
        k).toLinearEquiv.toEquiv.subsingleton_congr.mp
      (ModuleCat.subsingleton_of_isZero (isZero_hypercohomology _ _ 0 k hk))
  @ModuleCat.isZero_of_subsingleton _ _ (deRhamCohomologyBaseModule p k) this

end AlgebraicGeometry.Scheme.Hom
