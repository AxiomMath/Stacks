module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.HomGlue
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.AffineSections
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsCharts
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.IdealSheafOfHomComap
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineOpenTensorSections
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Sheaf

/-!
# Existence of the maps of Section 0FL7

For a locally quasi-finite syntomic morphism `f : Y ⟶ X` we glue the maps of Remark 0FL9 on the
charts `(U, V)` of `f` for which `Γ(Y, V)` has a square relative global complete intersection
presentation over `Γ(X, U)` (these cover `Y` by Discriminants, Lemma 0BWE) into maps
`c^p : Ω^p_{Y/ℤ} ⟶ f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})`, and show that they satisfy the conditions
(0H9C) and (0H9D) of Section 0FL7.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.chartGarelMaps`: the glued maps.

## Main results

* `AlgebraicGeometry.Scheme.Hom.chartGarelMaps_app`: on a presented chart they are the maps of
  Remark 0FL9.
* `AlgebraicGeometry.Scheme.Hom.chartGarelMaps_isNormalized`: condition (0H9C).
* `AlgebraicGeometry.Scheme.Hom.chartGarelMaps_isMultiplicative`: condition (0H9D).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- A chart `(U, V)` of `f` is *presented* when `Γ(Y, V)` has a square presentation over
`Γ(X, U)` which is a relative global complete intersection (Remark 0FL9). -/
def ChartPresented (c : f.chartIndex.ι) : Prop :=
  letI := f.chartAlgebra c.2
  ∃ (n : ℕ) (P : Algebra.Presentation Γ(X, c.1.1.1) Γ(Y, c.1.2.1) (Fin n) (Fin n)),
    P.IsRelativeGlobalCompleteIntersection

/-- Every chart of a locally quasi-finite syntomic morphism is refined near each of its points
by a presented chart (Discriminants, Lemma 0BWE, part (5)): a basic open of `V` around the
point, with the same `U`. -/
theorem exists_refines_chartPresented (hf : Syntomic f) [LocallyQuasiFinite f]
    (c : f.chartIndex.ι) {y : Y} (hy : y ∈ (f.chartIndex.V c).1) :
    ∃ c', f.chartIndex.Refines c' c ∧ f.ChartPresented c' ∧ y ∈ (f.chartIndex.V c').1 := by
  let := f.chartAlgebra c.2
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have hV : IsAffineOpen c.1.2.1 := c.1.2.2
  obtain ⟨r, hr, hrgci⟩ := Algebra.Syntomic.exists_notMem_isRelativeGlobalCompleteIntersection
    (R := Γ(X, c.1.1.1)) (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  have hyr : y ∈ Y.basicOpen r := by
    have h : hV.fromSpec (hV.primeIdealOf ⟨y, hy⟩) ∈ Y.basicOpen r := by
      show _ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen r
      rw [hV.fromSpec_preimage_basicOpen r]
      exact (PrimeSpectrum.mem_basicOpen r _).mpr hr
    rwa [hV.fromSpec_primeIdealOf ⟨y, hy⟩] at h
  have hle : Y.basicOpen r ≤ f ⁻¹ᵁ c.1.1.1 := (Y.basicOpen_le r).trans c.2
  let c' : f.chartIndex.ι := ⟨(c.1.1, ⟨Y.basicOpen r, hV.basicOpen r⟩), hle⟩
  refine ⟨c', ⟨Scheme.IsBasicOpenOf.refl _, ⟨r, rfl⟩⟩, ?_, hyr⟩
  let := f.chartAlgebra c'.2
  have := hV.isLocalization_basicOpen r
  have : IsScalarTower Γ(X, c.1.1.1) Γ(Y, c.1.2.1) Γ(Y, Y.basicOpen r) :=
    .of_algebraMap_eq fun x => by
      simp only [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply,
        Scheme.Hom.appLE_map]
      rfl
  have : Algebra.IsRelativeGlobalCompleteIntersection Γ(X, c.1.1.1) Γ(Y, Y.basicOpen r) :=
    .of_algEquiv ((IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r)
      Γ(Y, Y.basicOpen r)).restrictScalars Γ(X, c.1.1.1))
  have : Algebra.QuasiFinite Γ(X, c.1.1.1) Γ(Y, Y.basicOpen r) :=
    f.quasiFinite_chartAlgebra inferInstance c'.1.1 c'.1.2 c'.2
  exact Algebra.exists_square_presentation ((hV.basicOpen r).primeIdealOf ⟨y, hyr⟩).asIdeal

/-! ### The maps of Remark 0FL9 on presented charts -/

section ChartMaps

variable (hf : Syntomic f)

/-- A chosen square relative global complete intersection presentation of a presented chart. -/
def chartPresentation (c : {c : f.chartIndex.ι // f.ChartPresented c}) :
    letI := f.chartAlgebra c.1.2
    Σ n : ℕ, Algebra.Presentation Γ(X, c.1.1.1.1) Γ(Y, c.1.1.2.1) (Fin n) (Fin n) :=
  ⟨_, c.2.choose_spec.choose⟩

/-- The chosen presentation of a presented chart is a relative global complete intersection. -/
instance isRelativeGlobalCompleteIntersection_chartPresentation
    (c : {c : f.chartIndex.ι // f.ChartPresented c}) :
    letI := f.chartAlgebra c.1.2
    (f.chartPresentation c).2.IsRelativeGlobalCompleteIntersection :=
  c.2.choose_spec.choose_spec

/-- The maps of Remark 0FL9 on a presented chart `(U, V)`, with values in
`det(NL_{Γ(V)/Γ(U)})`. -/
def chartGarelMap (c : {c : f.chartIndex.ι // f.ChartPresented c}) (p : ℕ) :
    letI := f.chartAlgebra c.1.2
    (⋀[Γ(Y, c.1.1.2.1)]^p Ω[Γ(Y, c.1.1.2.1)⁄ℤ]) →ₗ[Γ(Y, c.1.1.2.1)]
      (⋀[Γ(Y, c.1.1.2.1)]^p (Γ(Y, c.1.1.2.1) ⊗[Γ(X, c.1.1.1.1)] Ω[Γ(X, c.1.1.1.1)⁄ℤ]))
        ⊗[Γ(Y, c.1.1.2.1)] f.detNLChart hf c.1 :=
  letI := f.chartAlgebra c.1.2
  haveI := f.syntomic_chartAlgebra hf c.1.1.1 c.1.1.2 c.1.2
  Stacks.DeRham.presentationDetNLMap (f.chartPresentation c).2 p

attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-- The sections over `V` of `f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})` are
`Γ(f^*Ω^p_{X/ℤ}, V) ⊗ Γ(det(NL_{Y/X}), V)`, for `V` affine. -/
def twistedSectionsEquiv {V : Y.Opens} (hV : IsAffineOpen V) (L : Y.Modules) [L.IsQuasicoherent]
    (p : ℕ) :
    Γ(f.twistedPullbackForms L p, V) ≃ₗ[Γ(Y, V)] Γ(f.pullbackForms p, V) ⊗[Γ(Y, V)] Γ(L, V) :=
  (Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTensorEquiv hV
    (f.pullbackForms p) L).symm

open Stacks.PullbackTensorCoherence in
/-- Restriction of a local pure tensor of `f^*Ω^p_{X/ℤ} ⊗ L` is the pure tensor of the
restrictions. -/
theorem twistedPullbackFormsTmul_restrict (L : Y.Modules) (p : ℕ) {V V' : Y.Opens} (h : V' ≤ V)
    (a : Γ(f.pullbackForms p, V)) (t : Γ(L, V)) :
    (f.twistedPullbackForms L p).presheaf.map (homOfLE h).op
        (f.twistedPullbackFormsTmul L p V a t) =
      f.twistedPullbackFormsTmul L p V' ((f.pullbackForms p).presheaf.map (homOfLE h).op a)
        (L.presheaf.map (homOfLE h).op t) :=
  tmul_restrict (homOfLE h).op a t

/-- `twistedSectionsEquiv` on a pure tensor is the local pure tensor. -/
theorem twistedSectionsEquiv_symm_tmul {V : Y.Opens} (hV : IsAffineOpen V) (L : Y.Modules)
    [L.IsQuasicoherent] (p : ℕ) (a : Γ(f.pullbackForms p, V)) (t : Γ(L, V)) :
    (f.twistedSectionsEquiv hV L p).symm (a ⊗ₜ t) = f.twistedPullbackFormsTmul L p V a t :=
  rfl

variable {f} in
/-- The maps of Remark 0FL9 on presented charts are natural under refinement (Lemma 0H9F
for the localizations `Γ(U) → Γ(U')`, `Γ(V) → Γ(V')`): the maps on a refinement, precomposed
with the restriction of forms, are the maps on the chart followed by the base change of pulled
back forms and of determinants. -/
theorem chartGarelMap_restrict [LocallyQuasiFinite f]
    (c c' : {c : f.chartIndex.ι // f.ChartPresented c}) (h : f.chartIndex.Refines c'.1 c.1)
    (p : ℕ) (η : letI := f.chartAlgebra c.1.2; ⋀[Γ(Y, c.1.1.2.1)]^p Ω[Γ(Y, c.1.1.2.1)⁄ℤ]) :
    letI := f.chartAlgebra c.1.2
    letI := f.chartAlgebra c'.1.2
    letI := X.restrictAlgebra h.1.le
    letI := Y.restrictAlgebra h.2.le
    letI := f.chartAlgebra (h.2.le.trans c.1.2)
    haveI := f.isScalarTower_chartAlgebra_restrict c.1.2 c'.1.2 h.1.le h.2.le
    haveI := f.isScalarTower_restrict_chartAlgebra c.1.2 h.2.le
    f.chartGarelMap hf c' p (ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, c.1.1.2.1)
        Γ(Y, c'.1.1.2.1)) (Stacks.DeRham.kaehlerMapₛₗ Γ(Y, c.1.1.2.1) Γ(Y, c'.1.1.2.1)) η) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, c.1.1.2.1)
          Γ(Y, c'.1.1.2.1)) (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1)
            Γ(Y, c.1.1.2.1) Γ(X, c'.1.1.1.1) Γ(Y, c'.1.1.2.1)))
        (f.detNLChartRestrict hf h) (f.chartGarelMap hf c p η) := by
  let := f.chartAlgebra c.1.2
  let := f.chartAlgebra c'.1.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := f.chartAlgebra (h.2.le.trans c.1.2)
  have := f.isScalarTower_chartAlgebra_restrict c.1.2 c'.1.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.1.2 h.2.le
  have := f.syntomic_chartAlgebra hf c.1.1.1 c.1.1.2 c.1.2
  have := f.syntomic_chartAlgebra hf c'.1.1.1 c'.1.1.2 c'.1.2
  exact f.presentationDetNLMap_detNLChartRestrict hf h (f.chartPresentation c).2
    (f.chartPresentation c').2 p η

/-- The identification of the sections of `f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})` over a presented chart
with the ring-level module. -/
def chartTwistedEquiv (c : {c : f.chartIndex.ι // f.ChartPresented c}) (p : ℕ) :
    letI := f.chartAlgebra c.1.2
    Γ(f.twistedPullbackForms (f.detNL hf) p, c.1.1.2.1) ≃ₗ[Γ(Y, c.1.1.2.1)]
      (⋀[Γ(Y, c.1.1.2.1)]^p (Γ(Y, c.1.1.2.1) ⊗[Γ(X, c.1.1.1.1)] Ω[Γ(X, c.1.1.1.1)⁄ℤ]))
        ⊗[Γ(Y, c.1.1.2.1)] f.detNLChart hf c.1 :=
  letI := f.chartAlgebra c.1.2
  f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p ≪≫ₗ
    TensorProduct.congr (Scheme.pullbackFormsSectionsEquiv c.1.1.2.2 f c.1.1.1.2 c.1.2 p)
      (f.detNLSectionsEquiv hf c.1)

/-- `chartTwistedEquiv` on a local pure tensor. -/
theorem chartTwistedEquiv_tmul (c : {c : f.chartIndex.ι // f.ChartPresented c}) (p : ℕ)
    (a : Γ(f.pullbackForms p, c.1.1.2.1)) (t : Γ(f.detNL hf, c.1.1.2.1)) :
    letI := f.chartAlgebra c.1.2
    f.chartTwistedEquiv hf c p (f.twistedPullbackFormsTmul (f.detNL hf) p c.1.1.2.1 a t) =
      Scheme.pullbackFormsSectionsEquiv c.1.1.2.2 f c.1.1.1.2 c.1.2 p a ⊗ₜ
        f.detNLSectionsEquiv hf c.1 t := by
  let := f.chartAlgebra c.1.2
  refine (congrArg (f.chartTwistedEquiv hf c p)
    (f.twistedSectionsEquiv_symm_tmul c.1.1.2.2 (f.detNL hf) p a t).symm).trans ?_
  simp only [chartTwistedEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul]

variable {f} in
/-- `chartTwistedEquiv` is natural under restriction to a refinement, on local pure tensors. -/
theorem chartTwistedEquiv_restrict_tmul
    (c c' : {c : f.chartIndex.ι // f.ChartPresented c}) (h : f.chartIndex.Refines c'.1 c.1)
    (p : ℕ) (a : Γ(f.pullbackForms p, c.1.1.2.1)) (t : Γ(f.detNL hf, c.1.1.2.1)) :
    letI := f.chartAlgebra c.1.2
    letI := f.chartAlgebra c'.1.2
    letI := X.restrictAlgebra h.1.le
    letI := Y.restrictAlgebra h.2.le
    letI := f.chartAlgebra (h.2.le.trans c.1.2)
    haveI := f.isScalarTower_chartAlgebra_restrict c.1.2 c'.1.2 h.1.le h.2.le
    haveI := f.isScalarTower_restrict_chartAlgebra c.1.2 h.2.le
    f.chartTwistedEquiv hf c' p
        ((f.twistedPullbackForms (f.detNL hf) p).presheaf.map (homOfLE h.2.le).op
          (f.twistedPullbackFormsTmul (f.detNL hf) p c.1.1.2.1 a t)) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, c.1.1.2.1)
          Γ(Y, c'.1.1.2.1)) (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1)
            Γ(Y, c.1.1.2.1) Γ(X, c'.1.1.1.1) Γ(Y, c'.1.1.2.1)))
        (f.detNLChartRestrict hf h)
        (f.chartTwistedEquiv hf c p (f.twistedPullbackFormsTmul (f.detNL hf) p c.1.1.2.1 a t)) := by
  let := f.chartAlgebra c.1.2
  let := f.chartAlgebra c'.1.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := f.chartAlgebra (h.2.le.trans c.1.2)
  have := f.isScalarTower_chartAlgebra_restrict c.1.2 c'.1.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.1.2 h.2.le
  refine (congrArg (f.chartTwistedEquiv hf c' p)
    (f.twistedPullbackFormsTmul_restrict (f.detNL hf) p h.2.le a t)).trans ?_
  refine (f.chartTwistedEquiv_tmul hf c' p _ _).trans ?_
  refine Eq.trans ?_ (congrArg _ (f.chartTwistedEquiv_tmul hf c p a t)).symm
  refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
  exact congrArg₂ (· ⊗ₜ ·)
    (Scheme.pullbackFormsSectionsEquiv_restrict_formsBaseChangeMapₛₗ c.1.1.2.2 c'.1.1.2.2 f
      c.1.1.1.2 c'.1.1.1.2 c.1.2 c'.1.2 h.1.le h.2.le p a)
    (f.detNLSectionsEquiv_restrict hf h t)

variable {f} in
/-- `chartTwistedEquiv` is natural under restriction to a refinement of presented charts. -/
theorem chartTwistedEquiv_restrict
    (c c' : {c : f.chartIndex.ι // f.ChartPresented c}) (h : f.chartIndex.Refines c'.1 c.1)
    (p : ℕ) (x : Γ(f.twistedPullbackForms (f.detNL hf) p, c.1.1.2.1)) :
    letI := f.chartAlgebra c.1.2
    letI := f.chartAlgebra c'.1.2
    letI := X.restrictAlgebra h.1.le
    letI := Y.restrictAlgebra h.2.le
    letI := f.chartAlgebra (h.2.le.trans c.1.2)
    haveI := f.isScalarTower_chartAlgebra_restrict c.1.2 c'.1.2 h.1.le h.2.le
    haveI := f.isScalarTower_restrict_chartAlgebra c.1.2 h.2.le
    f.chartTwistedEquiv hf c' p
        ((f.twistedPullbackForms (f.detNL hf) p).presheaf.map (homOfLE h.2.le).op x) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, c.1.1.2.1)
          Γ(Y, c'.1.1.2.1)) (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1)
            Γ(Y, c.1.1.2.1) Γ(X, c'.1.1.1.1) Γ(Y, c'.1.1.2.1)))
        (f.detNLChartRestrict hf h) (f.chartTwistedEquiv hf c p x) := by
  let := f.chartAlgebra c.1.2
  let := f.chartAlgebra c'.1.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := f.chartAlgebra (h.2.le.trans c.1.2)
  have := f.isScalarTower_chartAlgebra_restrict c.1.2 c'.1.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.1.2 h.2.le
  suffices H : ∀ z, f.chartTwistedEquiv hf c' p
      ((f.twistedPullbackForms (f.detNL hf) p).presheaf.map (homOfLE h.2.le).op
        ((f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p).symm z)) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, c.1.1.2.1)
          Γ(Y, c'.1.1.2.1)) (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1)
            Γ(Y, c.1.1.2.1) Γ(X, c'.1.1.1.1) Γ(Y, c'.1.1.2.1)))
        (f.detNLChartRestrict hf h) (f.chartTwistedEquiv hf c p
          ((f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p).symm z)) by
    simpa only [LinearEquiv.symm_apply_apply] using
      H (f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p x)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a t => exact chartTwistedEquiv_restrict_tmul hf c c' h p a t

/-- The maps of Remark 0FL9 on the sections over a presented chart:
`Γ(Ω^p_{Y/ℤ}, V) → Γ(f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X}), V)`. -/
def chartGarelSectionMap (c : {c : f.chartIndex.ι // f.ChartPresented c}) (p : ℕ) :
    Γ(absoluteDifferentialForms Y p, c.1.1.2.1) →ₗ[Γ(Y, c.1.1.2.1)]
      Γ(f.twistedPullbackForms (f.detNL hf) p, c.1.1.2.1) :=
  letI := f.chartAlgebra c.1.2
  (f.chartTwistedEquiv hf c p).symm.toLinearMap ∘ₗ f.chartGarelMap hf c p ∘ₗ
    (Scheme.absoluteFormsSectionsEquiv Y c.1.1.2.2 p).toLinearMap

/-- `chartGarelSectionMap` read through `chartTwistedEquiv`. -/
theorem chartTwistedEquiv_chartGarelSectionMap (c : {c : f.chartIndex.ι // f.ChartPresented c})
    (p : ℕ) (s : Γ(absoluteDifferentialForms Y p, c.1.1.2.1)) :
    f.chartTwistedEquiv hf c p (f.chartGarelSectionMap hf c p s) =
      f.chartGarelMap hf c p (Scheme.absoluteFormsSectionsEquiv Y c.1.1.2.2 p s) := by
  let := f.chartAlgebra c.1.2
  simp only [chartGarelSectionMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

variable {f} in
/-- The maps on the sections over presented charts commute with the restriction maps. -/
theorem chartGarelSectionMap_restrict [LocallyQuasiFinite f]
    (c c' : {c : f.chartIndex.ι // f.ChartPresented c}) (h : f.chartIndex.Refines c'.1 c.1)
    (p : ℕ) (s : Γ(absoluteDifferentialForms Y p, c.1.1.2.1)) :
    f.chartGarelSectionMap hf c' p
        ((absoluteDifferentialForms Y p).presheaf.map (homOfLE h.2.le).op s) =
      (f.twistedPullbackForms (f.detNL hf) p).presheaf.map (homOfLE h.2.le).op
        (f.chartGarelSectionMap hf c p s) := by
  let := f.chartAlgebra c.1.2
  let := f.chartAlgebra c'.1.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := f.chartAlgebra (h.2.le.trans c.1.2)
  have := f.isScalarTower_chartAlgebra_restrict c.1.2 c'.1.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.1.2 h.2.le
  refine (f.chartTwistedEquiv hf c' p).injective ?_
  refine (f.chartTwistedEquiv_chartGarelSectionMap hf c' p _).trans ?_
  refine Eq.trans ?_ (chartTwistedEquiv_restrict hf c c' h p _).symm
  refine (congrArg (f.chartGarelMap hf c' p)
    (Scheme.absoluteFormsSectionsEquiv_restrict_kaehlerMapₛₗ c.1.1.2.2 c'.1.1.2.2 h.2.le p
      s)).trans ?_
  refine (chartGarelMap_restrict hf c c' h p _).trans ?_
  exact congrArg _ (f.chartTwistedEquiv_chartGarelSectionMap hf c p s).symm

/-! ### The glued maps -/

variable [LocallyQuasiFinite f]

/-- The maps of Section 0FL7 of a locally quasi-finite syntomic morphism, glued (Stacks 009U)
from the maps of Remark 0FL9 on the presented charts. -/
def chartGarelMaps : f.GarelMaps (f.detNL hf) := fun p =>
  f.chartIndex.homOfCompatible f.ChartPresented
    (fun c _ hy => f.exists_refines_chartPresented hf c hy) (fun c => c.1.1.2.1) (fun _ => rfl)
    (fun c => f.chartGarelSectionMap hf c p)
    (fun c c' h i s => by
      obtain rfl : i = homOfLE h.2.le := Subsingleton.elim _ _
      have L := chartGarelSectionMap_restrict hf c c' h p s
      refine Eq.trans ?_ (L.trans ?_)
      · exact congrArg (f.chartGarelSectionMap hf c' p) rfl
      · exact rfl)

/-- The glued maps on a presented chart are the maps of Remark 0FL9. -/
theorem chartGarelMaps_app (p : ℕ) (c : {c : f.chartIndex.ι // f.ChartPresented c})
    (s : Γ(absoluteDifferentialForms Y p, c.1.1.2.1)) :
    (f.chartGarelMaps hf p).app c.1.1.2.1 s = f.chartGarelSectionMap hf c p s :=
  f.chartIndex.homOfCompatible_app f.ChartPresented _ (fun c => c.1.1.2.1) (fun _ => rfl) _ _ c s

/-- The glued maps on a presented chart, read through `chartTwistedEquiv`. -/
theorem chartTwistedEquiv_chartGarelMaps_app (p : ℕ)
    (c : {c : f.chartIndex.ι // f.ChartPresented c})
    (s : Γ(absoluteDifferentialForms Y p, c.1.1.2.1)) :
    f.chartTwistedEquiv hf c p ((f.chartGarelMaps hf p).val.app (op c.1.1.2.1) s) =
      f.chartGarelMap hf c p (Scheme.absoluteFormsSectionsEquiv Y c.1.1.2.2 p s) :=
  (congrArg (f.chartTwistedEquiv hf c p) (f.chartGarelMaps_app hf p c s)).trans
    (f.chartTwistedEquiv_chartGarelSectionMap hf c p s)

/-- Condition (0H9C) for the maps of Remark 0FL9 on a presented chart: the empty wedge goes
to `1 ⊗ δ(NL_{Γ(V)/Γ(U)})`. -/
theorem chartGarelMap_zero (c : {c : f.chartIndex.ι // f.ChartPresented c}) :
    letI := f.chartAlgebra c.1.2
    f.chartGarelMap hf c 0 (exteriorPower.ιMulti Γ(Y, c.1.1.2.1) 0 Fin.elim0) =
      exteriorPower.ιMulti Γ(Y, c.1.1.2.1) 0 Fin.elim0 ⊗ₜ f.deltaNLChart hf c.1 :=
  let := f.chartAlgebra c.1.2
  have := f.syntomic_chartAlgebra hf c.1.1.1 c.1.1.2 c.1.2
  have := f.quasiFinite_chartAlgebra inferInstance c.1.1.1 c.1.1.2 c.1.2
  (Stacks.DeRham.isFunnyMapFamily_presentationDetNLMap (f.chartPresentation c).2).map_zero

/-- Condition (0H9D) for the maps of Remark 0FL9 on a presented chart: they commute with
wedging on the left by base-changed forms on `Γ(U)`. -/
theorem chartGarelMap_wedge (c : {c : f.chartIndex.ι // f.ChartPresented c}) (q p : ℕ)
    (ω : letI := f.chartAlgebra c.1.2;
      ⋀[Γ(Y, c.1.1.2.1)]^q (Γ(Y, c.1.1.2.1) ⊗[Γ(X, c.1.1.1.1)] Ω[Γ(X, c.1.1.1.1)⁄ℤ]))
    (η : ⋀[Γ(Y, c.1.1.2.1)]^p Ω[Γ(Y, c.1.1.2.1)⁄ℤ]) :
    letI := f.chartAlgebra c.1.2
    f.chartGarelMap hf c (q + p) (exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p
        (exteriorPower.map q (KaehlerDifferential.mapBaseChange ℤ Γ(X, c.1.1.1.1)
          Γ(Y, c.1.1.2.1)) ω) η) =
      (exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p ω).rTensor _
        (f.chartGarelMap hf c p η) :=
  let := f.chartAlgebra c.1.2
  have := f.syntomic_chartAlgebra hf c.1.1.1 c.1.1.2 c.1.2
  have := f.quasiFinite_chartAlgebra inferInstance c.1.1.1 c.1.1.2 c.1.2
  (Stacks.DeRham.isFunnyMapFamily_presentationDetNLMap (f.chartPresentation c).2).map_wedge
    q p ω η

open Stacks.RingedSpace Stacks.PullbackTensorCoherence in
/-- A local pure tensor is additive in its second factor. -/
theorem _root_.Stacks.PullbackTensorCoherence.tmul_add_right {Z : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureRingSheaf Z)} (U : (TopologicalSpace.Opens Z.carrier)ᵒᵖ)
    (a : A.val.obj U) (b b' : B.val.obj U) :
    tmul Z A B U a (b + b') = tmul Z A B U a b + tmul Z A B U a b' := by
  simp only [tmul, TensorProduct.tmul_add]
  exact LinearMap.map_add (((PresheafOfModules.tensorSheafUnit A B).app U).hom) _ _

open Stacks.RingedSpace Stacks.PullbackTensorCoherence in
/-- A local pure tensor with second factor zero is zero. -/
theorem _root_.Stacks.PullbackTensorCoherence.tmul_zero_right {Z : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureRingSheaf Z)} (U : (TopologicalSpace.Opens Z.carrier)ᵒᵖ)
    (a : A.val.obj U) : tmul Z A B U a 0 = 0 := by
  simp only [tmul, TensorProduct.tmul_zero]
  exact LinearMap.map_zero (((PresheafOfModules.tensorSheafUnit A B).app U).hom)

omit [LocallyQuasiFinite f] in
open Stacks.PullbackTensorCoherence in
/-- The left action of pulled back forms on `f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})` on a presented chart,
on a local pure tensor. -/
theorem chartTwistedEquiv_twistedPullbackFormsMul_tmul
    (c : {c : f.chartIndex.ι // f.ChartPresented c}) (q p : ℕ)
    (ω : Γ(f.pullbackForms q, c.1.1.2.1)) (a : Γ(f.pullbackForms p, c.1.1.2.1))
    (t : Γ(f.detNL hf, c.1.1.2.1)) :
    letI := f.chartAlgebra c.1.2
    f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms (f.detNL hf) p)
            (op c.1.1.2.1) ω (f.twistedPullbackFormsTmul (f.detNL hf) p c.1.1.2.1 a t))) =
      (exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p
        (Scheme.pullbackFormsSectionsEquiv c.1.1.2.2 f c.1.1.1.2 c.1.2 q ω)).rTensor _
        (f.chartTwistedEquiv hf c p (f.twistedPullbackFormsTmul (f.detNL hf) p c.1.1.2.1 a t)) := by
  let := f.chartAlgebra c.1.2
  have e₁ : eqToHom (congrArg (f.twistedPullbackForms (f.detNL hf)) (Nat.cast_add q p).symm) =
      𝟙 _ := eqToHom_refl _ _
  have e₂ : eqToHom (congrArg f.pullbackForms (Nat.cast_add q p).symm) = 𝟙 _ :=
    eqToHom_refl _ _
  have hE : (eqToHom (congrArg (f.twistedPullbackForms (f.detNL hf))
      (Nat.cast_add q p).symm)).val.app (op c.1.1.2.1)
        (f.twistedPullbackFormsTmul (f.detNL hf) (q + p) c.1.1.2.1
          (((pullbackFormsAlgebra f).mul q p).app (op c.1.1.2.1) ω a) t) =
      f.twistedPullbackFormsTmul (f.detNL hf) ((q + p : ℕ) : ℤ) c.1.1.2.1
        ((eqToHom (congrArg f.pullbackForms (Nat.cast_add q p).symm)).val.app (op c.1.1.2.1)
          (((pullbackFormsAlgebra f).mul q p).app (op c.1.1.2.1) ω a)) t := by
    rw [e₁, e₂]
    rfl
  refine (congrArg (f.chartTwistedEquiv hf c (q + p))
    (twistedPullbackFormsMul_tmul f (f.detNL hf) q p c.1.1.2.1 ω a t)).trans ?_
  refine (congrArg (f.chartTwistedEquiv hf c (q + p)) hE).trans ?_
  refine (f.chartTwistedEquiv_tmul hf c (q + p) _ t).trans ?_
  refine (congrArg (· ⊗ₜ f.detNLSectionsEquiv hf c.1 t)
    (Scheme.pullbackFormsSectionsEquiv_mul c.1.1.2.2 f c.1.1.1.2 c.1.2 q p ω a)).trans ?_
  refine (LinearMap.rTensor_tmul _ _ _ _).symm.trans ?_
  exact congrArg _ (f.chartTwistedEquiv_tmul hf c p a t).symm

omit [LocallyQuasiFinite f] in
open Stacks.PullbackTensorCoherence in
/-- The left action of pulled back forms on `f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})` on a presented
chart is the wedge product on the first factor. -/
theorem chartTwistedEquiv_twistedPullbackFormsMul
    (c : {c : f.chartIndex.ι // f.ChartPresented c}) (q p : ℕ)
    (ω : Γ(f.pullbackForms q, c.1.1.2.1))
    (x : Γ(f.twistedPullbackForms (f.detNL hf) p, c.1.1.2.1)) :
    letI := f.chartAlgebra c.1.2
    f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms (f.detNL hf) p)
            (op c.1.1.2.1) ω x)) =
      (exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p
        (Scheme.pullbackFormsSectionsEquiv c.1.1.2.2 f c.1.1.1.2 c.1.2 q ω)).rTensor _
        (f.chartTwistedEquiv hf c p x) := by
  let := f.chartAlgebra c.1.2
  suffices H : ∀ z, f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms (f.detNL hf) p)
            (op c.1.1.2.1) ω ((f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p).symm z))) =
      (exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p
        (Scheme.pullbackFormsSectionsEquiv c.1.1.2.2 f c.1.1.1.2 c.1.2 q ω)).rTensor _
        (f.chartTwistedEquiv hf c p ((f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p).symm z)) by
    simpa only [LinearEquiv.symm_apply_apply] using
      H (f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p x)
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
    refine (congrArg (fun y => f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms (f.detNL hf) p)
            (op c.1.1.2.1) ω y))) (map_zero _)).trans ?_
    refine (congrArg (fun y => f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1) y))
      (tmul_zero_right _ ω)).trans ?_
    refine (congrArg (f.chartTwistedEquiv hf c (q + p)) (map_zero _)).trans ?_
    refine (map_zero _).trans ?_
    simp only [map_zero]
  | add z z' hz hz' =>
    refine (congrArg (fun y => f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms (f.detNL hf) p)
            (op c.1.1.2.1) ω y))) (map_add _ _ _)).trans ?_
    refine (congrArg (fun y => f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1) y))
      (tmul_add_right _ ω _ _)).trans ?_
    refine (congrArg (f.chartTwistedEquiv hf c (q + p)) (map_add _ _ _)).trans ?_
    refine (map_add _ _ _).trans ?_
    refine (congrArg₂ (· + ·) hz hz').trans ?_
    simp only [map_add]
  | tmul a t =>
    refine (congrArg (fun y => f.chartTwistedEquiv hf c (q + p)
        ((f.twistedPullbackFormsMul (f.detNL hf) q p).val.app (op c.1.1.2.1)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms (f.detNL hf) p)
            (op c.1.1.2.1) ω y)))
      (f.twistedSectionsEquiv_symm_tmul c.1.1.2.2 (f.detNL hf) p a t)).trans ?_
    refine (f.chartTwistedEquiv_twistedPullbackFormsMul_tmul hf c q p ω a t).trans ?_
    exact congrArg (fun y => (exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p
        (Scheme.pullbackFormsSectionsEquiv c.1.1.2.2 f c.1.1.1.2 c.1.2 q ω)).rTensor _
        (f.chartTwistedEquiv hf c p y))
      (f.twistedSectionsEquiv_symm_tmul c.1.1.2.2 (f.detNL hf) p a t).symm

include hf in
/-- Every point of `Y` lies in a presented chart. -/
theorem exists_chartPresented_mem (y : Y) :
    ∃ c : {c : f.chartIndex.ι // f.ChartPresented c}, y ∈ c.1.1.2.1 := by
  obtain ⟨c, hc⟩ := f.chartIndex.exists_mem y
  obtain ⟨c', -, hK, hy⟩ := f.exists_refines_chartPresented hf c hc
  exact ⟨⟨c', hK⟩, hy⟩

/-- The glued maps satisfy condition (0H9C): `c^0(1) = δ(NL_{Y/X})`. -/
theorem chartGarelMaps_isNormalized : (f.chartGarelMaps hf).IsNormalized (f.deltaNL hf) := by
  refine (GarelMaps.isNormalized_iff _ _).mpr ?_
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover _
    (fun c : {c : f.chartIndex.ι // f.ChartPresented c} => c.1.1.2.1) (fun _ => le_top)
    (fun y _ => f.exists_chartPresented_mem hf y) _ _ fun c => ?_
  refine (f.chartTwistedEquiv hf c 0).injective ?_
  refine (congrArg (f.chartTwistedEquiv hf c 0) (PresheafOfModules.naturality_apply
    (f.chartGarelMaps hf 0).val (homOfLE (le_top : c.1.1.2.1 ≤ ⊤)).op _).symm).trans ?_
  refine (congrArg (fun z => f.chartTwistedEquiv hf c 0
    ((f.chartGarelMaps hf 0).val.app (op c.1.1.2.1) z))
    (?e₁ : _ = (absoluteDifferentialFormsAlgebra Y).one.eval (op c.1.1.2.1))).trans ?_
  case e₁ =>
    exact SheafOfModules.GradedAlgebra.one_eval_map (absoluteDifferentialFormsAlgebra Y)
      (homOfLE (le_top : c.1.1.2.1 ≤ ⊤)).op
  refine (f.chartTwistedEquiv_chartGarelMaps_app hf 0 c _).trans ?_
  refine (congrArg (f.chartGarelMap hf c 0)
    (?e : _ = exteriorPower.ιMulti Γ(Y, c.1.1.2.1) 0 Fin.elim0)).trans ?_
  case e => exact Scheme.absoluteFormsSectionsEquiv_one Y c.1.1.2.2
  refine (f.chartGarelMap_zero hf c).trans ?_
  refine Eq.trans ?_ (congrArg (f.chartTwistedEquiv hf c 0)
    (f.twistedPullbackFormsTmul_restrict (f.detNL hf) 0 (le_top : c.1.1.2.1 ≤ ⊤) _ _)).symm
  refine Eq.trans ?_ (congrArg (fun z => f.chartTwistedEquiv hf c 0
    (f.twistedPullbackFormsTmul (f.detNL hf) 0 c.1.1.2.1 z
      ((f.detNL hf).presheaf.map (homOfLE (le_top : c.1.1.2.1 ≤ ⊤)).op (f.deltaNL hf))))
    (?e₂ : _ = (pullbackFormsAlgebra f).one.eval (op c.1.1.2.1))).symm
  case e₂ =>
    exact SheafOfModules.GradedAlgebra.one_eval_map (pullbackFormsAlgebra f)
      (homOfLE (le_top : c.1.1.2.1 ≤ ⊤)).op
  refine Eq.trans ?_ (f.chartTwistedEquiv_tmul hf c 0 _ _).symm
  exact congrArg₂ (· ⊗ₜ ·)
    (Scheme.pullbackFormsSectionsEquiv_one c.1.1.2.2 f c.1.1.1.2 c.1.2).symm
    (f.detNLSectionsEquiv_deltaNL hf c.1).symm

/-- The glued maps satisfy condition (0H9D): `c^{q+p}(ω ∧ η) = ω ∧ c^p(η)`. -/
theorem chartGarelMaps_isMultiplicative : (f.chartGarelMaps hf).IsMultiplicative := by
  refine GarelMaps.isMultiplicative_of_isBasis _
    (f.chartIndex.isBasis_of_refines f.ChartPresented
      (fun c _ hy => f.exists_refines_chartPresented hf c hy) (fun c => c.1.1.2.1) (fun _ => rfl))
    (fun _ _ => Set.univ) (fun _ _ _ => Submodule.span_univ) ?_
  rintro q p _ ⟨c, rfl⟩ ω - η
  refine (f.chartTwistedEquiv hf c (q + p)).injective ?_
  refine (congrArg (fun y => f.chartTwistedEquiv hf c (q + p)
    ((f.chartGarelMaps hf (q + p)).val.app (op c.1.1.2.1) y))
    (absoluteFormsAction_tmul f q p c.1.1.2.1 ω η)).trans ?_
  refine (f.chartTwistedEquiv_chartGarelMaps_app hf (q + p) c _).trans ?_
  refine (congrArg (f.chartGarelMap hf c (q + p))
    (?e₁ : _ = exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p
      (Scheme.absoluteFormsSectionsEquiv Y c.1.1.2.2 q
        ((f.absoluteFormsMap q).val.app (op c.1.1.2.1) ω))
      (Scheme.absoluteFormsSectionsEquiv Y c.1.1.2.2 p η))).trans ?_
  case e₁ => exact Scheme.absoluteFormsSectionsEquiv_mul Y c.1.1.2.2 q p _ η
  refine (congrArg (fun y => f.chartGarelMap hf c (q + p)
    (exteriorPower.wedgeMul (R := Γ(Y, c.1.1.2.1)) q p y
      (Scheme.absoluteFormsSectionsEquiv Y c.1.1.2.2 p η)))
    (?e₂ : _ = (let := f.chartAlgebra c.1.2
      exteriorPower.map q (KaehlerDifferential.mapBaseChange ℤ Γ(X, c.1.1.1.1) Γ(Y, c.1.1.2.1))
        (Scheme.pullbackFormsSectionsEquiv c.1.1.2.2 f c.1.1.1.2 c.1.2 q ω)))).trans ?_
  case e₂ =>
    exact Scheme.absoluteFormsSectionsEquiv_absoluteFormsMap c.1.1.2.2 f c.1.1.1.2 c.1.2 q ω
  refine (f.chartGarelMap_wedge hf c q p _ _).trans ?_
  refine Eq.trans ?_ (f.chartTwistedEquiv_twistedPullbackFormsMul hf c q p ω _).symm
  exact congrArg _ (f.chartTwistedEquiv_chartGarelMaps_app hf p c η).symm

end ChartMaps

end AlgebraicGeometry.Scheme.Hom

end
