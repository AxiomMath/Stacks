module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.AffineSections
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineOpenTensorSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Stalk
public import StacksFrontier.Cotangent.DirectedColimit

/-!
# Rigidity of the maps of Section 0FL7 on a nice universal chart

Let `B₀` be an algebra over `ℤ[σ] = MvPolynomial σ ℤ` with a square presentation `P₀`, and let
`h ∈ B₀` be such that `B₀[1/h]` is a domain, quasi-finite and syntomic over `ℤ[σ]`, in which the
Jacobian determinant of `P₀` is nonzero. These are the nice charts of the universal family
produced by `AlgebraicGeometry.exists_niceChartSquare`. For the morphism
`f : Spec B₀[1/h] ⟶ Spec ℤ[σ]` this file supplies the hypotheses of
`AlgebraicGeometry.Scheme.Hom.GarelMaps.app_eq_of_isSMulRegular` on the chart `(⊤, ⊤)`, with
`L = det(NL_{Y/X})` and `J` the image of the Jacobian determinant, and deduces that two families
of maps as in Section 0FL7 satisfying (0H9C) for `δ(NL_{Y/X})` and (0H9D) agree (proof of Stacks
Tag 0FLA).

## Main results

* `AlgebraicGeometry.NiceChart.syntomic_hom`, `AlgebraicGeometry.NiceChart.locallyQuasiFinite_hom`:
  the chart morphism is syntomic and locally quasi-finite.
* `AlgebraicGeometry.NiceChart.exists_niceChart_hypotheses`: the hypotheses of the rigidity of
  the maps of Section 0FL7 on the chart `(⊤, ⊤)`.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.eq_of_niceChart`: two such families of maps are equal.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.NiceChart

variable (σ : Type u) {B₀ : Type u} [CommRing B₀] [Algebra (MvPolynomial σ ℤ) B₀] (h : B₀)

/-- The morphism `Spec B₀[1/h] ⟶ Spec ℤ[σ]` of a nice universal chart. -/
abbrev hom : Spec (.of (Localization.Away h)) ⟶ Spec (.of (MvPolynomial σ ℤ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial σ ℤ) (Localization.Away h)))

/-- The morphism of a nice universal chart is syntomic. -/
theorem syntomic_hom [Algebra.Syntomic (MvPolynomial σ ℤ) (Localization.Away h)] :
    Syntomic (hom σ h) := by
  refine HasRingHomProperty.Spec_iff.mpr ?_
  rw [CommRingCat.hom_ofHom, RingHom.syntomic_iff, toAlgebra_algebraMap]
  infer_instance

/-- The morphism of a nice universal chart is locally quasi-finite. -/
theorem locallyQuasiFinite_hom [Algebra.QuasiFinite (MvPolynomial σ ℤ) (Localization.Away h)] :
    LocallyQuasiFinite (hom σ h) := by
  refine HasRingHomProperty.Spec_iff.mpr ?_
  rw [CommRingCat.hom_ofHom, RingHom.quasiFinite_algebraMap]
  infer_instance

/-- The ring maps of global sections of a nice universal chart are those of the chart. -/
theorem ΓSpecIso_hom_appLE (e : (⊤ : (Spec (.of (Localization.Away h))).Opens) ≤ hom σ h ⁻¹ᵁ ⊤)
    (a : Γ(Spec (.of (MvPolynomial σ ℤ)), ⊤)) :
    (Scheme.ΓSpecIso (.of (Localization.Away h))).hom ((hom σ h).appLE ⊤ ⊤ e a) =
      algebraMap (MvPolynomial σ ℤ) (Localization.Away h)
        ((Scheme.ΓSpecIso (.of (MvPolynomial σ ℤ))).hom a) := by
  have h1 : (hom σ h).appLE ⊤ ⊤ e = (hom σ h).appTop := (hom σ h).appLE_eq_app
  have := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (algebraMap (MvPolynomial σ ℤ) (Localization.Away h))))
  rw [h1]
  exact this

variable {σ} {n : ℕ} (P₀ : Algebra.Presentation (MvPolynomial σ ℤ) B₀ (Fin n) (Fin n))

/-- The image in `Γ(Spec B₀[1/h], ⊤)` of the Jacobian determinant of the square presentation
`P₀`. -/
def jacobian : Γ(Spec (.of (Localization.Away h)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Localization.Away h))).inv
    (algebraMap B₀ (Localization.Away h) P₀.relationJacobiMatrix.det)

/-- The Jacobian determinant kills the relative differentials of the chart. -/
theorem jacobian_smul_eq_zero (e : (⊤ : (Spec (.of (Localization.Away h))).Opens) ≤ hom σ h ⁻¹ᵁ ⊤) :
    letI := ((hom σ h).appLE ⊤ ⊤ e).hom.toAlgebra
    ∀ x : Ω[Γ(Spec (.of (Localization.Away h)), ⊤)⁄Γ(Spec (.of (MvPolynomial σ ℤ)), ⊤)],
      jacobian h P₀ • x = 0 := by
  let := ((hom σ h).appLE ⊤ ⊤ e).hom.toAlgebra
  intro x
  let E := AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv
    (Scheme.ΓSpecIso (.of (MvPolynomial σ ℤ))).commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (.of (Localization.Away h))).commRingCatIsoToRingEquiv
    (fun a => ΓSpecIso_hom_appLE σ h e a)
  apply E.injective
  rw [LinearEquiv.map_smul, LinearEquiv.map_zero]
  have h2 : (Scheme.ΓSpecIso (.of (Localization.Away h))).hom (jacobian h P₀) • E x = 0 := by
    rw [jacobian, Iso.inv_hom_id_apply]
    exact Stacks.DeRham.algebraMap_smul_eq_zero_of_isLocalization (Submonoid.powers h) _
      P₀.relationJacobiMatrix_det_smul_eq_zero (E x)
  exact h2

/-- On the nice chart, every absolute differential is carried by a power of the Jacobian
determinant into the image of the pulled back differentials. -/
theorem exists_pow_jacobian_smul_mem_range
    (e : (⊤ : (Spec (.of (Localization.Away h))).Opens) ≤ hom σ h ⁻¹ᵁ ⊤) :
    letI := ((hom σ h).appLE ⊤ ⊤ e).hom.toAlgebra
    ∀ x : Ω[Γ(Spec (.of (Localization.Away h)), ⊤)⁄ℤ], ∃ k : ℕ,
      jacobian h P₀ ^ k • x ∈ LinearMap.range (KaehlerDifferential.mapBaseChange ℤ
        Γ(Spec (.of (MvPolynomial σ ℤ)), ⊤) Γ(Spec (.of (Localization.Away h)), ⊤)) := by
  let := ((hom σ h).appLE ⊤ ⊤ e).hom.toAlgebra
  exact fun x => Stacks.DeRham.exists_pow_smul_mem_range_mapBaseChange ℤ _
    (fun y => ⟨1, by rw [pow_one]; exact jacobian_smul_eq_zero h P₀ e y⟩) x

/-- The Jacobian determinant of a nice chart is nonzero on global sections. -/
theorem jacobian_ne_zero
    (hjac : algebraMap B₀ (Localization.Away h) P₀.relationJacobiMatrix.det ≠ 0) :
    jacobian h P₀ ≠ 0 := fun H => hjac (by
  simpa [jacobian] using congrArg (Scheme.ΓSpecIso (.of (Localization.Away h))).hom H)

/-- The global sections of a nice chart form a domain. -/
theorem isDomain_Γ [IsDomain (Localization.Away h)] :
    IsDomain Γ(Spec (.of (Localization.Away h)), ⊤) :=
  MulEquiv.isDomain _
    (Scheme.ΓSpecIso (.of (Localization.Away h))).commRingCatIsoToRingEquiv.toMulEquiv

variable (σ) in
/-- The absolute differentials of the global sections of `Spec ℤ[σ]` are free. -/
theorem free_kaehler_Γ :
    Module.Free Γ(Spec (.of (MvPolynomial σ ℤ)), ⊤) Ω[Γ(Spec (.of (MvPolynomial σ ℤ)), ⊤)⁄ℤ] :=
  .of_basis (KaehlerDifferential.basisOfMvPolynomialAlgEquiv
    (AlgEquiv.ofRingEquiv
      (f := (Scheme.ΓSpecIso (.of (MvPolynomial σ ℤ))).commRingCatIsoToRingEquiv)
      (fun x => by simp)))

section Twisted

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

variable (σ) in
/-- The open `⊤` of a nice chart lies over the open `⊤` of `Spec ℤ[σ]`. -/
theorem top_le_preimage_top :
    (⊤ : (Spec (.of (Localization.Away h))).Opens) ≤ hom σ h ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

/-- The sheaf of absolute differential `p`-forms of a scheme is quasi-coherent. -/
private instance isQuasicoherent_absoluteDifferentialForms (X : Scheme.{u}) (p : ℕ) :
    (Scheme.absoluteDifferentialForms X p).IsQuasicoherent :=
  Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ p

variable (σ) in
/-- On a nice chart, the global sections of `f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})` are a projective
module. -/
theorem projective_Γ_twistedPullbackForms (hφ : Syntomic (hom σ h)) (p : ℕ) :
    Module.Projective Γ(Spec (.of (Localization.Away h)), ⊤)
      Γ((hom σ h).twistedPullbackForms ((hom σ h).detNL hφ) p, ⊤) := by
  have e := top_le_preimage_top σ h
  let := ((hom σ h).appLE ⊤ ⊤ e).hom.toAlgebra
  have := free_kaehler_Γ σ
  have : Module.Projective Γ(Spec (.of (Localization.Away h)), ⊤)
      Γ((hom σ h).pullbackForms p, ⊤) :=
    .of_equiv' (Scheme.pullbackFormsSectionsEquiv (isAffineOpen_top _) (hom σ h)
      (isAffineOpen_top _) e p).symm
  let c : (hom σ h).chartIndex.ι := ⟨(⟨⊤, isAffineOpen_top _⟩, ⟨⊤, isAffineOpen_top _⟩), e⟩
  have := (hom σ h).syntomic_chartAlgebra hφ c.1.1 c.1.2 c.2
  have : Module.Projective Γ(Spec (.of (Localization.Away h)), ⊤)
      Γ((hom σ h).detNL hφ, ⊤) :=
    .of_equiv' ((hom σ h).detNLSectionsEquiv hφ c).symm
  exact .of_equiv' (Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTensorEquiv
    (isAffineOpen_top _) ((hom σ h).pullbackForms p) ((hom σ h).detNL hφ))

/-- On a nice chart, the Jacobian determinant is a nonzerodivisor on the global sections of
every `f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})`. -/
theorem isSMulRegular_jacobian [IsDomain (Localization.Away h)]
    (hjac : algebraMap B₀ (Localization.Away h) P₀.relationJacobiMatrix.det ≠ 0)
    (hφ : Syntomic (hom σ h)) (p : ℕ) :
    IsSMulRegular Γ((hom σ h).twistedPullbackForms ((hom σ h).detNL hφ) p, ⊤)
      (jacobian h P₀) := by
  have := isDomain_Γ h
  have := projective_Γ_twistedPullbackForms σ h hφ p
  have : Module.Flat Γ(Spec (.of (Localization.Away h)), ⊤)
      Γ((hom σ h).twistedPullbackForms ((hom σ h).detNL hφ) p, ⊤) :=
    Module.Flat.of_projective
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (jacobian_ne_zero h P₀ hjac))

/-- **The nice-chart hypotheses of the rigidity of the maps of Section 0FL7.** On the chart
`(⊤, ⊤)` of a nice universal chart, there is a nonzerodivisor `J` of the global sections of every
`f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})` some power of which carries every absolute differential into the
image of the pulled back ones: the image of the Jacobian determinant. -/
theorem exists_niceChart_hypotheses [IsDomain (Localization.Away h)]
    (hjac : algebraMap B₀ (Localization.Away h) P₀.relationJacobiMatrix.det ≠ 0)
    (hφ : Syntomic (hom σ h)) (e : (⊤ : (Spec (.of (Localization.Away h))).Opens) ≤ hom σ h ⁻¹ᵁ ⊤) :
    ∃ J : Γ(Spec (.of (Localization.Away h)), ⊤),
      (letI := ((hom σ h).appLE ⊤ ⊤ e).hom.toAlgebra
        ∀ x : Ω[Γ(Spec (.of (Localization.Away h)), ⊤)⁄ℤ], ∃ k : ℕ,
          J ^ k • x ∈ LinearMap.range (KaehlerDifferential.mapBaseChange ℤ
            Γ(Spec (.of (MvPolynomial σ ℤ)), ⊤) Γ(Spec (.of (Localization.Away h)), ⊤))) ∧
      ∀ p : ℕ, IsSMulRegular Γ((hom σ h).twistedPullbackForms ((hom σ h).detNL hφ) p, ⊤) J :=
  ⟨jacobian h P₀, exists_pow_jacobian_smul_mem_range h P₀ e,
    fun p => isSMulRegular_jacobian h P₀ hjac hφ p⟩

/-- The morphism of a nice universal chart is locally quasi-finite. -/
instance [Algebra.QuasiFinite (MvPolynomial σ ℤ) (Localization.Away h)] :
    LocallyQuasiFinite (hom σ h) :=
  locallyQuasiFinite_hom σ h

/-- **Rigidity of the maps of Section 0FL7 on a nice universal chart** (proof of Stacks Tag 0FLA).
Let `B₀[1/h]` be a domain, quasi-finite and syntomic over `ℤ[σ]`, where `B₀` has a square
presentation over `ℤ[σ]` whose Jacobian determinant is nonzero in `B₀[1/h]`. Two families of maps
`c^p : Ω^p_{Y/ℤ} ⟶ f^*Ω^p_{X/ℤ} ⊗ det(NL_{Y/X})` for `f : Spec B₀[1/h] ⟶ Spec ℤ[σ]` which both
satisfy (0H9C) for `δ(NL_{Y/X})` and (0H9D) are equal. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.GarelMaps.eq_of_niceChart
    [IsDomain (Localization.Away h)]
    (hjac : algebraMap B₀ (Localization.Away h) P₀.relationJacobiMatrix.det ≠ 0)
    [Algebra.QuasiFinite (MvPolynomial σ ℤ) (Localization.Away h)]
    [Algebra.Syntomic (MvPolynomial σ ℤ) (Localization.Away h)]
    {c c' : (hom σ h).GarelMaps ((hom σ h).detNL (syntomic_hom σ h))}
    (hn : c.IsNormalized ((hom σ h).deltaNL (syntomic_hom σ h))) (hm : c.IsMultiplicative)
    (hn' : c'.IsNormalized ((hom σ h).deltaNL (syntomic_hom σ h))) (hm' : c'.IsMultiplicative)
    (p : ℕ) : c p = c' p := by
  have e := top_le_preimage_top σ h
  have : ((hom σ h).twistedPullbackForms ((hom σ h).detNL (syntomic_hom σ h)) p).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineTensorGeneral.isQuasicoherent_tensorMod _ _
  exact Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top fun a =>
    Scheme.Hom.GarelMaps.app_eq_of_isSMulRegular hn hm hn' hm' (isAffineOpen_top _)
      (isAffineOpen_top _) e (jacobian h P₀) (exists_pow_jacobian_smul_mem_range h P₀ e)
      (fun q => isSMulRegular_jacobian h P₀ hjac _ q) p a

end Twisted

end AlgebraicGeometry.NiceChart

end
