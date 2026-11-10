module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ConverseContainmentShrink
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.RingTheory.Flat.ProjectiveOfUniversallyInjectiveBaseChange

/-!
# Projectivity of sections from an étale chart, on an affine open of the base

Let `fU : Y ⟶ T` be a morphism of affine schemes locally of finite presentation, `ℱ_Y` a
quasi-coherent module on `Y` of finite presentation and flat over `T`, `h : Z ⟶ Y` an étale
morphism from an affine scheme such that the direct image of `h^*ℱ_Y` along `h ≫ fU` is locally
projective, and `W` an affine open of `T`. If over every point of `W` the associated points of
the fibre of `ℱ_Y` lie in an open subscheme contained in the image of `h`, then the sections of
`ℱ_Y` on `fU⁻¹W` are projective over `Γ(T, W)`.

## Main results

* `AlgebraicGeometry.exists_isPrime_under_eq_of_fibrewiseContainment`: under the fibrewise
  containment, every relative associated prime of the sections of `ℱ_Y` on `fU⁻¹W` is the
  contraction of a prime of the sections of `Z` on `h⁻¹fU⁻¹W`.
* `AlgebraicGeometry.projective_sections_of_fibrewiseContainment`: the sections of `ℱ_Y` on
  `fU⁻¹W` are projective over `Γ(T, W)`.

## References

* [Stacks Project, Tag 05MD](https://stacks.math.columbia.edu/tag/05MD)
* [Stacks Project, Tag 0CU5](https://stacks.math.columbia.edu/tag/0CU5)
* [Stacks Project, Tag 05DH](https://stacks.math.columbia.edu/tag/05DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Every relative associated prime of the sections of `ℱ` on `fU⁻¹W` is the contraction of a
prime of the chart, as soon as the associated points of each fibre over a point of `W` lie in an
open subscheme `V` contained in the image of the chart. -/
theorem exists_isPrime_under_eq_of_fibrewiseContainment {T Y Z : Scheme.{u}} (fU : Y ⟶ T)
    (FU : Y.Modules) [FU.IsQuasicoherent] (h : Z ⟶ Y) {W : T.Opens} (hW : IsAffineOpen W)
    (hWY : IsAffineOpen (fU ⁻¹ᵁ W)) (hWZ : IsAffineOpen (h ⁻¹ᵁ (fU ⁻¹ᵁ W))) (V : Y.Opens)
    (hVr : (V : Set Y) ⊆ Set.range h.base)
    (hcontain : (W : Set T) ⊆ Stacks.RelativeAssassin.fibrewiseContainment fU FU V) :
    letI : Algebra Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) := (fU.appLE W (fU ⁻¹ᵁ W) le_rfl).hom.toAlgebra
    letI : Module Γ(T, W) Γ(FU, fU ⁻¹ᵁ W) :=
      Module.compHom _ (fU.appLE W (fU ⁻¹ᵁ W) le_rfl).hom
    letI : IsScalarTower Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W) :=
      IsScalarTower.of_compHom Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W)
    letI : Algebra Γ(Y, fU ⁻¹ᵁ W) Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
      (h.appLE (fU ⁻¹ᵁ W) (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) le_rfl).hom.toAlgebra
    ∀ (q : Ideal Γ(Y, fU ⁻¹ᵁ W)) (_ : q.IsPrime),
      IsAssociatedPrimeStacks Γ(Y, fU ⁻¹ᵁ W)
          (Γ(FU, fU ⁻¹ᵁ W) ⊗[Γ(T, W)] (q.under Γ(T, W)).ResidueField) q →
        ∃ q' : Ideal Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)), q'.IsPrime ∧
          q'.under Γ(Y, fU ⁻¹ᵁ W) = q :=
  let : Algebra Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) := (fU.appLE W (fU ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  let : Module Γ(T, W) Γ(FU, fU ⁻¹ᵁ W) :=
    Module.compHom _ (fU.appLE W (fU ⁻¹ᵁ W) le_rfl).hom
  let : IsScalarTower Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W) :=
    IsScalarTower.of_compHom Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W)
  let : Algebra Γ(Y, fU ⁻¹ᵁ W) Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    (h.appLE (fU ⁻¹ᵁ W) (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) le_rfl).hom.toAlgebra
  by
  intro q hq hass
  set y : Y := hWY.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(Y, fU ⁻¹ᵁ W)) with hydef
  have hy : y ∈ (fU ⁻¹ᵁ W : Y.Opens) := hWY.range_fromSpec.le ⟨_, rfl⟩
  have hpq : hWY.primeIdealOf ⟨y, hy⟩ = (⟨q, hq⟩ : PrimeSpectrum Γ(Y, fU ⁻¹ᵁ W)) :=
    hWY.fromSpec.isOpenEmbedding.injective
      ((hWY.fromSpec_primeIdealOf ⟨y, hy⟩).trans hydef)
  have hmem : hWY.primeIdealOf ⟨y, hy⟩ ∈
      Module.relativeAssassin Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W) := by
    rw [hpq]
    exact Module.mem_relativeAssassin_of_isAssociatedPrimeStacks ⟨q, hq⟩ hass
  have hyass : y ∈ Stacks.Divisors.relativeAssassin fU FU :=
    mem_relativeAssassin_of_mem_relativeAssassin_sections fU FU (fU ⁻¹ᵁ W) W hWY hW le_rfl hy hmem
  obtain ⟨t, ξ, hξ, hyeq⟩ := (Stacks.Divisors.mem_relativeAssassin fU FU y).mp hyass
  have ht : t = fU y := by rw [← hyeq]; exact ((fU.range_fiberι t).le ⟨ξ, rfl⟩).symm
  subst ht
  have hyV : y ∈ (V : Set Y) := by
    rw [← hyeq]
    exact hcontain (show fU y ∈ (W : Set T) from hy) hξ
  obtain ⟨z, hz⟩ := hVr hyV
  have hzmem : z ∈ (h ⁻¹ᵁ (fU ⁻¹ᵁ W) : Z.Opens) := by
    change h z ∈ (fU ⁻¹ᵁ W : Y.Opens)
    rw [hz]; exact hy
  refine ⟨(hWZ.primeIdealOf ⟨z, hzmem⟩).asIdeal, (hWZ.primeIdealOf ⟨z, hzmem⟩).isPrime, ?_⟩
  have hle : h ⁻¹ᵁ (fU ⁻¹ᵁ W) ≤ h ⁻¹ᵁ (fU ⁻¹ᵁ W) := le_rfl
  have hkey := IsAffineOpen.comap_primeIdealOf_appLE (f := h) (fU ⁻¹ᵁ W) hWY
    (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) hWZ hle hzmem
  have hsub : (⟨h z, hle hzmem⟩ : (fU ⁻¹ᵁ W : Y.Opens)) = ⟨y, hy⟩ := Subtype.ext hz
  rw [hsub] at hkey
  simpa [Ideal.under, hpq, RingHom.algebraMap_toAlgebra] using
    congrArg PrimeSpectrum.asIdeal hkey

/-- Let `fU : Y ⟶ T` be an affine morphism of
finite presentation between affine schemes, let `ℱ_Y` be quasi-coherent of finite presentation and
flat over `T`, let `h : Z ⟶ Y` be étale with `Z` affine, and let `W` be an affine open of `T`.
If the direct image along `h ≫ fU` of the chart's module is locally projective, and if over every
point of `W` the associated points of the fibre of `ℱ_Y` lie in an open subscheme `V` contained in
the image of `h`, then the sections of `ℱ_Y` on `fU⁻¹W` are projective over `Γ(T, W)`. -/
theorem projective_sections_of_fibrewiseContainment {T Y Z : Scheme.{u}} [IsAffine T] [IsAffine Y]
    [IsAffine Z] (fU : Y ⟶ T) [LocallyOfFinitePresentation fU] (FU : Y.Modules)
    [FU.IsQuasicoherent] [FU.IsFinitePresentation]
    (hflat : IsFlatOver fU.toLRSHom.toShHom FU) (h : Z ⟶ Y) [Etale h] {W : T.Opens}
    (hW : IsAffineOpen W) (V : Y.Opens) (hVr : (V : Set Y) ⊆ Set.range h.base)
    (hcontain : (W : Set T) ⊆ Stacks.RelativeAssassin.fibrewiseContainment fU FU V)
    (hchart : Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward (h ≫ fU)).obj ((Scheme.Modules.pullback h).obj FU))) :
    Module.Projective Γ(T, W) Γ((Scheme.Modules.pushforward fU).obj FU, W) :=
  let : Algebra Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) := (fU.appLE W (fU ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  let : Algebra Γ(Y, fU ⁻¹ᵁ W) Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    (h.appLE (fU ⁻¹ᵁ W) (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) le_rfl).hom.toAlgebra
  let : Algebra Γ(T, W) Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    ((h ≫ fU).appLE W (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) le_rfl).hom.toAlgebra
  let : IsScalarTower Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((h ≫ fU).appLE W (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) le_rfl).hom = _
      rw [← Scheme.Hom.appLE_comp_appLE]
      rfl)
  let : Module Γ(T, W) Γ(FU, fU ⁻¹ᵁ W) :=
    Module.compHom _ (fU.appLE W (fU ⁻¹ᵁ W) le_rfl).hom
  let : IsScalarTower Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W) :=
    IsScalarTower.of_compHom Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W)
  let : Module Γ(T, W) Γ((Scheme.Modules.pullback h).obj FU, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    Module.compHom _ ((h ≫ fU).appLE W (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) le_rfl).hom
  let : IsScalarTower Γ(T, W) Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W))
      Γ((Scheme.Modules.pullback h).obj FU, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    IsScalarTower.of_compHom _ _ _
  by
  have hWY : IsAffineOpen (fU ⁻¹ᵁ W) := hW.preimage fU
  have hWZ : IsAffineOpen (h ⁻¹ᵁ (fU ⁻¹ᵁ W)) := hWY.preimage h
  have hGqc : ((Scheme.Modules.pullback h).obj FU).IsQuasicoherent :=
    isQuasicoherent_pullback_obj h FU
  have hfpS : Algebra.FinitePresentation Γ(T, W) Γ(Y, fU ⁻¹ᵁ W) :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := fU) inferInstance
      ⟨W, hW⟩ ⟨fU ⁻¹ᵁ W, hWY⟩ le_rfl
  have hflatS' : Module.Flat Γ(Y, fU ⁻¹ᵁ W) Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    HasRingHomProperty.appLE (P := @Flat) (f := h) inferInstance
      ⟨fU ⁻¹ᵁ W, hWY⟩ ⟨h ⁻¹ᵁ (fU ⁻¹ᵁ W), hWZ⟩ le_rfl
  have hfpN : Module.FinitePresentation Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W) :=
    finitePresentation_sections_on_affine FU ⟨fU ⁻¹ᵁ W, hWY⟩
  have hout := (isFlatOver_tfae fU FU).out 1 2
  have hflatN : Module.Flat Γ(T, W) Γ(FU, fU ⁻¹ᵁ W) := hout.mp hflat _ hWY _ hW le_rfl
  have hPchart : Module.Projective Γ(T, W)
      Γ((Scheme.Modules.pullback h).obj FU, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    (projective_sections_appLE_iff_app (h ≫ fU) _ W).2
      ((projective_pushforward_sections_iff (h ≫ fU) _ W).1 (hchart W hW))
  have ebc : (Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) ⊗[Γ(Y, fU ⁻¹ᵁ W)] Γ(FU, fU ⁻¹ᵁ W)) ≃ₗ[Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W))]
      Γ((Scheme.Modules.pullback h).obj FU, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) :=
    (affinePullbackSectionsBaseChangeIso h FU hWY hWZ le_rfl).toLinearEquiv
  have hPflip : Module.Projective Γ(T, W)
      (Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W)) ⊗[Γ(Y, fU ⁻¹ᵁ W)] Γ(FU, fU ⁻¹ᵁ W)) :=
    Module.Projective.of_equiv' (ebc.restrictScalars Γ(T, W)).symm
  have hPtensor : Module.Projective Γ(T, W)
      (Γ(FU, fU ⁻¹ᵁ W) ⊗[Γ(Y, fU ⁻¹ᵁ W)] Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W))) :=
    Module.Projective.of_equiv'
      ((TensorProduct.comm Γ(Y, fU ⁻¹ᵁ W) Γ(FU, fU ⁻¹ᵁ W)
        Γ(Z, h ⁻¹ᵁ (fU ⁻¹ᵁ W))).restrictScalars Γ(T, W)).symm
  have hPN : Module.Projective Γ(T, W) Γ(FU, fU ⁻¹ᵁ W) :=
    Stacks.UniversalInjectivity.projective_of_baseChange_of_flat
      (exists_isPrime_under_eq_of_fibrewiseContainment fU FU h hW hWY hWZ V hVr hcontain)
  exact (projective_pushforward_sections_iff fU FU W).2
    ((projective_sections_appLE_iff_app fU FU W).1 hPN)

end AlgebraicGeometry

end
