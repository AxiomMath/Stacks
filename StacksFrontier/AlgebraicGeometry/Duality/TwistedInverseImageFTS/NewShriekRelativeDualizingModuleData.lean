module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekAffineChartsNormalization
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens

/-!
# `H⁰(f_new^! 𝒪_Y)` is the relative dualizing module, for `f` not necessarily separated

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes of
finite type over `S`, and `ω_X^•`, `ω_Y^•` normalized relative to `ω_S^•`. On an affine open
`V ⊆ f⁻¹U` of `X`, with `U ⊆ Y` affine, the normalization `ω_X^•|_V ≅ (V → Y)^! ω_Y^•` attached to
`U` identifies `H⁰(f_new^! 𝒪_Y)|_V` with the module `M|_V` of a factorization `V → T → Y`; these
identifications restrict to smaller affine opens and do not depend on `U`. They glue to the chart
data of the relative dualizing module `ω_{X/Y}` of [Stacks, Tag 0BVG] on `H⁰(f_new^! 𝒪_Y)`: the
second assertion of [Stacks, Tag 0BUL], for any choice of compactifications.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.newShriekRelativeDualizingModuleData`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.restrictIso_affineIsoOfIso_chart`.

## References

* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh plusCoh_le_qcoh plusCoh_iff
  pull stdMonoidal stdSymmetric stdMonoidalClosed)

namespace NormalizedOnOpens

/-- Restricting `ε ≫ μ` through `G`, against a transitivity `hG` and a restriction `hR`. -/
theorem restrictIso_chart_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {a b e d : 𝒟} {c₀ c₁ c₂ : 𝒞} (X₁ : a ≅ b) (X₂ : b ≅ G.obj c₀) (ρ : c₀ ≅ c₁) (μ : c₁ ≅ c₂)
    (Z : G.obj c₂ ≅ d) (T : G.obj c₁ ≅ e) (μ' : e ≅ d) (ρW : a ≅ e)
    (hR : G.mapIso μ ≪≫ Z = T ≪≫ μ') (hG : X₁ ≪≫ X₂ ≪≫ G.mapIso ρ ≪≫ T = ρW) :
    X₁ ≪≫ X₂ ≪≫ G.mapIso (ρ ≪≫ μ) ≪≫ Z = ρW ≪≫ μ' := by
  rw [← hG, Functor.mapIso_trans, Iso.trans_assoc, hR]
  simp only [Iso.trans_assoc]

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
  [LocallyQuasiFinite f]

omit [LocallyQuasiFinite f] in
/-- **The restriction step of [Stacks, Tag 0BUL], second assertion**. -/
theorem restrictIso_affineIsoOfIso_chart (U : Y.affineOpens) {V W : X.affineOpens} (hWV : W.1 ≤ V.1)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hWU : W.1 ≤ f ⁻¹ᵁ U.1) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)),
      @Stacks.Discriminant.OpenChart.restrictIso X F.space V.1 F.immersion
          F.isOpenImmersion_immersion (finiteZeroTwisted F) _
          (affineIsoOfIso c 𝒦X 𝒦Y hpe hωS V (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU) F)
          W.1 hWV =
        affineIsoOfIso c 𝒦X 𝒦Y hpe hωS W (affineChartNormalization c 𝒦X 𝒦Y hpe U W hWU)
          (restrictFactorization (hp := hp) (hq := hq) hpe hWV F) := by
  have := hq.source_noetherian
  intro F
  have hVeq := affineIsoOfIso_eq c 𝒦X 𝒦Y hpe hωS V (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU) F
  have hWeq := affineIsoOfIso_eq c 𝒦X 𝒦Y hpe hωS W (affineChartNormalization c 𝒦X 𝒦Y hpe U W hWU)
    (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
      (affineRestrictHom_comp hpe hWV))
  have R := restrict_upperShriekStructureSheafZerothIsoOfIso_trans'
    (affineRestrictHom (hp := hp) (hq := hq) hpe hWV) F (affineRestrictHom_comp hpe hWV)
    (isDualizing_stdComplex c hωS 𝒦Y)
    (isBoundedBelow_dualizingQCoh (hp := hp) c 𝒦Y hωS) (stdComplexRestrictLEIso c 𝒦X hWV)
    (affineNormalizationAt c 𝒦X 𝒦Y hpe hωS V (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU) F)
    (affineNormalizationAt c 𝒦X 𝒦Y hpe hωS W (affineChartNormalization c 𝒦X 𝒦Y hpe U W hWU)
      _)
    (affineNormalizationAt_chart_restrict c 𝒦X 𝒦Y hpe hωS U hWV hVU hWU F)
  have G := newShriekStructureSheafZerothRestrictIso_trans (c := c) (f := f) (𝒦X := 𝒦X)
    (𝒦Y := 𝒦Y) hWV
  refine (congrArg (fun ε => @Stacks.Discriminant.OpenChart.restrictIso X F.space V.1 F.immersion
    F.isOpenImmersion_immersion (finiteZeroTwisted F) _ ε W.1 hWV) hVeq).trans
    ((restrictIso_chart_chase (Scheme.Modules.restrictFunctor (X.homOfLE hWV)) _ _ _ _ _ _ _ _
      R G).trans hWeq.symm)


/-- On the charts inside `W ⊆ V` with `V ⊆ f⁻¹U`, the chart data on `V` and on `W` relative to
`U` give the same identifications. -/
theorem localEquiv_affineChartData_restrict (U : Y.affineOpens) {V W : X.affineOpens}
    (hWV : W.1 ≤ V.1) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hWU : W.1 ≤ f ⁻¹ᵁ U.1)
    (T'V : V.1.toScheme.affineOpens) (hV : V.1.ι ⁻¹ᵁ W.1 = T'V.1) (T'W : W.1.toScheme.affineOpens)
    (hWT : W.1.ι ⁻¹ᵁ W.1 = T'W.1) :
    haveI := hp.source_noetherian
    haveI := hq.source_noetherian
    letI : Algebra Γ(Y, U.1) Γ(X, W.1) := (f.appLE U W hWU).hom.toAlgebra
    ∀ G : Stacks.Discriminant.FiniteOpenFactorization.{u, u, u} Γ(Y, U.1) Γ(X, W.1),
      Stacks.Discriminant.OpenChart.localEquiv f V.1 (affineChartData c 𝒦X 𝒦Y hpe hωS U V hVU)
          (Iso.refl _) U W hWU hWV T'V hV G =
        Stacks.Discriminant.OpenChart.localEquiv f W.1 (affineChartData c 𝒦X 𝒦Y hpe hωS U W hWU)
          (Iso.refl _) U W hWU le_rfl T'W hWT G := by
  have := hp.source_noetherian
  have := hq.source_noetherian
  intro G
  have : @IsOpenImmersion V.1.toScheme _
      (affineFactorization (hp := hp) (hq := hq) hpe V).immersion :=
    (affineFactorization (hp := hp) (hq := hq) hpe V).isOpenImmersion_immersion
  have : @IsFinite _ Y (affineFactorization (hp := hp) (hq := hq) hpe V).toBase :=
    (affineFactorization (hp := hp) (hq := hq) hpe V).isFinite_toBase
  refine (Stacks.Discriminant.OpenChart.localEquiv_ofFiniteTrace_restrictIso f _ _ _ _ _ hWV
    U W hWU le_rfl T'V hV T'W hWT G).trans ?_
  rw [restrictIso_affineIsoOfIso_chart c 𝒦X 𝒦Y hpe hωS U hWV hVU hWU
    (affineFactorization (hp := hp) (hq := hq) hpe V)]
  refine Stacks.Discriminant.OpenChart.localEquiv_congr f W.1 _ _ _ _ U W hWU le_rfl T'W hWT
    (fun F' x => ?_) G
  have : LocallyQuasiFinite
      (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2)).left :=
    inferInstanceAs (LocallyQuasiFinite (W.1.ι ≫ f))
  exact OpenFiniteFactorization.localEquiv_ofFiniteTrace_trans_eq
    (restrictFactorization (hp := hp) (hq := hq) hpe hWV
      (affineFactorization (hp := hp) (hq := hq) hpe V))
    (affineFactorization (hp := hp) (hq := hq) hpe W)
    (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2))
    (newShriekStructureSheafZerothRestrictIso c f 𝒦X 𝒦Y W.1 ≪≫
      upperShriekStructureSheafZerothIsoOfIso
        (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2))
        (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2))
        (isDualizing_stdComplex c hωS 𝒦Y)
        (normalizationStdIso c hωS (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2)
          (𝒦X.restrict W.1) 𝒦Y (affineChartNormalization c 𝒦X 𝒦Y hpe U W hWU)))
    U T'W _ F' _

/-- The chart `V ∩ V = V` of the open subscheme `V`. -/
def affineChart (V : X.affineOpens) : V.1.toScheme.affineOpens :=
  ⟨V.1.ι ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion V.1.ι (by rw [Scheme.Opens.opensRange_ι])⟩

/-- **[Stacks, Tag 0BUL], second assertion.** Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes of finite type over `S`, not necessarily separated, and `ω_X^•`, `ω_Y^•` normalized
relative to `ω_S^•`. Then `H⁰(f_new^! 𝒪_Y)` carries the chart data of the relative dualizing module
`ω_{X/Y}` of Tag 0BVG. -/
def newShriekRelativeDualizingModuleData :
    haveI := hp.source_noetherian
    haveI := hq.source_noetherian
    Stacks.Discriminant.RelativeDualizingModuleData f :=
  haveI := hp.source_noetherian
  haveI := hq.source_noetherian
  { sheaf := newShriekStructureSheafZeroth c f 𝒦X 𝒦Y
    isQuasicoherent := AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen _
      fun V hV => (affineData c 𝒦X 𝒦Y hpe hωS ⟨V, hV⟩).isQuasicoherent
    isCoherent :=
      Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_of_forall_isAffineOpen_restrict _
      fun V hV _ => (affineData c 𝒦X 𝒦Y hpe hωS ⟨V, hV⟩).isCoherent
    factorization U V hVU := by
      let : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U V hVU).hom.toAlgebra
      let : Algebra Γ(Y, U.1) Γ(V.1, (affineChart V).1) :=
        ((V.1.ι ≫ f).appLE U (affineChart V)
          (Stacks.Discriminant.OpenChart.preimage_le f hVU rfl)).hom.toAlgebra
      obtain ⟨F⟩ := (affineData c 𝒦X 𝒦Y hpe hωS V).factorization U (affineChart V)
        (Stacks.Discriminant.OpenChart.preimage_le f hVU rfl)
      let : Algebra Γ(Y, U.1) Γ(V.1, V.1.ι ⁻¹ᵁ V.1) :=
        ((V.1.ι ≫ f).appLE U (affineChart V)
          (Stacks.Discriminant.OpenChart.preimage_le f hVU rfl)).hom.toAlgebra
      exact ⟨Stacks.Discriminant.dualizingModule.retargetFactorization F
        (Stacks.Discriminant.OpenChart.ringEquiv f U.1 hVU le_rfl rfl).symm⟩
    localEquiv U V hVU F := Stacks.Discriminant.OpenChart.localEquiv f V.1
      (affineChartData c 𝒦X 𝒦Y hpe hωS U V hVU) (Iso.refl _) U V hVU le_rfl (affineChart V) rfl F
    localEquiv_natural U V hVU := Stacks.Discriminant.OpenChart.localEquiv_natural f V.1
      (affineChartData c 𝒦X 𝒦Y hpe hωS U V hVU) (Iso.refl _) U V hVU le_rfl (affineChart V) rfl
    localEquiv_baseBasicOpen U V hVU a hVa := by
      intro Ua
      unfold affineChartData affineChartNormalization
      rw [chartIso_eq_of_le hpe 𝒦X 𝒦Y (hp.isShriekable_of_isAffineOpen V.2) (Y.basicOpen_le a)
        (hq.isShriekable_of_isAffineOpen U.2) (hq.isShriekable_of_isAffineOpen Ua.2) hVa hVU]
      exact Stacks.Discriminant.OpenChart.localEquiv_baseBasicOpen f V.1
        (affineChartData c 𝒦X 𝒦Y hpe hωS U V hVU) (Iso.refl _) U V hVU a hVa le_rfl (affineChart V)
        rfl
    localEquiv_basicOpen U V hVU g := by
      intro W hWU F G
      obtain ⟨r, hr, h1, h2⟩ := Stacks.Discriminant.OpenChart.localEquiv_basicOpen f V.1
        (affineChartData c 𝒦X 𝒦Y hpe hωS U V hVU) (Iso.refl _) U V hVU g le_rfl (affineChart V) rfl
        F G
      refine ⟨r, hr, fun s => Eq.trans ?_ (h1 s), h2⟩
      exact (DFunLike.congr_fun (localEquiv_affineChartData_restrict c 𝒦X 𝒦Y hpe hωS U
        (X.basicOpen_le g) hVU hWU _ _ (affineChart W) rfl G) _).symm }

end NormalizedOnOpens

end Stacks.Duality

end
