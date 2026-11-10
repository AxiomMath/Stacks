module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsBaseChange
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.BaseChange
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.GoodChart
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Sheaf

/-!
# The maps of Remark 0FL9 on the charts of a morphism

Let `f : Y ⟶ X` be a locally quasi-finite syntomic morphism. On a chart `(U, V)` of `f` (affine
opens with `f(V) ⊆ U`) on which `Γ(Y, V)` has a square relative global complete intersection
presentation over `Γ(X, U)`, the maps of Remark 0FL9 with values in `det(NL_{Γ(V)/Γ(U)})`
(`Stacks.DeRham.presentationDetNLMap`) do not depend on the presentation
(`Stacks.DeRham.presentationDetNLMap_eq`). This file proves that they are compatible with the
restriction maps `Scheme.Hom.detNLChartRestrict` of `det(NL)` along refinements of charts
(`Scheme.Hom.presentationDetNLMap_detNLChartRestrict`).

## References

* [Stacks Project, Tag 0FL9](https://stacks.math.columbia.edu/tag/0FL9)
* [Stacks Project, Tag 0H9F](https://stacks.math.columbia.edu/tag/0H9F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Syntomic f) [LocallyQuasiFinite f]

/-- **The maps of Remark 0FL9 are compatible with the restriction of charts**: for a refinement
`(U', V')` of a chart `(U, V)` of `f` (basic opens) and any square relative global complete
intersection presentations `P` of `Γ(Y, V)` over `Γ(X, U)` and `P'` of `Γ(Y, V')` over
`Γ(X, U')`, the maps of Remark 0FL9 with values in `det(NL)` commute with the restriction maps on
forms and the restriction map `detNLChartRestrict` of `det(NL)`. -/
theorem presentationDetNLMap_detNLChartRestrict {c' c : f.chartIndex.ι}
    (h : f.chartIndex.Refines c' c) {n n' : ℕ} :
    letI := f.chartAlgebra c.2
    letI := f.chartAlgebra c'.2
    letI := X.restrictAlgebra h.1.le
    letI := Y.restrictAlgebra h.2.le
    letI := f.chartAlgebra (h.2.le.trans c.2)
    haveI := f.isScalarTower_chartAlgebra_restrict c.2 c'.2 h.1.le h.2.le
    haveI := f.isScalarTower_restrict_chartAlgebra c.2 h.2.le
    haveI := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
    haveI := f.syntomic_chartAlgebra hf c'.1.1 c'.1.2 c'.2
    ∀ (P : Algebra.Presentation Γ(X, c.1.1.1) Γ(Y, c.1.2.1) (Fin n) (Fin n))
      [P.IsRelativeGlobalCompleteIntersection]
      (P' : Algebra.Presentation Γ(X, c'.1.1.1) Γ(Y, c'.1.2.1) (Fin n') (Fin n'))
      [P'.IsRelativeGlobalCompleteIntersection] (p : ℕ) (η : ⋀[Γ(Y, c.1.2.1)]^p Ω[Γ(Y, c.1.2.1)⁄ℤ]),
      Stacks.DeRham.presentationDetNLMap P' p (ExteriorAlgebra.powMapₛₗ p
          (algebraMap Γ(Y, c.1.2.1) Γ(Y, c'.1.2.1)) (Stacks.DeRham.kaehlerMapₛₗ _ _) η) =
        TensorProduct.map (ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, c.1.2.1) Γ(Y, c'.1.2.1))
            (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1) Γ(Y, c.1.2.1) Γ(X, c'.1.1.1)
              Γ(Y, c'.1.2.1)))
          (f.detNLChartRestrict hf h) (Stacks.DeRham.presentationDetNLMap P p η) := by
  let := f.chartAlgebra c.2
  let := f.chartAlgebra c'.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := f.chartAlgebra (h.2.le.trans c.2)
  have := f.isScalarTower_chartAlgebra_restrict c.2 c'.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.2 h.2.le
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f.syntomic_chartAlgebra hf c'.1.1 c'.1.2 c'.2
  have := f.quasiFinite_chartAlgebra inferInstance c'.1.1 c'.1.2 c'.2
  intro P _ P' _ p η
  have : IsLocalization.Away h.1.choose Γ(X, c'.1.1.1) :=
    c.1.1.2.isLocalization_of_eq_basicOpen h.1.choose (homOfLE _) h.1.choose_spec
  have : IsLocalization.Away h.2.choose Γ(Y, c'.1.2.1) :=
    c.1.2.2.isLocalization_of_eq_basicOpen h.2.choose (homOfLE _) h.2.choose_spec
  exact Stacks.DeRham.presentationDetNLMap_naturality_of_isLocalizationAway_of_isLocalizationAway
    h.1.choose h.2.choose P _ P' p η

/-! ### Charts over charts of a base change square -/

section Square

variable {X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  (w : b ≫ f = f' ≫ a)

/-- **Charts of `f'` over a chart of `f`, as localizations of pushouts.** Let `b ≫ f = f' ≫ a` be
a commutative square whose comparison map `j : Y' ⟶ X' ×_X Y` is an open immersion. For every
chart `(U, V)` of `f`, every point `y'` of `Y'` over `V` and every open neighbourhood `W` of `y'`,
there are an affine open `U' ⊆ a⁻¹U`, the affine open `Z = pr₁⁻¹V ∩ pr₂⁻¹U'` of `X' ×_X Y`
(whose ring is the pushout `Γ(X', U') ⊗_{Γ(X, U)} Γ(Y, V)`) and `g ∈ Γ(Z)` with `D(g)` in the
range of `j`, such that `V' = j⁻¹D(g)` contains `y'` and lies in `W`. -/
theorem exists_isPushout_isLocalizationAway [IsOpenImmersion (pullback.lift b f' w)]
    (U : X.affineOpens) (V : Y.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) {y' : Y'}
    (hy : y' ∈ b ⁻¹ᵁ V.1) {W : Y'.Opens} (hyW : y' ∈ W) :
    ∃ (U' : X'.affineOpens) (hU : U'.1 ≤ a ⁻¹ᵁ U.1) (g : Γ(pullback f a,
        pullback.fst f a ⁻¹ᵁ V.1 ⊓ pullback.snd f a ⁻¹ᵁ U'.1)),
      IsAffineOpen (pullback.fst f a ⁻¹ᵁ V.1 ⊓ pullback.snd f a ⁻¹ᵁ U'.1) ∧
      CategoryTheory.IsPushout (f.appLE U.1 V.1 e) (a.appLE U.1 U'.1 hU)
        ((pullback.fst f a).appLE V.1 _ inf_le_left)
        ((pullback.snd f a).appLE U'.1 _ inf_le_right) ∧
      (pullback f a).basicOpen g ≤ (pullback.lift b f' w).opensRange ∧
      y' ∈ pullback.lift b f' w ⁻¹ᵁ (pullback f a).basicOpen g ∧
      pullback.lift b f' w ⁻¹ᵁ (pullback f a).basicOpen g ≤ W ⊓ f' ⁻¹ᵁ U'.1 ⊓ b ⁻¹ᵁ V.1 := by
  set j := pullback.lift b f' w with hj
  have hfy : f' y' ∈ a ⁻¹ᵁ U.1 := by
    change a (f' y') ∈ U.1
    rw [← Scheme.Hom.comp_apply, ← w, Scheme.Hom.comp_apply]
    exact e hy
  obtain ⟨_, ⟨U', hU'aff, rfl⟩, hyU', hU'le⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hfy (a ⁻¹ᵁ U.1).isOpen
  replace hU'le : U' ≤ a ⁻¹ᵁ U.1 := hU'le
  have H := IsPullback.of_hasPullback f a
  let Z : (pullback f a).Opens := pullback.fst f a ⁻¹ᵁ V.1 ⊓ pullback.snd f a ⁻¹ᵁ U'
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine _ := hU'aff
  have hZ : IsAffineOpen Z := IsAffine.of_isPullback (Scheme.Hom.isPullback_resLE H hU'le e rfl)
  have hpush := (isIso_pushoutSection_iff H hU'le e (UY := Z) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hU'le e rfl U.2 hU'aff V.2)
  have hjy : j y' ∈ Z := by
    refine ⟨?_, ?_⟩
    · change (pullback.fst f a) (j y') ∈ V.1
      rw [← Scheme.Hom.comp_apply, hj, pullback.lift_fst]
      exact hy
    · change (pullback.snd f a) (j y') ∈ U'
      rw [← Scheme.Hom.comp_apply, hj, pullback.lift_snd]
      exact hyU'
  let O : (pullback f a).Opens := j ''ᵁ (W ⊓ f' ⁻¹ᵁ U' ⊓ b ⁻¹ᵁ V.1)
  have hjyO : j y' ∈ O := ⟨y', ⟨⟨hyW, hyU'⟩, hy⟩, rfl⟩
  obtain ⟨g, hgO, hjg⟩ := hZ.exists_basicOpen_le ⟨j y', hjyO⟩ hjy
  have hgrange : (pullback f a).basicOpen g ≤ j.opensRange := hgO.trans (j.image_le_opensRange _)
  have hV'O : j ⁻¹ᵁ (pullback f a).basicOpen g ≤ W ⊓ f' ⁻¹ᵁ U' ⊓ b ⁻¹ᵁ V.1 := by
    have := j.preimage_mono hgO
    rwa [j.preimage_image_eq] at this
  exact ⟨⟨U', hU'aff⟩, hU'le, g, hZ, hpush, hgrange, hjg, hV'O⟩

end Square

end AlgebraicGeometry.Scheme.Hom

end
