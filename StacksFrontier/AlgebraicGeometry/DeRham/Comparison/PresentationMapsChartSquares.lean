module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Existence
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsCharts
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections

/-!
# The maps of Remark 0FL9 on charts over charts of a base change square

Let `b ≫ f = f' ≫ a` be a commutative square of locally quasi-finite syntomic morphisms inducing
an open immersion `Y' ⟶ X' ×_X Y`. Around every point of `Y'` over a presented chart `(U, V)`
of `f` there is a presented chart `(U', V')` of `f'` lying over `(U, V)` on which `Γ(Y', V')` is
a localization of the pushout `Γ(X', U') ⊗_{Γ(X, U)} Γ(Y, V)`; on it the maps of Remark 0FL9
with values in `det(NL)` are compatible with the base change map `detNLSquareMap` of
determinants (Stacks, proof of Lemma 0H9H).

## Main results

* `AlgebraicGeometry.Scheme.Hom.chartOver_of_isPushout_isLocalizationAway`: the ring-level
  input, on a chart which is a localization of a pushout.
* `AlgebraicGeometry.Scheme.Hom.exists_chartOver_presentationDetNLMap`.

## References

* [Stacks Project, Tag 0H9H](https://stacks.math.columbia.edu/tag/0H9H)
* [Stacks Project, Tag 0H9F](https://stacks.math.columbia.edu/tag/0H9F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  (w : b ≫ f = f' ≫ a)

variable (hf : Syntomic f) (hf' : Syntomic f') [LocallyQuasiFinite f']

/-- Sections of a composite `j ≫ p = q` on opens `U`, `Z`, `V` factor through the sections of
`p` and `j`. -/
private theorem appLE_apply_appLE_of_comp_eq {A B C : Scheme.{u}} {j : A ⟶ B} {p : B ⟶ C}
    {q : A ⟶ C} (h : j ≫ p = q) {U : C.Opens} {Z : B.Opens} {V : A.Opens} (hZ : Z ≤ p ⁻¹ᵁ U)
    (hjZ : V ≤ j ⁻¹ᵁ Z) (e : V ≤ q ⁻¹ᵁ U) (x : Γ(C, U)) :
    q.appLE U V e x = j.appLE Z V hjZ (p.appLE U Z hZ x) := by
  subst h
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- The ring-level input of `exists_chartOver_presentationDetNLMap`: a chart `(U', V')` of `f'`
whose ring is a localization `Γ(Z)[1/g]` of the pushout `Γ(Z) = Γ(X', U') ⊗_{Γ(X, U)} Γ(Y, V)`
lies over `(U, V)` in a good square, is presented when `(U, V)` is, and carries the
compatibility of the maps of Remark 0FL9 with `detNLSquareMap`. -/
theorem chartOver_of_isPushout_isLocalizationAway [IsOpenImmersion (pullback.lift b f' w)]
    (c : f.chartIndex.ι) (hc : f.ChartPresented c) (U' : X'.affineOpens)
    (hU : U'.1 ≤ a ⁻¹ᵁ c.1.1.1) (Z : (pullback f a).Opens) (hZV : Z ≤ pullback.fst f a ⁻¹ᵁ c.1.2.1)
    (hZU : Z ≤ pullback.snd f a ⁻¹ᵁ U'.1)
    (hpush : CategoryTheory.IsPushout (f.appLE c.1.1.1 c.1.2.1 c.2) (a.appLE c.1.1.1 U'.1 hU)
      ((pullback.fst f a).appLE c.1.2.1 Z hZV) ((pullback.snd f a).appLE U'.1 Z hZU))
    (g : Γ(pullback f a, Z)) (V' : Y'.affineOpens) (hjZ : V'.1 ≤ pullback.lift b f' w ⁻¹ᵁ Z)
    (e' : V'.1 ≤ f' ⁻¹ᵁ U'.1) (hV : V'.1 ≤ b ⁻¹ᵁ c.1.2.1)
    (hloc : letI := ((pullback.lift b f' w).appLE Z V'.1 hjZ).hom.toAlgebra
      IsLocalization.Away g Γ(Y', V'.1)) :
    ∃ hsq : f.IsGoodChartSquare w c.2 e' hU hV, f'.ChartPresented ⟨(U', V'), e'⟩ ∧
      letI := f.chartAlgebra c.2
      letI := f'.chartAlgebra e'
      letI := a.chartAlgebra hU
      letI := b.chartAlgebra hV
      letI := squareAlgebra f' a hU e'
      haveI := isScalarTower_squareAlgebra_left hU e'
      haveI := f.isScalarTower_squareAlgebra_right w c.2 hU hV e'
      haveI := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
      haveI := f'.syntomic_chartAlgebra hf' U' V' e'
      ∀ {n n' : ℕ} (P : Algebra.Presentation Γ(X, c.1.1.1) Γ(Y, c.1.2.1) (Fin n) (Fin n))
        [P.IsRelativeGlobalCompleteIntersection]
        (P' : Algebra.Presentation Γ(X', U'.1) Γ(Y', V'.1) (Fin n') (Fin n'))
        [P'.IsRelativeGlobalCompleteIntersection] (p : ℕ)
        (η : ⋀[Γ(Y, c.1.2.1)]^p Ω[Γ(Y, c.1.2.1)⁄ℤ]),
        Stacks.DeRham.presentationDetNLMap P' p (ExteriorAlgebra.powMapₛₗ p
            (algebraMap Γ(Y, c.1.2.1) Γ(Y', V'.1)) (Stacks.DeRham.kaehlerMapₛₗ _ _) η) =
          TensorProduct.map (ExteriorAlgebra.powMapₛₗ p
              (algebraMap Γ(Y, c.1.2.1) Γ(Y', V'.1))
              (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1) Γ(Y, c.1.2.1) Γ(X', U'.1)
                Γ(Y', V'.1)))
            (detNLSquareMap w hf hf' c ⟨(U', V'), e'⟩ hU hV hsq)
            (Stacks.DeRham.presentationDetNLMap P p η) := by
  let := f.chartAlgebra c.2
  let := f'.chartAlgebra e'
  let := a.chartAlgebra hU
  let := b.chartAlgebra hV
  let := squareAlgebra f' a hU e'
  have := isScalarTower_squareAlgebra_left hU e'
  have := f.isScalarTower_squareAlgebra_right w c.2 hU hV e'
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f'.syntomic_chartAlgebra hf' U' V' e'
  have := f'.quasiFinite_chartAlgebra inferInstance U' V' e'
  let : Algebra Γ(X', U'.1) Γ(pullback f a, Z) :=
    ((pullback.snd f a).appLE U'.1 Z hZU).hom.toAlgebra
  let : Algebra Γ(Y, c.1.2.1) Γ(pullback f a, Z) :=
    ((pullback.fst f a).appLE c.1.2.1 Z hZV).hom.toAlgebra
  let : Algebra Γ(X, c.1.1.1) Γ(pullback f a, Z) :=
    (f.appLE c.1.1.1 c.1.2.1 c.2 ≫ (pullback.fst f a).appLE c.1.2.1 Z hZV).hom.toAlgebra
  have : IsScalarTower Γ(X, c.1.1.1) Γ(Y, c.1.2.1) Γ(pullback f a, Z) :=
    .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(X, c.1.1.1) Γ(X', U'.1) Γ(pullback f a, Z) :=
    .of_algebraMap_eq fun x => (congrArg (fun φ : Γ(X, c.1.1.1) ⟶ Γ(pullback f a, Z) => φ x)
      hpush.w).trans (CommRingCat.comp_apply _ _ x)
  have : Algebra.IsPushout Γ(X, c.1.1.1) Γ(Y, c.1.2.1) Γ(X', U'.1) Γ(pullback f a, Z) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  let : Algebra Γ(pullback f a, Z) Γ(Y', V'.1) :=
    ((pullback.lift b f' w).appLE Z V'.1 hjZ).hom.toAlgebra
  have : IsScalarTower Γ(X', U'.1) Γ(pullback f a, Z) Γ(Y', V'.1) :=
    .of_algebraMap_eq fun x =>
      appLE_apply_appLE_of_comp_eq (pullback.lift_snd b f' w) _ _ _ x
  have : IsScalarTower Γ(Y, c.1.2.1) Γ(pullback f a, Z) Γ(Y', V'.1) :=
    .of_algebraMap_eq fun x =>
      appLE_apply_appLE_of_comp_eq (pullback.lift_fst b f' w) _ _ _ x
  have := hloc
  obtain ⟨n, P₀, hP₀⟩ := hc
  have hsq : f.IsGoodChartSquare w c.2 e' hU hV :=
    Stacks.DeRham.isGoodSquare_of_isPushout_of_isLocalizationAway
      (C := Γ(pullback f a, Z)) g P₀
  refine ⟨hsq, ⟨1 + n, Stacks.DeRham.localizationPresentation Γ(Y', V'.1) g
    (Stacks.DeRham.pushoutPresentation Γ(X', U'.1) Γ(pullback f a, Z) P₀), inferInstance⟩, ?_⟩
  intro n₁ n₂ P _ P' _ p η
  exact Stacks.DeRham.presentationDetNLMap_naturality_of_isPushout_of_isLocalizationAway
    (C := Γ(pullback f a, Z)) g P hsq P' p η

/-- **Charts over a presented chart along a base change square, and the maps of Remark 0FL9 on
them.** Let `b ≫ f = f' ≫ a` be a commutative square of syntomic morphisms, `f'` locally
quasi-finite, inducing an open immersion of `Y'` into `X' ×_X Y`. For every presented chart
`(U, V)` of `f`, every point `y'` of `Y'` over `V` and every open neighbourhood `W` of `y'` there
is a presented chart `(U', V')` of `f'` lying over `(U, V)` (a good square of charts) with
`y' ∈ V' ⊆ W` on which the maps of Remark 0FL9 with values in `det(NL)`, for any presentations,
commute with the maps on forms and the base change map `detNLSquareMap` of determinants. -/
theorem exists_chartOver_presentationDetNLMap [IsOpenImmersion (pullback.lift b f' w)]
    (c : f.chartIndex.ι) (hc : f.ChartPresented c) {y' : Y'} (hy : y' ∈ b ⁻¹ᵁ c.1.2.1)
    {W : Y'.Opens} (hyW : y' ∈ W) :
    ∃ (c' : f'.chartIndex.ι) (hU : c'.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1) (hV : c'.1.2.1 ≤ b ⁻¹ᵁ c.1.2.1)
      (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV),
      y' ∈ c'.1.2.1 ∧ c'.1.2.1 ≤ W ∧ f'.ChartPresented c' ∧
      letI := f.chartAlgebra c.2
      letI := f'.chartAlgebra c'.2
      letI := a.chartAlgebra hU
      letI := b.chartAlgebra hV
      letI := squareAlgebra f' a hU c'.2
      haveI := isScalarTower_squareAlgebra_left hU c'.2
      haveI := f.isScalarTower_squareAlgebra_right w c.2 hU hV c'.2
      haveI := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
      haveI := f'.syntomic_chartAlgebra hf' c'.1.1 c'.1.2 c'.2
      ∀ {n n' : ℕ} (P : Algebra.Presentation Γ(X, c.1.1.1) Γ(Y, c.1.2.1) (Fin n) (Fin n))
        [P.IsRelativeGlobalCompleteIntersection]
        (P' : Algebra.Presentation Γ(X', c'.1.1.1) Γ(Y', c'.1.2.1) (Fin n') (Fin n'))
        [P'.IsRelativeGlobalCompleteIntersection] (p : ℕ)
        (η : ⋀[Γ(Y, c.1.2.1)]^p Ω[Γ(Y, c.1.2.1)⁄ℤ]),
        Stacks.DeRham.presentationDetNLMap P' p (ExteriorAlgebra.powMapₛₗ p
            (algebraMap Γ(Y, c.1.2.1) Γ(Y', c'.1.2.1)) (Stacks.DeRham.kaehlerMapₛₗ _ _) η) =
          TensorProduct.map (ExteriorAlgebra.powMapₛₗ p
              (algebraMap Γ(Y, c.1.2.1) Γ(Y', c'.1.2.1))
              (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1) Γ(Y, c.1.2.1) Γ(X', c'.1.1.1)
                Γ(Y', c'.1.2.1)))
            (detNLSquareMap w hf hf' c c' hU hV hsq)
            (Stacks.DeRham.presentationDetNLMap P p η) := by
  have h0 := exists_isPushout_isLocalizationAway w c.1.1 c.1.2 c.2 hy hyW
  obtain ⟨U', hU, g, hZ, hpush, hgrange, hyg, hle⟩ := h0
  have hV'aff : IsAffineOpen (pullback.lift b f' w ⁻¹ᵁ (pullback f a).basicOpen g) :=
    (hZ.basicOpen g).preimage_of_isOpenImmersion _ hgrange
  have e' : pullback.lift b f' w ⁻¹ᵁ (pullback f a).basicOpen g ≤ f' ⁻¹ᵁ U'.1 :=
    hle.trans (inf_le_left.trans inf_le_right)
  have hV : pullback.lift b f' w ⁻¹ᵁ (pullback f a).basicOpen g ≤ b ⁻¹ᵁ c.1.2.1 :=
    hle.trans inf_le_right
  have H := chartOver_of_isPushout_isLocalizationAway w hf hf' c hc U' hU _
    inf_le_left inf_le_right hpush g ⟨_, hV'aff⟩
    ((pullback.lift b f' w).preimage_mono ((pullback f a).basicOpen_le g)) e' hV
    (hZ.isLocalization_away_appLE_preimage_basicOpen _ g hgrange)
  refine ⟨⟨(U', ⟨_, hV'aff⟩), e'⟩, hU, hV, H.1, hyg, hle.trans (inf_le_left.trans inf_le_left),
    H.2.1, ?_⟩
  exact H.2.2

end AlgebraicGeometry.Scheme.Hom

end
