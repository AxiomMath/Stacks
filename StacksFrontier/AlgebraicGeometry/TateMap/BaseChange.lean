module

public import StacksFrontier.AlgebraicGeometry.TateMap.Construction
public import StacksFrontier.RingTheory.TateMap.ClaimFinal
public import StacksFrontier.AlgebraicGeometry.TateMap.Basic

/-!
# Clause (2) of Stacks 0FKD on affine charts

The Tate map is compatible with every morphism of the category of Section 0FKB, read on
compatible affine charts: the base change of its value on a chart of `Y` is its value on the
corresponding chart of `Y'`.

## Main results

* `Stacks.TateMap.pullbackTate_pullbackTate_eq_of_classified`: if the restrictions of two Tate
  values to principal localizations are pulled back from universal basic charts, the base change of
  the first and the second have the same restriction.
* `AlgebraicGeometry.TateMap.tateIso_baseChange_local`: clause (2) holds after restriction to a
  classified principal open `D(b')` of `V'` lying over a classified principal open of `V`.
* `AlgebraicGeometry.TateMap.span_classified_eq_top`: these principal opens `D(b')` generate the
  unit ideal of `Γ(Y', V')`.
* `AlgebraicGeometry.TateMap.tateIso_baseChange`: clause (2) for the Tate maps on affine charts.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Discriminant Stacks.TateMap
open scoped TensorProduct

universe u

namespace Stacks.TateMap

/-- Let `D` go from `A → B` to `A' → B'`, let `B₀` be a principal localization of `B` and `B''` one
of `B'`, with `D₃` from `A → B₀` to `A' → B''`. If the restriction of `cv` to `B₀` and the
restriction of `cv'` to `B''` are both pulled back from universal basic charts, then the base
change of `cv` and `cv'` have the same restriction to `B''`. -/
theorem pullbackTate_pullbackTate_eq_of_classified {A B B₀ A' B' B'' : Type u} [CommRing A]
    [CommRing B] [CommRing B₀] [CommRing A'] [CommRing B'] [CommRing B''] [Algebra A B]
    [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra B B₀] [Algebra A B₀] [Algebra B' B'']
    [Algebra A' B''] [Algebra B₀ B''] [Algebra B B''] [IsScalarTower B B' B'']
    [IsScalarTower B B₀ B''] [IsNoetherianRing A] [IsNoetherianRing A']
    [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A B₀]
    [Algebra.Syntomic A' B''] [Algebra.QuasiFinite A' B''] [IsNoetherianRing B'']
    (D : ChartBaseChange A B A' B') (D₁ : ChartBaseChange A B A B₀)
    (D₂ : ChartBaseChange A' B' A' B'') (D₃ : ChartBaseChange A B₀ A' B'')
    {F : FiniteOpenFactorization.{u, u, u} A B} (cv : detNL A B ≃ₗ[B] dualizingModule F)
    {G : FiniteOpenFactorization.{u, u, u} A' B'} (cv' : detNL A' B' ≃ₗ[B'] dualizingModule G)
    (G₀ : FiniteOpenFactorization.{u, u, u} A B₀) (G'' : FiniteOpenFactorization.{u, u, u} A' B'')
    {n d : ℕ} [NeZero d] (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
    (instR : Algebra (univBase.{u} n d) A) (instC : Algebra (univChart n d k) B₀)
    (Dκ : ChartBaseChange (univBase.{u} n d) (univChart n d k) A B₀)
    {n' d' : ℕ} [NeZero d'] (k' : MvPolynomial (Fin n') (univBase.{u} n' d'))
    [Algebra.QuasiFinite (univBase.{u} n' d') (univChart n' d' k')]
    (instR' : Algebra (univBase.{u} n' d') A') (instC' : Algebra (univChart n' d' k') B'')
    (Dκ' : ChartBaseChange (univBase.{u} n' d') (univChart n' d' k') A' B'')
    (hcv : pullbackTate D₁ cv G₀ = tateOf k instR instC Dκ G₀)
    (hcv' : pullbackTate D₂ cv' G'' = tateOf k' instR' instC' Dκ' G'') :
    pullbackTate D₂ (pullbackTate D cv G) G'' = pullbackTate D₂ cv' G'' := by
  rw [pullbackTate_square D D₁ D₂ D₃ cv G G₀ G'', hcv, hcv']
  let iR : Algebra (univBase.{u} n d) A' :=
    ((algebraMap A A').comp (@algebraMap _ _ _ _ instR)).toAlgebra
  let iC : Algebra (univChart n d k) B'' :=
    ((algebraMap B₀ B'').comp (@algebraMap _ _ _ _ instC)).toAlgebra
  have : @IsScalarTower (univBase.{u} n d) A A' instR.toSMul Algebra.toSMul iR.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : @IsScalarTower (univChart n d k) B₀ B'' instC.toSMul Algebra.toSMul iC.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [tateOf_pullbackTate k instR instC Dκ D₃ (D₃.comp Dκ) G₀ G'']
  exact tateOf_eq_tateOf k _ _ _ k' instR' instC' Dκ' G''

end Stacks.TateMap

namespace AlgebraicGeometry.TateMap

/-- If `f ≫ g = h` for ring maps `A → B → C`, `A → C`, the induced algebras form a scalar tower. -/
private theorem isScalarTower_of_comp_eq {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (e : f ≫ g = h) :
    @IsScalarTower A B C f.hom.toAlgebra.toSMul g.hom.toAlgebra.toSMul h.hom.toAlgebra.toSMul := by
  subst e
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := (f ≫ g).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' rfl

variable {X Y X' Y' : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian X']
  (f : Y ⟶ X) (f' : Y' ⟶ X') (hf : IsQuasiFiniteSyntomic f) (hf' : IsQuasiFiniteSyntomic f')
  (sq : OpenBaseChangeSquare f f')

/-- On a principal open `D(b')` of `V'` lying over a classified principal open `D(b)` of `V`, and
itself classified, the two sides of clause (2) for the Tate maps have the same restriction. -/
theorem tateIso_baseChange_local (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens)
    (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1)
    (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1) (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) (b : Γ(Y, V.1))
    (b' : Γ(Y', V'.1)) (hbb' : Y'.basicOpen b' ≤ sq.cover ⁻¹ᵁ Y.basicOpen b)
    {n d : ℕ} [NeZero d] (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
    (instR : Algebra (univBase.{u} n d) Γ(X, U.1))
    (instC : Algebra (univChart n d k) Γ(Y, Y.basicOpen b))
    (Dκ : letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
        (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
      @ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X, U.1) Γ(Y, Y.basicOpen b) _ _ _ _
        _ instR _ instC)
    {n' d' : ℕ} [NeZero d'] (k' : MvPolynomial (Fin n') (univBase.{u} n' d'))
    [Algebra.QuasiFinite (univBase.{u} n' d') (univChart n' d' k')]
    (instR' : Algebra (univBase.{u} n' d') Γ(X', U'.1))
    (instC' : Algebra (univChart n' d' k') Γ(Y', Y'.basicOpen b'))
    (Dκ' : letI : Algebra Γ(X', U'.1) Γ(Y', Y'.basicOpen b') :=
        (f'.appLE U' (Y'.basicOpen b') ((Y'.basicOpen_le b').trans hV'U')).hom.toAlgebra
      @ChartBaseChange (univBase.{u} n' d') (univChart n' d' k') Γ(X', U'.1) Γ(Y', Y'.basicOpen b')
        _ _ _ _ _ instR' _ instC') :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', Y'.basicOpen b') :=
      (f'.appLE U' (Y'.basicOpen b') ((Y'.basicOpen_le b').trans hV'U')).hom.toAlgebra
    letI : Algebra Γ(Y', V'.1) Γ(Y', Y'.basicOpen b') :=
      (Y'.presheaf.map (homOfLE (Y'.basicOpen_le b')).op).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf'.2 U' V' hV'U'
    haveI := algebra_syntomic_appLE hf'.2 U' ⟨Y'.basicOpen b', V'.2.basicOpen b'⟩
      ((Y'.basicOpen_le b').trans hV'U')
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (D₂ : ChartBaseChange Γ(X', U'.1) Γ(Y', V'.1) Γ(X', U'.1) Γ(Y', Y'.basicOpen b'))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1))
      (G'' : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', Y'.basicOpen b')),
      pullbackTate D₂ (pullbackTate D (chartValue (tateIso f hf) U V hVU F) G) G'' =
        pullbackTate D₂ (chartValue (tateIso f' hf') U' V' hV'U' G) G'' := by
  intro D D₂ F G G''
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', Y'.basicOpen b') :=
    (f'.appLE U' (Y'.basicOpen b') ((Y'.basicOpen_le b').trans hV'U')).hom.toAlgebra
  let : Algebra Γ(Y', V'.1) Γ(Y', Y'.basicOpen b') :=
    (Y'.presheaf.map (homOfLE (Y'.basicOpen_le b')).op).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := algebra_syntomic_appLE hf'.2 U' V' hV'U'
  have := algebra_syntomic_appLE hf'.2 U' ⟨Y'.basicOpen b', V'.2.basicOpen b'⟩
    ((Y'.basicOpen_le b').trans hV'U')
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  have : IsScalarTower Γ(X', U'.1) Γ(Y', V'.1) Γ(Y', Y'.basicOpen b') :=
    isScalarTower_of_comp_eq _ _ _ (Scheme.Hom.appLE_map _ _ _)
  have : IsLocalization.Away b' Γ(Y', Y'.basicOpen b') := V'.2.isLocalization_basicOpen b'
  let : Algebra Γ(Y, V.1) Γ(Y, Y.basicOpen b) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
    (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen b) Γ(Y', Y'.basicOpen b') :=
    (sq.cover.appLE (Y.basicOpen b) (Y'.basicOpen b') hbb').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', Y'.basicOpen b') :=
    (sq.cover.appLE V.1 (Y'.basicOpen b') ((hbb'.trans
      (sq.cover.preimage_mono (Y.basicOpen_le b))))).hom.toAlgebra
  have : IsScalarTower Γ(Y, V.1) Γ(Y', V'.1) Γ(Y', Y'.basicOpen b') :=
    isScalarTower_of_comp_eq _ _ _ (Scheme.Hom.appLE_map _ _ _)
  have : IsScalarTower Γ(Y, V.1) Γ(Y, Y.basicOpen b) Γ(Y', Y'.basicOpen b') :=
    isScalarTower_of_comp_eq _ _ _ (Scheme.Hom.map_appLE _ _ _)
  have : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, Y.basicOpen b) :=
    isScalarTower_of_comp_eq _ _ _ (Scheme.Hom.appLE_map _ _ _)
  have : IsLocalization.Away b Γ(Y, Y.basicOpen b) := V.2.isLocalization_basicOpen b
  have := algebra_syntomic_appLE hf.2 U ⟨Y.basicOpen b, V.2.basicOpen b⟩
    ((Y.basicOpen_le b).trans hVU)
  have := AlgebraicGeometry.quasiFinite_appLE hf'.1 U' ⟨Y'.basicOpen b', V'.2.basicOpen b'⟩
    ((Y'.basicOpen_le b').trans hV'U')
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U ⟨Y.basicOpen b, V.2.basicOpen b⟩
    ((Y.basicOpen_le b).trans hVU)
  have : Algebra.FiniteType Γ(X, U.1) Γ(Y, Y.basicOpen b) := inferInstance
  have := isLocallyNoetherian_source f' hf'
  have : IsNoetherianRing Γ(Y', Y'.basicOpen b') :=
    IsLocallyNoetherian.component_noetherian ⟨Y'.basicOpen b', V'.2.basicOpen b'⟩
  let D₁ : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
    ChartBaseChange.ofLocalizationSource b
  let D₃ : ChartBaseChange Γ(X, U.1) Γ(Y, Y.basicOpen b) Γ(X', U'.1) Γ(Y', Y'.basicOpen b') :=
    ChartBaseChange.ofSourceAway (D₂.comp D) b
  obtain ⟨G₀⟩ := Stacks.Discriminant.nonempty_finiteOpenFactorization (A := Γ(X, U.1))
    (B := Γ(Y, Y.basicOpen b))
  refine pullbackTate_pullbackTate_eq_of_classified D D₁ D₂ D₃ _ _ G₀ G'' k instR instC Dκ k'
    instR' instC' Dκ' ?_ ?_
  · rw [← chartValue_restrict_source f hf (tateIso f hf) U V hVU b D₁ F G₀]
    exact chartValue_tateIso f hf U V hVU b k instR instC Dκ G₀
  · rw [← chartValue_restrict_source f' hf' (tateIso f' hf') U' V' hV'U' b' D₂ G G'']
    exact chartValue_tateIso f' hf' U' V' hV'U' b' k' instR' instC' Dκ' G''

include hf hf' in
/-- The principal opens `D(b')` of `V'` lying over a classified principal open of `V` and
classified themselves generate the unit ideal of `Γ(Y', V')`. -/
theorem span_classified_eq_top (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens)
    (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
    Ideal.span {b' : Γ(Y', V'.1) | ∃ b : Γ(Y, V.1),
      Y'.basicOpen b' ≤ sq.cover ⁻¹ᵁ Y.basicOpen b ∧
      (∃ (n d : ℕ) (_ : NeZero d) (k : MvPolynomial (Fin n) (univBase.{u} n d))
        (_ : Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k))
        (_ : Algebra (univBase.{u} n d) Γ(X, U.1))
        (_ : Algebra (univChart n d k) Γ(Y, Y.basicOpen b)),
        letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
          (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
        Nonempty (ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X, U.1)
          Γ(Y, Y.basicOpen b))) ∧
      (∃ (n d : ℕ) (_ : NeZero d) (k : MvPolynomial (Fin n) (univBase.{u} n d))
        (_ : Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k))
        (_ : Algebra (univBase.{u} n d) Γ(X', U'.1))
        (_ : Algebra (univChart n d k) Γ(Y', Y'.basicOpen b')),
        letI : Algebra Γ(X', U'.1) Γ(Y', Y'.basicOpen b') :=
          (f'.appLE U' (Y'.basicOpen b') ((Y'.basicOpen_le b').trans hV'U')).hom.toAlgebra
        Nonempty (ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X', U'.1)
          Γ(Y', Y'.basicOpen b')))} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let p : PrimeSpectrum Γ(Y', V'.1) := ⟨m, hm.isPrime⟩
  let y' := V'.2.fromSpec p
  have hy'V' : y' ∈ V'.1 := by
    have : y' ∈ Set.range V'.2.fromSpec := ⟨p, rfl⟩
    rwa [V'.2.range_fromSpec] at this
  have hyV : sq.cover.base y' ∈ V.1 := hV'V hy'V'
  obtain ⟨b, hyb, -, hκ⟩ := exists_classified_basicOpen f hf U V hVU (sq.cover.base y') hyV 1
    (by rw [Scheme.basicOpen_one]; exact hyV)
  obtain ⟨b'₀, hb'₀, hy'b'₀⟩ := V'.2.exists_basicOpen_le
    (V := sq.cover ⁻¹ᵁ Y.basicOpen b) ⟨y', hyb⟩ hy'V'
  obtain ⟨b', hy'b', hb'b'₀, hκ'⟩ :=
    exists_classified_basicOpen f' hf' U' V' hV'U' y' hy'V' b'₀ hy'b'₀
  have hmem : b' ∈ m := hle (Ideal.subset_span ⟨b, hb'b'₀.trans hb'₀, hκ, hκ'⟩)
  have h1 : p ∈ V'.2.fromSpec ⁻¹ᵁ Y'.basicOpen b' := hy'b'
  rw [V'.2.fromSpec_preimage_basicOpen] at h1
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h1 hmem

/-- **Clause (2) for the Tate maps, on affine charts.** For a morphism `sq : Y'/X' → Y/X` of the
category of Section 0FKB, compatible affine charts `U, V, U', V'` and a chart base change `D`, the
base change along `D` of the chart value of `tateIso f hf` on `(U, V)` is the chart value of
`tateIso f' hf'` on `(U', V')`. -/
theorem tateIso_baseChange (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens)
    (V' : Y'.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1)
    (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1) (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf'.2 U' V' hV'U'
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1)),
      pullbackTate D (chartValue (tateIso f hf) U V hVU F) G =
        chartValue (tateIso f' hf') U' V' hV'U' G := by
  intro D F G
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := algebra_syntomic_appLE hf'.2 U' V' hV'U'
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  set s := {b' : Γ(Y', V'.1) | ∃ b : Γ(Y, V.1),
      Y'.basicOpen b' ≤ sq.cover ⁻¹ᵁ Y.basicOpen b ∧
      (∃ (n d : ℕ) (_ : NeZero d) (k : MvPolynomial (Fin n) (univBase.{u} n d))
        (_ : Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k))
        (instR : Algebra (univBase.{u} n d) Γ(X, U.1))
        (instC : Algebra (univChart n d k) Γ(Y, Y.basicOpen b)),
        let : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
          (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
        Nonempty (ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X, U.1)
          Γ(Y, Y.basicOpen b))) ∧
      (∃ (n d : ℕ) (_ : NeZero d) (k : MvPolynomial (Fin n) (univBase.{u} n d))
        (_ : Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k))
        (instR : Algebra (univBase.{u} n d) Γ(X', U'.1))
        (instC : Algebra (univChart n d k) Γ(Y', Y'.basicOpen b')),
        let : Algebra Γ(X', U'.1) Γ(Y', Y'.basicOpen b') :=
          (f'.appLE U' (Y'.basicOpen b') ((Y'.basicOpen_le b').trans hV'U')).hom.toAlgebra
        Nonempty (ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X', U'.1)
          Γ(Y', Y'.basicOpen b')))}
  have hs : Ideal.span s = ⊤ :=
    span_classified_eq_top f f' hf hf' sq U V U' V' hVU hV'U' hV'V
  let iA : ∀ b : s, Algebra Γ(X', U'.1) Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) := fun b ↦
    (f'.appLE U' (Y'.basicOpen b.1) ((Y'.basicOpen_le b.1).trans hV'U')).hom.toAlgebra
  let iB : ∀ b : s, Algebra Γ(Y', V'.1) Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) := fun b ↦
    (Y'.presheaf.map (homOfLE (Y'.basicOpen_le b.1)).op).hom.toAlgebra
  have iT : ∀ b : s, IsScalarTower Γ(X', U'.1) Γ(Y', V'.1) Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) :=
    fun b ↦ isScalarTower_of_comp_eq _ _ _ (Scheme.Hom.appLE_map _ _ _)
  have iL : ∀ b : s, IsLocalization.Away (b : Γ(Y', V'.1)) Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) :=
    fun b ↦ V'.2.isLocalization_basicOpen b.1
  have iS : ∀ b : s, Algebra.Syntomic Γ(X', U'.1) Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) :=
    fun b ↦ algebra_syntomic_appLE hf'.2 U' ⟨Y'.basicOpen b.1, V'.2.basicOpen b.1⟩
      ((Y'.basicOpen_le b.1).trans hV'U')
  have iQ : ∀ b : s, Algebra.QuasiFinite Γ(X', U'.1) Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) :=
    fun b ↦ AlgebraicGeometry.quasiFinite_appLE hf'.1 U' ⟨Y'.basicOpen b.1, V'.2.basicOpen b.1⟩
      ((Y'.basicOpen_le b.1).trans hV'U')
  let Dl : ∀ b : s, ChartBaseChange Γ(X', U'.1) Γ(Y', V'.1) Γ(X', U'.1)
      Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) := fun b ↦ ChartBaseChange.ofLocalizationSource b.1
  let Gl : ∀ b : s, FiniteOpenFactorization.{u, u, u} Γ(X', U'.1)
      Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1))) := fun b ↦
    (Stacks.Discriminant.nonempty_finiteOpenFactorization (A := Γ(X', U'.1))
      (B := Γ(Y', Y'.basicOpen b.1))).some
  refine eq_of_pullbackTate_eq s hs (fun _ ↦ Γ(X', U'.1))
    (fun b ↦ Γ(Y', Y'.basicOpen (b : Γ(Y', V'.1)))) Dl Gl _ _ fun b ↦ ?_
  obtain ⟨b₀, hbb', ⟨n, d, hd, k, hqf, instR, instC, ⟨Dκ⟩⟩,
    ⟨n', d', hd', k', hqf', instR', instC', ⟨Dκ'⟩⟩⟩ := b.2
  exact tateIso_baseChange_local f f' hf hf' sq U V U' V' hVU hU'U hV'U' hV'V b₀ b.1 hbb' k instR
    instC Dκ k' instR' instC' Dκ' D (Dl b) F G (Gl b)

end AlgebraicGeometry.TateMap
