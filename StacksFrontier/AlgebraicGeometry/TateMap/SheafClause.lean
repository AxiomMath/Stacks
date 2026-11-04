module

public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackComparison
public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackComparisonOmegaGlue
public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackExt
public import StacksFrontier.AlgebraicGeometry.TateMap.Rule

/-!
# Clause (2) of the Tate map at sheaf level and on charts

For a morphism `b/a : Y'/X' → Y/X` of the category of Section 0FKB and isomorphisms
`c : det(NL_{Y/X}) ≅ ω_{Y/X}`, `c' : det(NL_{Y'/X'}) ≅ ω_{Y'/X'}`, the equation
`b^* c ≫ (b^* ω_{Y/X} ≅ ω_{Y'/X'}) = (b^* det(NL_{Y/X}) ≅ det(NL_{Y'/X'})) ≫ c'` of morphisms of
`𝒪_{Y'}`-modules holds if and only if, on every compatible quadruple of affine charts on which the
square is a chart base change, the pullback of the chart value of `c` is the chart value of `c'`.

## Main results

* `AlgebraicGeometry.TateMap.pullbackTate_chartValue_of_comp_eq`: the sheaf form gives the
  chart form.
* `AlgebraicGeometry.TateMap.comp_eq_of_pullbackTate_chartValue`: the chart form gives the
  sheaf form.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Discriminant Stacks.TateMap
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TateMap

variable {X Y X' Y' : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian X']
  {f : Y ⟶ X} {f' : Y' ⟶ X'} (hf : IsQuasiFiniteSyntomic f) (hf' : IsQuasiFiniteSyntomic f')
  (sq : OpenBaseChangeSquare f f')

/-- The pullback along `b` of a morphism `t : M ⟶ N` sends the pulled-back section
`pullbackSection b M W W' h a` to the pulled-back section of `t.app W a`. -/
theorem app_pullbackSection {S T : Scheme.{u}} (b : T ⟶ S) {M N : S.Modules} (t : M ⟶ N)
    (W : S.Opens) (W' : T.Opens) (h : W' ≤ b ⁻¹ᵁ W) (a : Γ(M, W)) :
    ((Scheme.Modules.pullback b).map t).app W' (Scheme.Modules.pullbackSection b M W W' h a) =
      Scheme.Modules.pullbackSection b N W W' h (t.app W a) :=
  Scheme.Modules.pullbackSection_naturality b t W W' h a

/-- The chart value of `c` sends the image under `detNLChartEquiv` of a section `s` to the image
of `c.hom.app V s` under the local equivalence of `omegaData`. -/
theorem chartValue_detNLChartEquiv (c : detNL f hf ≅ omega f hf) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (F : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) (s : Γ(detNL f hf, V.1)) :
    letI := isLocallyNoetherian_source f hf
    letI := hf.1
    chartValue c U V hVU F (detNLChartEquiv f hf U V hVU s) =
      (omegaData f hf).localEquiv U V hVU F (c.hom.app V.1 s) := by
  simp [chartValue]

/-- The chart form of clause (2) holds on a compatible quadruple of charts if and only if
the two sheaf-level morphisms agree on sections pulled back from the chart. -/
private theorem pullbackTate_chartValue_iff_app_pullbackSection (c : detNL f hf ≅ omega f hf)
    (c' : detNL f' hf' ≅ omega f' hf')
    (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens) (V' : Y'.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
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
      pullbackTate D (chartValue c U V hVU F) G = chartValue c' U' V' hV'U' G ↔
      ∀ s : Γ(detNL f hf, V.1),
        (omegaPullbackIso hf hf' sq).hom.app V'.1 (((Scheme.Modules.pullback sq.cover).map
          c.hom).app V'.1 (Scheme.Modules.pullbackSection sq.cover (detNL f hf) V.1 V'.1 hV'V s)) =
        c'.hom.app V'.1 ((detNLPullbackIso hf hf' sq).hom.app V'.1
          (Scheme.Modules.pullbackSection sq.cover (detNL f hf) V.1 V'.1 hV'V s)) := by
  intro D F G
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := algebra_syntomic_appLE hf'.2 U' V' hV'U'
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  let := isLocallyNoetherian_source f' hf'
  let := hf'.1
  have h1 := detNLPullbackIso_pullbackSection hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D
  have h2 := omegaPullbackIso_pullbackSection hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G
  constructor
  · intro hD s
    apply ((omegaData f' hf').localEquiv U' V' hV'U' G).injective
    rw [app_pullbackSection, h2, ← chartValue_detNLChartEquiv hf c U V hVU F s,
      ← pullbackTate_detNLBaseChange_one_tmul D (chartValue c U V hVU F) G, hD,
      ← chartValue_detNLChartEquiv hf' c' U' V' hV'U' G, h1 s, LinearEquiv.apply_symm_apply]
  · intro hs
    refine (eq_pullbackTate D _ G _ ((detNLChartEquiv f hf U V hVU).surjective.forall.2 fun s ↦
      ?_)).symm
    rw [chartValue_detNLChartEquiv, ← h2 (c.hom.app V.1 s),
      ← (LinearEquiv.eq_symm_apply _).1 (h1 s), chartValue_detNLChartEquiv,
      ← hs s, app_pullbackSection]

/-- **From the sheaf form of clause (2) to the chart form**, for one morphism of the category of
Section 0FKB and one pair of isomorphisms. -/
theorem pullbackTate_chartValue_of_comp_eq (c : detNL f hf ≅ omega f hf)
    (c' : detNL f' hf' ≅ omega f' hf')
    (hsq : (Scheme.Modules.pullback sq.cover).map c.hom ≫ (omegaPullbackIso hf hf' sq).hom =
      (detNLPullbackIso hf hf' sq).hom ≫ c'.hom)
    (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens) (V' : Y'.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
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
      pullbackTate D (chartValue c U V hVU F) G = chartValue c' U' V' hV'U' G :=
  fun D F G ↦ (pullbackTate_chartValue_iff_app_pullbackSection hf hf' sq c c' U V U' V'
    hVU hU'U hV'U' hV'V D F G).2 fun _ ↦
    congrArg (fun φ : _ ⟶ omega f' hf' ↦ φ.app V'.1 _) hsq

/-- On pulled-back sections over a compatible quadruple of affine charts, the chart form of
clause (2) gives the sheaf form. -/
theorem comp_app_pullbackSection_of_pullbackTate (c : detNL f hf ≅ omega f hf)
    (c' : detNL f' hf' ≅ omega f' hf')
    (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens) (V' : Y'.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
    (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1) :
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
      pullbackTate D (chartValue c U V hVU F) G = chartValue c' U' V' hV'U' G →
      ∀ s : Γ(detNL f hf, V.1),
        (omegaPullbackIso hf hf' sq).hom.app V'.1 (((Scheme.Modules.pullback sq.cover).map
          c.hom).app V'.1 (Scheme.Modules.pullbackSection sq.cover (detNL f hf) V.1 V'.1 hV'V s)) =
        c'.hom.app V'.1 ((detNLPullbackIso hf hf' sq).hom.app V'.1
          (Scheme.Modules.pullbackSection sq.cover (detNL f hf) V.1 V'.1 hV'V s)) :=
  fun D F G ↦ (pullbackTate_chartValue_iff_app_pullbackSection hf hf' sq c c' U V U' V'
    hVU hU'U hV'U' hV'V D F G).1

/-- **From the chart form of clause (2) to the sheaf form**, for one morphism of the category of
Section 0FKB and one pair of isomorphisms. -/
theorem comp_eq_of_pullbackTate_chartValue (c : detNL f hf ≅ omega f hf)
    (c' : detNL f' hf' ≅ omega f' hf')
    (h : ∀ (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens) (V' : Y'.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
      (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1),
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
        pullbackTate D (chartValue c U V hVU F) G = chartValue c' U' V' hV'U' G) :
    (Scheme.Modules.pullback sq.cover).map c.hom ≫ (omegaPullbackIso hf hf' sq).hom =
      (detNLPullbackIso hf hf' sq).hom ≫ c'.hom := by
  refine hom_ext_of_pullbackSection sq.cover _ _ (fun V V' ↦ ∃ k : sq.Chart,
    k.V.1 = V ∧ k.V'.1 = V') (fun V V' ⟨k, hV, hV'⟩ ↦ hV ▸ hV' ▸ k.hV'V) (fun W y hy ↦ ?_) ?_
  · obtain ⟨U, V₁, hyV₁, hV₁U⟩ := Stacks.Discriminant.exists_affineChartPair f y
    have hU : y ∈ f ⁻¹ᵁ U.1 := hV₁U hyV₁
    obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ W ⊓ f ⁻¹ᵁ U.1 from ⟨hy, hU⟩) (W ⊓ f ⁻¹ᵁ U.1).2
    refine ⟨V, hyV, hVW.trans inf_le_left, fun y' hy' ↦ ?_⟩
    obtain ⟨U', V', hU'U, hV'U', hV'V, hy'V', -, ⟨D⟩⟩ :=
      sq.exists_chartBaseChange_of_le U ⟨V, hV⟩ (hVW.trans inf_le_right) y' hy' ⊤ trivial
    exact ⟨V', ⟨⟨U, ⟨V, hV⟩, U', V', hVW.trans inf_le_right, hU'U, hV'U', hV'V, D⟩, rfl, rfl⟩,
      hy'V'⟩
  · rintro V V' ⟨⟨U, V₀, U', V'₀, hVU, hU'U, hV'U', hV'V, D⟩, rfl, rfl⟩ s
    let : Algebra Γ(X, U.1) Γ(Y, V₀.1) := (f.appLE U.1 V₀.1 hVU).hom.toAlgebra
    let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    let : Algebra Γ(X', U'.1) Γ(Y', V'₀.1) := (f'.appLE U'.1 V'₀.1 hV'U').hom.toAlgebra
    let : Algebra Γ(Y, V₀.1) Γ(Y', V'₀.1) := (sq.cover.appLE V₀.1 V'₀.1 hV'V).hom.toAlgebra
    have := algebra_syntomic_appLE hf.2 U V₀ hVU
    have := algebra_syntomic_appLE hf'.2 U' V'₀ hV'U'
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
    have := quasiFinite_appLE hf.1 U V₀ hVU
    obtain ⟨F⟩ := Stacks.Discriminant.nonempty_finiteOpenFactorization (A := Γ(X, U.1))
      (B := Γ(Y, V₀.1))
    have := quasiFinite_appLE hf'.1 U' V'₀ hV'U'
    obtain ⟨G⟩ := Stacks.Discriminant.nonempty_finiteOpenFactorization (A := Γ(X', U'.1))
      (B := Γ(Y', V'₀.1))
    exact comp_app_pullbackSection_of_pullbackTate hf hf' sq c c' U V₀ U' V'₀ hVU hU'U hV'U'
      hV'V D F G (h U V₀ U' V'₀ hVU hU'U hV'U' hV'V D F G) s

end AlgebraicGeometry.TateMap
