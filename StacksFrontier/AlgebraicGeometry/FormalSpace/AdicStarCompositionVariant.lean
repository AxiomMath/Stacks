module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarChartCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionPresented

/-!
# Composition of a local property of morphisms of locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Remark 87.21.13 (Stacks 0GBJ)** defines
what it means for a local property `P` of morphisms of `WAdm^{adic*}` (Remark 0ANH) to be
*stable under composition* — `TopologicalRing.PropertyIsStableUnderCompositionAdicStar`, with
`P (B → A) ∧ P (C → B) ⟹ P (C → A)` for arrows of `WAdm^{adic*}` — and asserts that in exactly
the same way as Lemma 87.21.12 (Stacks 0GBI) one obtains its variant for morphisms between
locally adic\* formal algebraic spaces over `S`. This file states and proves that variant.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_finite_chartFactorization_of_comp`: the covering of the
  proof of Stacks 0GBI, refined against an affine étale diagram over the composite.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocal`: the
  variant of Stacks 0GBI for condition (1) of Stacks 0ANG, at an arbitrary class of rings.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyAdicStar`:
  **the second half of Stacks 0GBJ**: if `f : X ⟶ Y` and `g : Y ⟶ Z` are morphisms of locally
  adic\* formal algebraic spaces satisfying the equivalent conditions of Stacks 0ANG (in the
  adic\* reading of Remark 0ANH) for `P`, then so does `g ∘ f`.

## Implementation notes

The proof is the source's. Given an affine étale diagram `τ : U₀ ⟶ V₀` over `g ∘ f`, the
covering of the proof of Stacks 0GBI is refined against it: finitely many affine étale charts
`Wₛ ⟶ U₀` cover `U₀`, and each `Wₛ ⟶ U₀ ⟶ V₀` factors as `Wₛ ⟶ Mₛ ⟶ V₀` through an affine
chart `Mₛ` of `Y`, over `f` and over `g` respectively. On the disjoint unions, `P` holds on
`∐ Wₛ ⟶ ∐ Mₛ` and on `∐ Mₛ ⟶ V₀` by the hypotheses on `f` and `g`, hence on the composite by
stability under composition, read through Stacks 0AN0; and axiom (2) of Situation 0CBA descends
it along the surjective étale map `∐ Wₛ ⟶ U₀`, whose ring map is faithfully flat by Stacks 0AN9.

Condition (1) of Stacks 0ANG, `AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap`, asks
`P` of *every* presentation of a chart map by rings of the class. The hypotheses on `f` and `g`
are condition (1), so each step above is taken at the presentation at hand and nothing is
transported between presentations. For this reason the invariance of `P` under isomorphism of
source and target, with which Situation 0CBA opens and which the implication (3) ⟹ (1) of
Stacks 0ANG uses in this library
(`AlgebraicGeometry.FormalSpace.hasProperty_tfae_isAdicStar`), is not needed. Conditions (2)
and (3) for `g ∘ f` follow from condition (1) by the implications (1) ⟹ (2) ⟹ (3) of Stacks
0ANG, which hold for every property. Condition (1) is the strongest of the three, and under the
source's hypotheses, which include that invariance, the three are equivalent by the second half
of Remark 0ANH, so a morphism satisfying "the equivalent conditions" is one satisfying
condition (1).

## References

* [Stacks Project, Tag 0GBJ](https://stacks.math.columbia.edu/tag/0GBJ)
* [Stacks Project, Tag 0GBI](https://stacks.math.columbia.edu/tag/0GBI)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-! ### The covering of the proof of Stacks 0GBI, refined against a diagram -/

/-- **The covering of the proof of Stacks 0GBI, refined against an affine étale diagram over the
composite.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of fppf sheaves with `Y`, `Z` formal
algebraic spaces, and let `τ : U₀ ⟶ V₀` be a map of affine formal algebraic spaces lying over
`g ∘ f` through representable étale maps `a : U₀ ⟶ X`, `b : V₀ ⟶ Z`. Then there is a *finite*
affine étale covering `{Wₛ ⟶ U₀}` and for each `s` a factorization `Wₛ ⟶ Mₛ ⟶ V₀` of
`Wₛ ⟶ U₀ ⟶ V₀` through an affine formal algebraic space `Mₛ` representable étale over `Y`,
such that `Wₛ ⟶ Mₛ` lies over `f` and `Mₛ ⟶ V₀` lies over `g`.

The `Mₛ` are charts of an atlas of the fibre product `V₀ ×_Z Y`, a formal algebraic space by
Stacks 0AJ3, to which `U₀` maps; the `Wₛ` are charts of atlases of the fibre products
`Mₛ ×_{V₀ ×_Z Y} U₀`, formal algebraic spaces by the étale case of Stacks 0AJH; and finitely
many of them cover `U₀`, which is quasi-compact. -/
theorem exists_finite_chartFactorization_of_comp
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z)
    {U₀ V₀ : FppfSheaf B S hS} (a : U₀ ⟶ X) (b : V₀ ⟶ Z) (τ : U₀ ⟶ V₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀) (hV₀ : IsAffineFormalAlgebraicSpace B S hS V₀)
    (hb : IsRepresentableEtale B S hS b) (hsq : a ≫ f ≫ g = τ ≫ b) :
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (W M : σ → FppfSheaf B S hS) (p : ∀ s, W s ⟶ U₀)
      (μ : ∀ s, W s ⟶ M s) (ν : ∀ s, M s ⟶ V₀) (y : ∀ s, M s ⟶ Y),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (M s)) ∧
        (∀ s, IsRepresentableEtale B S hS (y s)) ∧ (∀ s, p s ≫ a ≫ f = μ s ≫ y s) ∧
        (∀ s, y s ≫ g = ν s ≫ b) ∧ ∀ s, μ s ≫ ν s = p s ≫ τ := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- `V₀ ×_Z Y` is a formal algebraic space, and `U₀` maps to it
  have hQ : IsFormalAlgebraicSpace B S hS (pullback b g) :=
    isFormalAlgebraicSpace_pullback_chart_of_etale B S hS hEt hY hZ V₀ b hV₀ hb
  obtain ⟨ℓ, hℓfst, hℓsnd⟩ : ∃ ℓ : U₀ ⟶ pullback b g,
      ℓ ≫ pullback.fst b g = τ ∧ ℓ ≫ pullback.snd b g = a ≫ f :=
    ⟨pullback.lift τ (a ≫ f) (by rw [Category.assoc, hsq]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  -- an atlas `{Mⱼ ⟶ V₀ ×_Z Y}`, and atlases of the fibre products `Mⱼ ×_{V₀ ×_Z Y} U₀`
  obtain ⟨J, M, m, hMaff, hMet, hMsurj⟩ := hQ.2
  have hT : ∀ j, IsFormalAlgebraicSpace B S hS (pullback (m j) ℓ) := fun j ↦
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal B S hS hEt (m j) ℓ
      hU₀ (hMet j)
  choose K W w hWaff hWet hWsurj using fun j ↦ (hT j).2
  have hcover : IsAffineEtaleCover B S hS (fun s : Σ j, K j ↦ W s.1 s.2)
      (fun s ↦ w s.1 s.2 ≫ pullback.snd (m s.1) ℓ) :=
    ⟨fun s ↦ hWaff s.1 s.2, fun s ↦ IsRepresentableEtale.comp B S hS (hWet s.1 s.2)
      (isRepresentableEtale_pullback_snd B S hS (m s.1) ℓ (hMet s.1)),
      Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (fun j ↦ pullback.snd (m j) ℓ) w
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd ℓ m hMsurj) hWsurj⟩
  -- finitely many of the charts cover `U₀`
  obtain ⟨σ, hσ, κ, hsub⟩ :=
    exists_finite_subcover_of_isAffineFormalAlgebraicSpace B S hS U₀ _ _ hU₀ hcover
  refine ⟨σ, hσ, fun s ↦ W (κ s).1 (κ s).2, fun s ↦ M (κ s).1,
    fun s ↦ w (κ s).1 (κ s).2 ≫ pullback.snd (m (κ s).1) ℓ,
    fun s ↦ w (κ s).1 (κ s).2 ≫ pullback.fst (m (κ s).1) ℓ,
    fun s ↦ m (κ s).1 ≫ pullback.fst b g, fun s ↦ m (κ s).1 ≫ pullback.snd b g,
    hsub, fun s ↦ hMaff (κ s).1, fun s ↦ IsRepresentableEtale.comp B S hS (hMet (κ s).1)
      (isRepresentableEtale_pullback_snd B S hS b g hb), fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩
  · simp only [Category.assoc, ← hℓsnd, pullback.condition_assoc]
  · simp only [Category.assoc, pullback.condition]
  · simp only [Category.assoc, pullback.condition_assoc, hℓfst]

/-! ### Condition (1) for the composite, from the axioms of a local property -/

/-- **The variant of Stacks 0GBI at a class of rings, for condition (1) of Stacks 0ANG, with no
invariance of `P` under isomorphism.** Let `C` be a class of weakly admissible rings with
countable fundamental systems of neighbourhoods of zero, stable under completion along étale
maps, let `P` be a local property of morphisms of rings of `C` (the three axioms of Situation
0CBA) which is stable under composition on arrows of `C`, and let `f : X ⟶ Y`, `g : Y ⟶ Z` be
morphisms of fppf sheaves with `Y` and `Z` formal algebraic spaces, every affine formal
algebraic space representable étale over `Y` being presented by a ring of `C`. If `f` and `g`
satisfy condition (1) of Stacks 0ANG for `P`, so does `g ∘ f`.

Given a diagram `τ : U₀ ⟶ V₀` over `g ∘ f`, the covering
`AlgebraicGeometry.FormalSpace.exists_finite_chartFactorization_of_comp` gives finitely many
charts `Wₛ ⟶ U₀` and factorizations `Wₛ ⟶ Mₛ ⟶ V₀` over `f` and over `g`. Their disjoint unions
`∐ Wₛ ⟶ ∐ Mₛ ⟶ V₀` are again maps of affine formal algebraic spaces over `f` and over `g`, with
`∐ Mₛ` representable étale over `Y`, so condition (1) for `f` and for `g` gives `P` on both, on
every presentation; the composition axiom then gives `P` on `∐ Wₛ ⟶ V₀` through Stacks 0AN0,
`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_comp_of_spfPresentation`; and axiom
(2) of Situation 0CBA descends it along the surjection `∐ Wₛ ⟶ U₀` to every presentation of
`τ`,
`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_isLocal`.
Because conditions (1) for `f` and `g` hold on every presentation, no presentation is ever
transported, so the invariance of `P` under isomorphism is not used. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocal
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (hCw : ClassIsWeaklyAdmissible C) (hCc : ClassHasCountableNhdsZero C)
    (hCcompl : ClassIsStableUnderEtaleCompletion C)
    (hP : TopologicalRing.PropertyIsLocal P C)
    (hcomp : ∀ {A M R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing M] [TopologicalSpace M] [IsTopologicalRing M]
      [IsLinearTopology M M] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C A → C M → C R → ∀ (φ : M →+* R) (ψ : A →+* M),
      Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hYC : ∀ (M : FppfSheaf B S hS) (y : M ⟶ Y), IsAffineFormalAlgebraicSpace B S hS M →
      IsRepresentableEtale B S hS y → ∃ PM : SpfPresentation B S hS M, C PM.ring)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro U₀ V₀ a b τ hU₀ hV₀ ha hb hsq
  obtain ⟨σ, hσ, W, M, p, μ, ν, y, hWcover, hMaff, hy, hsqf, hsqg, hμν⟩ :=
    exists_finite_chartFactorization_of_comp B S hS hEt f g hY hZ a b τ hU₀ hV₀ hb hsq
  have hp := coproductsRepresentableEtale B S hS σ W U₀ p hσ hWcover.2.1
  have hy' := coproductsRepresentableEtale B S hS σ M Y y hσ hy
  have hW : IsAffineFormalAlgebraicSpace B S hS (∐ W) :=
    isAffineFormalAlgebraicSpace_sigma B S hS W hWcover.1
  have hM : IsAffineFormalAlgebraicSpace B S hS (∐ M) :=
    isAffineFormalAlgebraicSpace_sigma B S hS M hMaff
  have hsq₁ : (Sigma.desc p ≫ a) ≫ f = Limits.Sigma.map μ ≫ Sigma.desc y :=
    Sigma.hom_ext _ _ fun s ↦ by simpa using hsqf s
  have hsq₂ : Sigma.desc y ≫ g = Sigma.desc ν ≫ b :=
    Sigma.hom_ext _ _ fun s ↦ by simpa using hsqg s
  have hsq₃ : Sigma.desc p ≫ τ = (Limits.Sigma.map μ ≫ Sigma.desc ν) ≫ 𝟙 V₀ :=
    Sigma.hom_ext _ _ fun s ↦ by simpa using (hμν s).symm
  -- `P` on `∐ Wₛ ⟶ ∐ Mₛ`, by condition (1) for `f`
  have hμ : HasPropertyOnAffineChartMap B S hS C P (Limits.Sigma.map μ) :=
    hf (∐ W) (∐ M) (Sigma.desc p ≫ a) (Sigma.desc y) (Limits.Sigma.map μ) hW hM
      (IsRepresentableEtale.comp B S hS hp ha) hy' hsq₁
  -- `P` on `∐ Mₛ ⟶ V₀`, by condition (1) for `g`
  have hν : HasPropertyOnAffineChartMap B S hS C P (Sigma.desc ν) :=
    hg (∐ M) V₀ (Sigma.desc y) b (Sigma.desc ν) hM hV₀ hy' hb hsq₂
  -- `P` on the composite `∐ Wₛ ⟶ V₀`, by the composition axiom
  have hμν' : HasPropertyOnAffineChartMap B S hS C P (Limits.Sigma.map μ ≫ Sigma.desc ν) :=
    hasPropertyOnAffineChartMap_comp_of_spfPresentation B S hS C P hCw hcomp _ _
      (hYC (∐ M) (Sigma.desc y) hM hy') hμ hν
  -- axiom (2), along the surjection `∐ Wₛ ⟶ U₀`
  exact hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_isLocal B S hS C P hCw hCc
    hCcompl hP τ (Sigma.desc p) (Limits.Sigma.map μ ≫ Sigma.desc ν) (𝟙 V₀) hW hV₀ hp
    (isRepresentableEtale_iso_hom B S hS (Iso.refl _)) hWcover.2.2 hsq₃ hμν'

/-! ### The variant of Stacks 0GBI for locally adic\* formal algebraic spaces -/

/-- **Stacks 0GBJ, second half: the variant of Lemma 0GBI for locally adic\* formal algebraic
spaces.** Let `P` be a local property of morphisms of `WAdm^{adic*}` (Remark 0ANH) which is
stable under composition in the sense of the first half of Remark 0GBJ,
`TopologicalRing.PropertyIsStableUnderCompositionAdicStar`. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally adic\* formal algebraic spaces over `S`. If `f` and `g` satisfy the
equivalent conditions of Stacks 0ANG for `P` (in the adic\* reading of Remark 0ANH) — here
condition (1), that `P` holds on every affine étale diagram, the strongest of the three — then
so does `g ∘ f`: the conclusion lists all three conditions.

Condition (1) for `g ∘ f` is
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocal` at the
class `WAdm^{adic*}`: every affine formal algebraic space representable étale over `Y` is adic\*
by the implication (2) ⟹ (1) of Stacks 0AKX, hence presented by a ring of `WAdm^{adic*}`.
Conditions (2) and (3) follow by the implications (1) ⟹ (2) ⟹ (3) of Stacks 0ANG. The
invariance of `P` under isomorphism of source and target, which Situation 0CBA stipulates, is
not needed. -/
@[stacks 0GBJ "the second half, the variant of Lemma 0GBI for morphisms between locally adic* \
formal algebraic spaces: for a local property P of morphisms of WAdm^{adic*} (Remark 0ANH) which \
is stable under composition in the sense of the first half, \
TopologicalRing.PropertyIsStableUnderCompositionAdicStar, and morphisms f : X -> Y, g : Y -> Z of \
locally adic* formal algebraic spaces satisfying the equivalent conditions of Stacks 0ANG \
(condition (1)), the composite g o f satisfies all three; the invariance of P under isomorphism \
of Situation 0CBA is not used"]
theorem hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyAdicStar
    (hP : TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P (f ≫ g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (f ≫ g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P (f ≫ g) := by
  have hEt : RepresentableEtaleOverAffineIsFormal B S hS :=
    representableEtaleOverAffineIsFormal B S hS
  have hYadic : HasAffineEtaleChartProperty B S hS Y (IsAdicStar B S hS) :=
    (hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem B S hS _ hY.1 _
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).2 hY.2
  have h1 : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P (f ≫ g) :=
    hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocal B S hS P TopologicalRing.IsAdicStar hEt
      classIsWeaklyAdmissible_isAdicStar classHasCountableNhdsZero_isAdicStar
      classIsStableUnderEtaleCompletion_isAdicStar hP.isLocal
      (fun hA hM hR φ ψ hφ hψ hPφ hPψ ↦ hP.comp
        (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hR)
        (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hM)
        (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hA) hR hM hA φ ψ hφ hψ hPφ
        hPψ)
      f g hY.1 hZ.1
      (fun M y hM hy ↦ exists_spfPresentation_of_isAdicStar B S hS M (hYadic M y hM hy)) hf hg
  have h2 : HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (f ≫ g) :=
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS _ P (f ≫ g) hZ.1
      (isFormalAlgebraicSpace_pullback_chart_of_etale B S hS hEt hX.1 hZ.1) h1
  exact ⟨h1, h2, hasPropertyAfterSourceCover_of_afterTargetCover B S hS _ P (f ≫ g) h2⟩

end AlgebraicGeometry.FormalSpace

end
