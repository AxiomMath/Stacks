module

public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.GlobalImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.SymLift
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedRingFunctoriality

/-!
# The charts of `r_{L, ψ}` along a homomorphism of graded algebras

Let `f : X ⟶ S` be a morphism of schemes, `P = (L, ψ)` a graded map `f^* B ⟶ ⨁_{d ≥ 0} L^{⊗ d}`
in the sense of [Stacks, Tag 01O8] for a quasi-coherent graded `𝒪_S`-algebra `B`, and
`φ : A ⟶ B` a homomorphism of graded algebras. The precomposition `P ∘ φ` is a graded map for
`A`. Over an affine open `V` of the base and at a homogeneous section `g ∈ A(V)` of positive
degree, the chart `X_{ψ(φ g)} ⟶ Spec A(V)_{(g)}` of `P ∘ φ` is the chart
`X_{ψ(φ g)} ⟶ Spec B(V)_{(φ g)}` of `P` followed by `Spec` of the induced map of homogeneous
localizations. When `φ` is surjective on sections of positive degree over affine opens, that
second map is a closed immersion, so an immersion `r_{L, ψ}` has immersions as the charts of
`r_{L, ψ ∘ φ}`.

## Main results

* `Stacks.Tag01VMVeryAmple.affineDatum_precomp`: the datum of [Stacks, Tag 01NK] that `P ∘ φ`
  induces over an open of the base is the one `P` induces, pulled back along `φ`.
* `Stacks.Tag01VMVeryAmple.toSpecAway_comap`: the chart of a graded map pulled back along a graded
  ring homomorphism is the chart of the graded map followed by `Spec` of the induced map of
  homogeneous localizations.
* `Stacks.Tag01VMVeryAmple.surjective_awayMap`: that induced map is surjective when the ring
  homomorphism is surjective in positive degrees.
* `Stacks.Tag01VMVeryAmple.isImmersion_toSpecAway_of_isImmersion`: the charts of an immersion
  `r_{L, ψ}` are immersions.
* `Stacks.Tag01VMVeryAmple.chartsAreImmersions_precomp`: **the charts of `r_{L, ψ ∘ φ}` at
  degree-one sections are immersions covering `X`**, when `r_{L, ψ}` is an immersion, `φ` is
  surjective in positive degrees over affine opens and the degree-one values of `ψ ∘ φ` generate
  `L` at every point.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Graded
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartFullGraded
open Stacks.QuasiProjectiveCompactification
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.Tag01VMVeryAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Charts of a pulled-back graded map -/

section Comap

variable {R R' σ τ : Type u} [CommRing R] [CommRing R']
  [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ R'] [AddSubgroupClass τ R']
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)

/-- **The induced map of homogeneous localizations is surjective** when `φ` is surjective in
every positive degree and the element inverted has positive degree: a fraction `x / φ(f)^n` is
also `x φ(f) / φ(f)^{n+1}`, whose numerator has positive degree and so lies in the image. -/
theorem surjective_awayMap {e : ℕ} {f : R} (hf : f ∈ 𝒜 e) (he : 0 < e)
    (hφ : ∀ n : ℕ, 0 < n → ∀ y ∈ ℬ n, ∃ x ∈ 𝒜 n, φ x = y) :
    Function.Surjective (HomogeneousLocalization.Away.map φ f) := by
  intro z
  obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective ℬ (map_mem φ hf) z
  have hy' : y * φ f ∈ ℬ ((n + 1) • e) := by
    rw [succ_nsmul]
    exact SetLike.mul_mem_graded hy (map_mem φ hf)
  have hpos : 0 < (n + 1) • e := by
    rw [smul_eq_mul]
    exact Nat.mul_pos n.succ_pos he
  obtain ⟨x, hx, hxy⟩ := hφ ((n + 1) • e) hpos _ hy'
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hf (n + 1) x hx, ?_⟩
  rw [HomogeneousLocalization.Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, hxy]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, pow_succ]; ring⟩

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections ℬ L) {e : ℕ} {f : R} (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
  (hV : V ≤ nonvanishingOpen T (natTensorPow L e)
    ((Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap φ ψ).toFun e ⟨f, hf⟩))

/-- **The chart of a pulled-back graded map.** The chart `V ⟶ Spec A_{(f)}` of `χ = ψ ∘ φ` at `f`
is the chart `V ⟶ Spec B_{(φ f)}` of `ψ` at `φ f` followed by `Spec` of
`HomogeneousLocalization.Away.map φ f`. The nonvanishing opens of `χ(f)` and of `ψ(φ f)` are the
same open, so the one hypothesis `hV` serves both. -/
theorem toSpecAway_comap :
    ((Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap φ ψ).homogeneousRatios
        hf hV).toSpecAway he =
      (ψ.homogeneousRatios (map_mem φ hf) hV).toSpecAway he ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φ f)) := by
  unfold Stacks.MorphismToProj.HomogeneousRatios.toSpecAway
  rw [Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.lift_comp_awayMap φ ψ hf he hV hV,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end Comap

/-! ### The datum induced over an open of the base by a precomposition -/

section Precomp

variable {S X : Scheme.{u}} {A B : SheafGradedAlgebra.{u} S} {f : X ⟶ S}

/-- The component of the image of a homogeneous section under the graded ring homomorphism
induced by `φ` is the image of its component. -/
theorem componentEquiv_sectionHom (φ : SheafGradedAlgebraHom A B) (V : S.Opens) (n : ℕ)
    (a : A.grading V n) :
    B.componentEquiv V n ⟨φ.sectionHom V a, map_mem (φ.sectionHom V) a.2⟩ =
      (φ.app (n : ℤ)).app V (A.componentEquiv V n a) := by
  obtain ⟨y, hy⟩ := (A.mem_grading_iff V (a : A.sectionRing V)).mp a.2
  obtain ⟨a, ha⟩ := a
  simp only at hy
  subst hy
  change (φ.sectionHom V (DirectSum.of (A.sectionPieces V) n y)) n = _
  rw [SheafGradedAlgebraHom.sectionHom_of]
  change (DirectSum.of (B.sectionPieces V) n _) n = (φ.app (n : ℤ)).app V
    ((DirectSum.of (A.sectionPieces V) n y) n)
  rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  rfl

/-- **The datum of [Stacks, Tag 01NK] induced by `P ∘ φ` over an open `V` of the base is the one
induced by `P`, pulled back along the graded ring homomorphism `A(V) ⟶ B(V)` of `φ`.** -/
theorem affineDatum_precomp (P : GradedPowerMap B f) (φ : SheafGradedAlgebraHom A B)
    (V : S.Opens) :
    (P.precomp φ).affineDatum V =
      Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap (φ.sectionHom V)
        (P.affineDatum V) := by
  have h : ∀ n, ((P.precomp φ).affineDatum V).toFun n =
      (Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap (φ.sectionHom V)
        (P.affineDatum V)).toFun n := by
    intro n
    refine AddMonoidHom.ext fun a => ?_
    change Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection P.L
        (f ⁻¹ᵁ V) n (P.value n V ((φ.app (n : ℤ)).app V (A.componentEquiv V n a))) =
      Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection P.L
        (f ⁻¹ᵁ V) n (P.value n V (B.componentEquiv V n
          ⟨φ.sectionHom V a, map_mem (φ.sectionHom V) a.2⟩))
    rw [componentEquiv_sectionHom]
  cases h' : (P.precomp φ).affineDatum V with
  | mk t m =>
    cases h'' : Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap (φ.sectionHom V)
        (P.affineDatum V) with
    | mk t' m' =>
      have : t = t' := funext fun n => by
        have := h n
        rwa [h', h''] at this
      subst this
      rfl

end Precomp

/-! ### Immersions of `r_{L, ψ}` and of its charts -/

/-- Being an immersion, for the chart of a datum of [Stacks, Tag 01NK] at a section, depends only
on the datum. -/
theorem isImmersion_toSpecAway_congr {R σ : Type u} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {M : T.Modules}
    [Stacks.Ample.IsInvertibleModule T M] {D D' : GradedSections 𝒜 M} (h : D = D') {g : R}
    (hg : g ∈ 𝒜 1) :
    IsImmersion ((D.homogeneousRatios hg le_rfl).toSpecAway one_pos) ↔
      IsImmersion ((D'.homogeneousRatios hg le_rfl).toSpecAway one_pos) := by
  subst h
  rfl

section Immersion

variable {S X : Scheme.{u}} {A B : SheafGradedAlgebra.{u} S} {f : X ⟶ S}

/-- **The charts of an immersion `r_{L, ψ}` at degree-one sections are immersions.** On the
nonvanishing open `X_{ψ(g)}` of a degree-one section `g` over an affine open `V` of the base,
`r_{L, ψ}` is the chart `X_{ψ(g)} ⟶ Spec B(V)_{(g)}` followed by the open immersions
`Spec B(V)_{(g)} = D₊(g) ⊆ Proj B(V) ⊆ Proj_S(B)`. -/
theorem isImmersion_toSpecAway_of_isImmersion (P : GradedPowerMap B f) (rp : RelativeProjData B)
    (hr : IsImmersion (P.globalMorphism rp)) {V : S.Opens} (hV : IsAffineOpen V)
    {g : B.sectionRing V} (hg : g ∈ B.grading V 1) :
    IsImmersion (((P.affineDatum V).homogeneousRatios hg le_rfl).toSpecAway one_pos) := by
  have h1 : IsImmersion (chartIncl P hV hg ≫ P.globalMorphism rp) := inferInstance
  rw [chartIncl_globalMorphism P rp hV hg] at h1
  have h2 : IsImmersion (((P.affineDatum V).homogeneousRatios hg le_rfl).toSpecAway one_pos ≫
      (AlgebraicGeometry.Proj.awayι (B.grading V) g hg one_pos ≫ rp.chart V hV)) := by
    simpa only [GradedSections.chartToProj, Stacks.MorphismToProj.HomogeneousRatios.chartToProj,
      Category.assoc] using h1
  exact IsImmersion.of_comp _ (AlgebraicGeometry.Proj.awayι (B.grading V) g hg one_pos ≫
    rp.chart V hV)

/-- **The charts of `r_{L, ψ ∘ φ}` at degree-one sections are immersions covering `X`.** Suppose
`r_{L, ψ}` is an immersion, `φ : A ⟶ B` is surjective on homogeneous sections of positive degree
over every affine open of the base, and every point of `X` lies in the nonvanishing open of the
value of `ψ ∘ φ` at some degree-one section over an affine open. Then the chart of `ψ ∘ φ` at that
section is the chart of `ψ` at its image, an immersion, followed by `Spec` of a surjection of
rings, a closed immersion. -/
theorem chartsAreImmersions_precomp (P : GradedPowerMap B f) (rp : RelativeProjData B)
    (hr : IsImmersion (P.globalMorphism rp)) (φ : SheafGradedAlgebraHom A B)
    (hφ : ∀ V : S.Opens, IsAffineOpen V → ∀ n : ℕ, 0 < n →
      Function.Surjective (φ.sectionPieceHom V n))
    (hgen : ∀ x : X, ∃ (V : S.Opens) (_ : IsAffineOpen V) (a : Γ(A.piece ((1 : ℕ) : ℤ), V)),
      x ∈ (P.precomp φ).nonvanishingOpenAt 1 V a) :
    ChartsAreImmersions (P.precomp φ) := by
  intro x
  obtain ⟨V, hV, a, hx⟩ := hgen x
  obtain ⟨g, rfl⟩ := (A.componentEquiv V 1).surjective a
  have hxV : f x ∈ V := (P.precomp φ).nonvanishingOpenAt_le_preimage 1 V _ hx
  have hx' : (⟨x, hxV⟩ : (f ⁻¹ᵁ V).toScheme) ∈
      ((P.precomp φ).affineDatum V).nonvanishingOpenAt 1 g := by
    rw [GradedPowerMap.nonvanishingOpenAt_affineDatum]
    exact hx
  refine ⟨V, hV, (g : A.sectionRing V), g.2, ⟨⟨x, hxV⟩, hx'⟩, rfl, ?_⟩
  have hsurj : ∀ n : ℕ, 0 < n → ∀ y ∈ B.grading V n, ∃ z ∈ A.grading V n,
      φ.sectionHom V z = y := by
    intro n hn y hy
    obtain ⟨b, hb⟩ := (B.mem_grading_iff V y).mp hy
    obtain ⟨c, hc⟩ := hφ V hV n hn b
    refine ⟨DirectSum.of (A.sectionPieces V) n c, ⟨c, rfl⟩, ?_⟩
    rw [SheafGradedAlgebraHom.sectionHom_of, ← hb]
    exact congrArg (DirectSum.of (B.sectionPieces V) n) hc
  have himm := isImmersion_toSpecAway_of_isImmersion P rp hr hV
    (map_mem (φ.sectionHom V) g.2)
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (HomogeneousLocalization.Away.map (φ.sectionHom V) (g : A.sectionRing V)))
    (surjective_awayMap (φ.sectionHom V) g.2 one_pos hsurj)
  have key : IsImmersion
      (((Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap (φ.sectionHom V)
        (P.affineDatum V)).homogeneousRatios g.2 le_rfl).toSpecAway one_pos) := by
    rw [toSpecAway_comap (φ.sectionHom V) (P.affineDatum V) g.2 one_pos]
    exact @IsImmersion.comp _ _ _ _ _ himm inferInstance
  exact (isImmersion_toSpecAway_congr (affineDatum_precomp P φ V) g.2).mpr key

end Immersion

end Stacks.Tag01VMVeryAmple

end
