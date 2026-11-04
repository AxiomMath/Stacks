module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjFromSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGraded
public import StacksFrontier.AlgebraicGeometry.ProductFamilyRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers

/-!
# A chart of `r_{L, ψ}` through which an immersion into projective space factors is an immersion

Let `ψ : A → Γ_*(T, M)` be a graded map ([Stacks, Tag 01NK]) and `a₀, …, aₙ ∈ A₁` homogeneous of
degree one. On the nonvanishing open `T_{ψ(aᵢ)}` the chart of `r_{M, ψ}` is the morphism
`T_{ψ(aᵢ)} ⟶ Spec A_{(aᵢ)}` of the ring map `a / aᵢ^m ↦ ψ(a) / ψ(aᵢ)^m`. If the sections `ψ(a_k)`
are, up to an isomorphism of invertible modules, a family `t` whose pinned morphism
`p : T ⟶ ℙⁿ_B` is an immersion, then the chart followed by the morphism
`Spec A_{(aᵢ)} ⟶ ℙⁿ_B` of the ratios `a_k / aᵢ` is `p` on `T_{ψ(aᵢ)}`, so the chart is an
immersion by [Stacks, Tag 07RK] (`AlgebraicGeometry.IsImmersion.of_comp`).

This is the step of the proof of [Stacks, Tag 07RM] that reads "over `V_j` we have a
factorization `f⁻¹V_j → 𝐏(ℰ_i)|_{V_j} → 𝐏^{n_j}_{V_j}` of the immersion given above. It follows that
`r_{L, ψ_i}|_{V_j}` is an immersion", carried out on one chart of the projective bundle at a time:
on the chart `D₊(aᵢ)` the rational map to `𝐏^{n_j}` is defined, and it is the morphism of the
coordinate ratios.

## Main results

* `Stacks.QuasiProjectiveCompactification.toSpecAway_comp_eq`: the chart followed by the morphism
  of the ratios is `p` restricted.
* `Stacks.QuasiProjectiveCompactification.isImmersion_toSpecAway`: the chart is an immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.ProjChartFullGraded
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf ratioOf_eq_of_resTop_eq)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.QuasiProjectiveCompactification

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T B : Scheme.{u}} {M : T.Modules} [IsInvertibleModule T M]
  (ψ : GradedSections 𝒜 M) {N : T.Modules} [IsInvertibleModule T N] {n : ℕ}
  (Φ : natTensorPow M 1 ≅ N) (a : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1)) {W : T.Opens}
  (hW : W ≤ nonvanishingOpen T (natTensorPow M 1) (ψ.toFun 1 (a i)))

/-- The coordinate ratio `a_k / aᵢ` as an element of `A_{(aᵢ)}`. -/
def awayRatio (k : Fin (n + 1)) : HomogeneousLocalization.Away 𝒜 (a i : A) :=
  HomogeneousLocalization.Away.mk 𝒜 (a i).2 1 (a k : A) (by simp)

/-- `aᵢ / aᵢ = 1`. -/
theorem awayRatio_self : awayRatio a i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [awayRatio]
  simp [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]

/-- The coordinate ratios, as global sections of `Spec A_{(aᵢ)}`. -/
def specRatio (k : Fin (n + 1)) : Γ(Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜
    (a i : A))), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (a i : A)))).inv
    (awayRatio a i k)

/-- The coordinate ratios generate the unit ideal, since among them is `aᵢ / aᵢ = 1`. -/
theorem span_range_specRatio : Ideal.span (Set.range (specRatio a i)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : specRatio a i i = 1 := by rw [specRatio, awayRatio_self, map_one]
  exact h ▸ Ideal.subset_span ⟨i, rfl⟩

include hW in
/-- **The ratio `ψ(a_k) / ψ(aᵢ)` is the ratio `t_k / tᵢ`** of the transported family, on any open
where `ψ(aᵢ)` does not vanish. -/
theorem ratioOf_eq_resO_ratio (t : Fin (n + 1) → Γ(N, ⊤))
    (hΦ : ∀ k, Φ.hom.app ⊤ (ψ.toFun 1 (a k)) = t k) (hWt : W ≤ nvCover t i) (k : Fin (n + 1)) :
    ratioOf M (ψ.toFun 1 (a i)) hW (ψ.toFun 1 (a k)) = resO hWt (ratio t i k) := by
  refine ratioOf_eq_of_resTop_eq M _ hW ?_
  apply (ConcreteCategory.bijective_of_isIso (Φ.hom.app W)).1
  have hn : ∀ x : Γ(natTensorPow M 1, ⊤),
      Φ.hom.app W (Stacks.TensorPowerTrivialize.resTop (natTensorPow M 1) x W)
        = resT W (Φ.hom.app ⊤ x) := fun x =>
    (PresheafOfModules.naturality_apply Φ.hom.val (homOfLE (le_top : W ≤ ⊤)).op x)
  rw [Scheme.Modules.Hom.app_smul, hn, hn, hΦ, hΦ, resO_ratio_smul t hWt k]

/-- The morphism `Spec A_{(aᵢ)} ⟶ ℙⁿ_B` of the coordinate ratios `a_k / aᵢ`, over a given morphism
`Spec A_{(aᵢ)} ⟶ B`. -/
def ratioHom (b : Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (a i : A))) ⟶ B) :
    Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (a i : A))) ⟶
      projectiveSpaceOver n B :=
  pullback.lift b
    (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (specRatio a i)
      (span_range_specRatio a i))
    (terminal.hom_ext _ _)

include hW in
/-- **The chart of `r_{M, ψ}` at `aᵢ`, followed by the morphism of the coordinate ratios, is the
pinned morphism `p` on `T_{ψ(aᵢ)}`.** The components over `B` agree by hypothesis; the components
to `ℙⁿ_ℤ` are the morphisms of two families of functions on `T_{ψ(aᵢ)}`, by the naturality of
that construction, and the two families are the ratios `ψ(a_k) / ψ(aᵢ)` and `t_k / tᵢ`, which
agree because `Φ` carries one family of sections to the other. -/
theorem toSpecAway_comp_ratioHom (t : Fin (n + 1) → Γ(N, ⊤))
    (hΦ : ∀ k, Φ.hom.app ⊤ (ψ.toFun 1 (a k)) = t k) (hWt : W ≤ nvCover t i)
    (g : T ⟶ B) (p : T ⟶ projectiveSpaceOver n B)
    (hpf : p ≫ pullback.fst (terminal.from B)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = g)
    (hchart : (nvCover t i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n B =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio t i)
        (span_range_chartRatio t i))
    (b : Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (a i : A))) ⟶ B)
    (hb : (ψ.homogeneousRatios (a i).2 hW).toSpecAway one_pos ≫ b = W.ι ≫ g) :
    (ψ.homogeneousRatios (a i).2 hW).toSpecAway one_pos ≫ ratioHom a i b =
      T.homOfLE hWt ≫ (nvCover t i).ι ≫ p := by
  apply pullback.hom_ext
  · rw [Category.assoc, ratioHom, pullback.lift_fst, hb, Category.assoc, Category.assoc, hpf,
      ← Category.assoc, Scheme.homOfLE_ι]
  · rw [Category.assoc, ratioHom, pullback.lift_snd]
    have hR := congrArg (fun q => T.homOfLE hWt ≫ q) hchart
    rw [Category.assoc, Category.assoc]
    show _ = T.homOfLE hWt ≫ (nvCover t i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n B
    rw [hR, Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _
        (Stacks.SectionsToProjectiveSpace.span_range_comp _ _ (span_range_specRatio a i)),
      Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _
        (Stacks.SectionsToProjectiveSpace.span_range_comp _ _ (span_range_chartRatio t i))]
    apply Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr
    funext k
    have h1 := ConcreteCategory.congr_hom
      (Stacks.MorphismToProj.HomogeneousRatios.toSpecAway_appTop
        (ψ.homogeneousRatios (a i).2 hW) one_pos) (awayRatio a i k)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [specRatio, h1, chartRatio, homOfLE_appTop_topIso_inv]
    congr 1
    rw [awayRatio, GradedSections.lift_mk ψ (a i).2 hW one_pos 1 (a k : A) _ ⟨(a k : A), by
      simp⟩ rfl]
    rw [← ratioOf_eq_resO_ratio ψ Φ a i hW t hΦ hWt k]
    exact ψ.ratioOf_congr _ _ (a i).2 (a k).2 _ hW (by simp) (pow_one _) rfl

omit [IsInvertibleModule T N] in
/-- The nonvanishing open of `ψ(aᵢ)` is that of its image `tᵢ` under `Φ`. -/
theorem nonvanishingOpen_eq_nvCover [IsInvertibleModule T N] (t : Fin (n + 1) → Γ(N, ⊤))
    (hΦ : ∀ k, Φ.hom.app ⊤ (ψ.toFun 1 (a k)) = t k) :
    nonvanishingOpen T (natTensorPow M 1) (ψ.toFun 1 (a i)) = nvCover t i := by
  refine TopologicalSpace.Opens.ext ?_
  show _ = Stacks.Ample.nonvanishingLocus N (t i)
  rw [← hΦ i]
  exact (Stacks.Ample.nonvanishingLocus_congr Φ _).symm

include hW in
/-- **The chart of `r_{M, ψ}` at `aᵢ` is an immersion** as soon as the transported family `t` pins
an immersion `p : T ⟶ ℙⁿ_B` and the chart lies over `B` compatibly: by
`Stacks.QuasiProjectiveCompactification.toSpecAway_comp_ratioHom` its composite with the morphism
of the coordinate ratios is `p` on an open, which is an immersion, and [Stacks, Tag 07RK]
(`AlgebraicGeometry.IsImmersion.of_comp`) cancels the second factor. -/
theorem isImmersion_toSpecAway (t : Fin (n + 1) → Γ(N, ⊤))
    (hΦ : ∀ k, Φ.hom.app ⊤ (ψ.toFun 1 (a k)) = t k)
    (g : T ⟶ B) (p : T ⟶ projectiveSpaceOver n B) (hp : IsImmersion p)
    (hpf : p ≫ pullback.fst (terminal.from B)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = g)
    (hchart : (nvCover t i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n B =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio t i)
        (span_range_chartRatio t i))
    (b : Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (a i : A))) ⟶ B)
    (hb : (ψ.homogeneousRatios (a i).2 hW).toSpecAway one_pos ≫ b = W.ι ≫ g) :
    IsImmersion ((ψ.homogeneousRatios (a i).2 hW).toSpecAway one_pos) := by
  have hWt : W ≤ nvCover t i := hW.trans (nonvanishingOpen_eq_nvCover ψ Φ a i t hΦ).le
  have := hp
  have : IsImmersion ((ψ.homogeneousRatios (a i).2 hW).toSpecAway one_pos ≫ ratioHom a i b) := by
    rw [toSpecAway_comp_ratioHom ψ Φ a i hW t hΦ hWt g p hpf hchart b hb]
    infer_instance
  exact IsImmersion.of_comp _ (ratioHom a i b)

end Stacks.QuasiProjectiveCompactification

end
