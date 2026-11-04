module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Additivity

/-!
# The Whitney sum formula: Stacks 02UI

For a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of modules on a scheme `X` locally of finite
type over the base of chapter 42, with `ℰ₁`, `ℰ₂` finite locally free of ranks `r₁`, `r₂`, the
total Chern classes of the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6]
satisfy

  `c(ℰ) = c(ℰ₁) c(ℰ₂)`

in the ring of graded cap families on the Chow groups of `X`. This is [Stacks, Tag 02UI].

The source's induction on `r₁` is `Stacks.Chow.whitneyChernRelation_of_hasChernSplitting`, for
an arbitrary family of cap rules; this file supplies its two inputs for the cap products of
Stacks 02U6. The relation for `r₁ ≤ 1` is the case of a vanishing sub-module and Stacks 02UH
(`Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact_of_isInvertible`). The splitting
datum is the projective bundle `π : P(ℰ₁) ⟶ X`: `π^*` is injective on Chow groups by the top
half of Stacks 02TW (`Stacks.Chow.GenuineChern.pullback_injective`) and commutes with the cap
products by Stacks 02U8 (`Stacks.Chow.GenuineChern.intertwines_chernFamily`), the tautological
quotient `π^*ℰ₁ ⟶ 𝒪(1)` has a kernel `ℱ` of rank `r₁ - 1`, and with `𝒬 = π^*ℰ/ℱ` the sequences
`0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒬 ⟶ 0` and `0 ⟶ 𝒪(1) ⟶ 𝒬 ⟶ π^*ℰ₂ ⟶ 0` are exact
(`Stacks.Chow.GenuineChern.exists_shortExact_pair`). The middle term is finite locally free of
rank `r₁ + r₂` by `Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact`.

## Main results

* `Stacks.Chow.GenuineChern.whitneyChernRelation_chernCap_of_le_one` — the relation for a
  sub-module of rank at most one.
* `Stacks.Chow.GenuineChern.hasChernSplitting_chernCap` — the splitting datum.
* `Stacks.Chow.GenuineChern.whitneyChernRelation_chernCap` — the relation at every rank.
* `Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact` — **Stacks 02UI**.

## References

* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- **The Whitney relation when the sub-module has rank at most one.** In rank zero the
sub-module vanishes and the quotient map is an isomorphism; in rank one the sub-module is
invertible and the relation is
`Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact_of_isInvertible`. -/
theorem whitneyChernRelation_chernCap_of_le_one (r₁ : ℕ) (hr₁ : r₁ ≤ 1) :
    WhitneyChernRelation C (chernCap C) r₁ := by
  intro T q _ S hS r₂ h₁ h₂ h₃
  rcases r₁ with _ | _ | r₁
  · have hz : IsZero S.X₁ := Stacks.WeilCohomology.isZero_of_isFiniteLocallyFreeOfRank_zero _ h₁
    have : IsIso S.g := hS.isIso_g_iff.2 hz
    show chernFamily C q S.X₂ (0 + r₂) = chernFamily C q S.X₁ 0 * chernFamily C q S.X₃ r₂
    rw [chernFamily_of_rank_zero C q S.X₁, one_mul]
    exact chernFamily_congr C q S.X₃ r₂ (asIso S.g) (by omega)
  · have := isInvertible_of_rank_one S.X₁
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (r₂ + 1) :=
      rank_of_iso (Iso.refl _) (by omega) h₂
    show chernFamily C q S.X₂ (0 + 1 + r₂) =
      chernFamily C q S.X₁ (0 + 1) * chernFamily C q S.X₃ r₂
    rw [chernFamily_congr C q S.X₂ (r₂ + 1) (Iso.refl _) (by omega)]
    exact chernFamily_eq_mul_of_shortExact_of_isInvertible C q S hS r₂
  · omega

/-- **The splitting datum of the source's induction exists**: the projective bundle `P(ℰ₁)` of the
sub-module, with its flat pullback injective on Chow groups (the top half of Stacks 02TW) and
compatible with the Chern class cap products (Stacks 02U8), the tautological sequence
`0 ⟶ ℱ ⟶ π^*ℰ₁ ⟶ 𝒪(1) ⟶ 0`, and the two sequences `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒬 ⟶ 0` and
`0 ⟶ 𝒪(1) ⟶ 𝒬 ⟶ π^*ℰ₂ ⟶ 0`. -/
theorem hasChernSplitting_chernCap : HasChernSplitting C (chernCap C) := by
  intro T q _ S hS n r₂ h₁ h₂ h₃
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁ :=
    isFiniteLocallyFree_of_rank S.X₁ (n + 1 + 1)
  have := flat_bundleProj S.X₁ (n + 1)
  have := locallyOfFiniteType_bundleProj S.X₁ (n + 1)
  have : S.X₁.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree S.X₁
  have hd := relativeDimension_bundleProj S.X₁ (n + 1)
  -- the tautological sequence `0 ⟶ ℱ ⟶ π^*ℰ₁ ⟶ 𝒪(1) ⟶ 0`
  let τ : (Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₁ ⟶ bundleTwist S.X₁ :=
    Stacks.ProjectiveBundleSplitting.tautologicalMap S.X₁ (bundlePieces S.X₁)
  have hτ : Epi τ :=
    Stacks.ProjectiveBundleSplitting.epi_tautologicalMap S.X₁ (bundlePieces S.X₁)
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle S.X₁).presheaf
      (bundle S.X₁).ringCatSheaf.2 (bundleTwist S.X₁) := isInvertible_bundleTwist S.X₁
  have hπA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₁) (n + 1 + 1) :=
    isFiniteLocallyFreeOfRank_pullback _ S.X₁ _
  have hK : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel τ) (n + 1) :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
      τ hτ hL (n + 1) hπA
  have hO : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (bundleTwist S.X₁) 1 := by
    have : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle S.X₁).sheaf.obj
        (bundle S.X₁).ringCatSheaf.property (bundleTwist S.X₁) := hL
    exact isFiniteLocallyFreeOfRank_one_of_isInvertible _
  let T1 : ShortComplex (bundle S.X₁).Modules :=
    ShortComplex.mk (kernel.ι τ) τ (kernel.condition τ)
  have hT1 : T1.ShortExact := { exact := ShortComplex.exact_kernel τ }
  -- the pulled-back sequence and the two sequences of the step
  have hS' : (S.map (Scheme.Modules.pullback (bundleProj S.X₁))).ShortExact :=
    shortExact_map_pullback _ S hS
  obtain ⟨T2, T3, hT2, hT3, ⟨e21⟩, ⟨e22⟩, ⟨e23⟩, ⟨e31⟩, ⟨e33⟩⟩ :=
    exists_shortExact_pair T1 _ hT1 hS' (Iso.refl _)
  have e21' : T2.X₁ ≅ kernel τ := e21
  have e22' : T2.X₂ ≅ (Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₂ := e22
  have e31' : T3.X₁ ≅ bundleTwist S.X₁ := e31
  have e33' : T3.X₃ ≅ (Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₃ := e33
  have hπB := isFiniteLocallyFreeOfRank_pullback (bundleProj S.X₁) S.X₂ (n + 1 + 1 + r₂)
  have r22 := rank_of_iso e22'.symm (show n + 1 + 1 + r₂ = n + 1 + (1 + r₂) by omega) hπB
  have r22' := rank_of_iso e22'.symm rfl hπB
  have r31 := rank_of_iso e31'.symm rfl hO
  have r33 := rank_of_iso e33'.symm rfl
    (isFiniteLocallyFreeOfRank_pullback (bundleProj S.X₁) S.X₃ r₂)
  have r32 := isFiniteLocallyFreeOfRank_of_shortExact T3 hT3 1 r₂ r31 r33
  -- the sequences with shared terms
  have hmk : ∀ (T : ShortComplex (bundle S.X₁).Modules), T.ShortExact →
      ∀ {A B : (bundle S.X₁).Modules} (e : T.X₁ ≅ A) (e' : T.X₃ ≅ B),
      (ShortComplex.mk (e.inv ≫ T.f) (T.g ≫ e'.hom) (by simp)).ShortExact := fun T hT _ _ e e' =>
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk e (Iso.refl _) e' (by simp) (by simp)) hT
  have hfac := fun k => flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj S.X₁ ≫ q) q (bundleProj S.X₁) rfl (n + 1 + 1 - 1) hd k
  have compatMid := intertwines_chernFamily C q S.X₂ (n + 1 + 1 + r₂) (bundleProj S.X₁ ≫ q)
    (bundleProj S.X₁) rfl (n + 1 + 1 - 1) hd T2.X₂ e22'
  rw [← chernFamily_congr C (bundleProj S.X₁ ≫ q) T2.X₂ (n + 1 + 1 + r₂) (Iso.refl _)
    (show n + 1 + (1 + r₂) = n + 1 + 1 + r₂ by omega)] at compatMid
  exact ⟨{
    P := bundle S.X₁
    sP := bundleProj S.X₁ ≫ q
    proj := bundleProj S.X₁
    base_comp := rfl
    relDim := n + 1 + 1 - 1
    has_relDim := hd
    flat_factors := hfac
    pullback_injective := pullback_injective q S.X₁ (topHalf C) (n + 1)
    F := kernel τ
    L := bundleTwist S.X₁
    pullSub := (Scheme.Modules.pullback (bundleProj S.X₁)).obj S.X₁
    pullMid := T2.X₂
    Q := T3.X₂
    pullQuot := T3.X₃
    rankF := hK
    rankL := hO
    rankPullSub := hπA
    rankPullMid := r22
    rankQ := rank_of_iso (Iso.refl _) rfl r32
    rankPullQuot := r33
    fSub := kernel.ι τ
    gSub := τ
    wSub := kernel.condition τ
    exactSub := hT1
    fMid := e21'.inv ≫ T2.f
    gMid := T2.g ≫ e23.hom
    wMid := by simp
    exactMid := hmk T2 hT2 e21' e23
    fQuot := e31'.inv ≫ T3.f
    gQuot := T3.g ≫ (Iso.refl _).hom
    wQuot := by simp
    exactQuot := hmk T3 hT3 e31' (Iso.refl _)
    compatSub := intertwines_chernFamily C q S.X₁ (n + 1 + 1) (bundleProj S.X₁ ≫ q)
      (bundleProj S.X₁) rfl (n + 1 + 1 - 1) hd _ (Iso.refl _)
    compatMid := compatMid
    compatQuot := intertwines_chernFamily C q S.X₃ r₂ (bundleProj S.X₁ ≫ q)
      (bundleProj S.X₁) rfl (n + 1 + 1 - 1) hd T3.X₃ e33' }⟩

/-- **The Whitney relation at every rank of the sub-module**, by the source's induction on the
rank (`Stacks.Chow.whitneyChernRelation_of_hasChernSplitting`), whose two inputs are
`Stacks.Chow.GenuineChern.whitneyChernRelation_chernCap_of_le_one` and
`Stacks.Chow.GenuineChern.hasChernSplitting_chernCap`. -/
theorem whitneyChernRelation_chernCap (r₁ : ℕ) : WhitneyChernRelation C (chernCap C) r₁ :=
  whitneyChernRelation_of_hasChernSplitting C (chernCap C)
    (whitneyChernRelation_chernCap_of_le_one C) (hasChernSplitting_chernCap C) r₁

/-- **Stacks 02UI, on the Chern class cap products.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of modules on `X` with `ℰ₁`, `ℰ₂` finite locally free of ranks `r₁`,
`r₂` (so that `ℰ` is finite locally free of rank `r₁ + r₂`), the total Chern classes satisfy

  `c(ℰ) = c(ℰ₁) c(ℰ₂)`

in the ring of graded cap families on the Chow groups of `X`: for every `k`, every
`α ∈ A_k(X)` and every `m`, `c_m(ℰ) ∩ α = ∑_{i + j = m} c_i(ℰ₁) ∩ (c_j(ℰ₂) ∩ α)`. -/
theorem chernFamily_eq_mul_of_shortExact {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (S : ShortComplex X.Modules) (exact_S : S.ShortExact) (r₁ r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] :
    haveI := isFiniteLocallyFreeOfRank_of_shortExact S exact_S r₁ r₂ ‹_› ‹_›
    chernFamily C sX S.X₂ (r₁ + r₂) = chernFamily C sX S.X₁ r₁ * chernFamily C sX S.X₃ r₂ :=
  have := isFiniteLocallyFreeOfRank_of_shortExact S exact_S r₁ r₂ ‹_› ‹_›
  whitneyChernRelation_chernCap C r₁ sX S exact_S r₂

end Stacks.Chow.GenuineChern

end
