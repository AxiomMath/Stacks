module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.DefinedChernTensor
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedComposite
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseCommute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.CommonModification

/-!
# The classes `C(r, n)` of localized ranks

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be closed and let `E ∈ D(𝒪_X)` be perfect with `E|_{X ∖ Z}`
zero. The rank `r = P_0(Z ⟶ X, E)` is the class of the locally constant function
`χ_E : x ↦ χ(E ⊗^L κ(x))`, which vanishes off `Z`, and the binomial coefficients `C(r, n)` of the
formula for `c_2` in Stacks 0FBF are the classes in `A^0(Z ⟶ X)` of `x ↦ C(χ_E(x), n)`
(`Stacks.Chow.LocalizedChernData.rankChoose`). This file relates them to the construction of
Stacks 0F9K.

Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with class `C ∈ A^0(W_∞ ⟶ X)` of
Stacks 0F9J, and let `Q ∈ D(𝒪_W)` and `T ⊆ W_∞` be as in Stacks 0F9K, with
`Q|_{b^{-1}(𝐀¹_X)}` the pullback of `E`. The class `C(r', n) ∈ A^0(W_∞ ×_X Z ⟶ W_∞)` of
Stacks 0FE5 for `Q|_{W_∞}` localizes to `C(r, n)`. The argument: `χ_Q = χ_E ∘ π` on the open and
closed subscheme `U ⊆ W` where the two locally constant functions agree, which contains
`b^{-1}(𝐀¹_X)`; by the second assertion of Stacks 0FAU the localization may be computed on `U`;
there the class of `C(χ_Q, n)` is pulled back from `X`, and its localization is characterized
along the closed cover `X = {C(χ_E, n) = 0} ∪ Z` (Stacks 0F9H) by the identity
`(Z ⟶ X)_* ∘ q' = q|_{X × {0}}` of Stacks 0F9K and by vanishing over `{C(χ_E, n) = 0}`.

For `n = 1` this gives `r = C(r, 1)`, for the classes of Stacks 0FB2 and of Remark 0GUK.

## Main results

* `Stacks.Chow.LocalizedChernData.modificationLocalization_closedCoverRankChoose` — the
  localization of `C(r', n)` is `C(r, n)`.
* `Stacks.Chow.LocalizedChernData.localizedModificationClass_eq_rankChoose` — the localized
  class of the class of `C(χ_Q, n)` is `C(r, n)`.
* `Stacks.Chow.localizedModificationClass_ofLocallyConstant_eq` — the localized class of the
  class of a locally constant function `m` on `W` with `m = n ∘ π` over `𝐀¹_X` is the class of `n`.
* `Stacks.Chow.modificationLocalization_capVanishesOver` — a localization caps to zero over a
  closed subscheme of `X` when the class does over its inverse image in `W_∞`.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum_zero_eq_rankChoose_one`,
  `Stacks.Chow.LocalizedChernData.localizedPowerSum_zero_eq_rankChoose_one` — `r = C(r, 1)`.

## Implementation notes

The function `χ_Q` need not equal `χ_E ∘ π` on all of `W`: a component of `W` lying over `∞`
carries no constraint. The class at infinity does not see such components, and the reduction to
the open and closed subscheme `U` is how this enters.

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0FAG](https://stacks.math.columbia.edu/tag/0FAG)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

section Capping

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- **A localization caps to zero over `X₁` when the class does over `W_∞ ×_X X₁`.** Let
`a ∈ A^m(E ⟶ W_∞)`, `E = W_∞ ×_X Y`, cap to zero over the inverse image `W_∞ ×_X X₁ ⟶ W_∞` of
`X₁ ⟶ X`. Then its localization `(E ⟶ Y)_* ∘ a ∘ C` caps to zero over `X₁`: on a class pushed
forward from a scheme over `X₁`, the class at infinity `C` produces, by proper naturality, a class
pushed forward from a scheme over `W_∞ ×_X X₁`, which `a` kills. -/
theorem modificationLocalization_capVanishesOver (y : Y ⟶ X) [IsClosedImmersion y] {m : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m)
    {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X)
    (ha : a.CapVanishesOver (pullback.fst (modificationProjectionAtInfinity f b) i₁)) :
    (modificationLocalization C f b hA y a).CapVanishesOver i₁ := by
  intro T T₀ g _ e _ mm hm sT₀ _ he k γ
  set π := modificationProjectionAtInfinity f b
  rw [modificationLocalization_cap,
    BivariantClass.cap_chowPush_eq (gysinAtInfinityClass C f b hA) g e he
      (sB := pullback.fst π (e ≫ g) ≫ (π ≫ f)) rfl k γ]
  have hc : pullback.fst π (e ≫ g) ≫ π = (pullback.snd π (e ≫ g) ≫ mm) ≫ i₁ := by
    rw [pullback.condition, Category.assoc, hm]
  have hm' : pullback.lift _ _ hc ≫ pullback.fst π i₁ =
      bivariantBaseChangeMap π g e ≫ pullback.fst π g := by
    rw [pullback.lift_fst, bivariantBaseChangeMap_fst]
  rw [ha (pullback.fst π g) (bivariantBaseChangeMap π g e) (pullback.lift _ _ hc) hm', map_zero,
    map_zero]

end Capping


section Core

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (z : Z ⟶ X) [IsClosedImmersion z]

/-- The class of a locally constant function vanishes over every morphism on whose image the
function vanishes. -/
theorem vanishesOver_ofLocallyConstant {Y V : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    (j : V ⟶ Y) [LocallyOfFiniteType j] (m : LocallyConstant Y ℤ) (hm : ∀ v, m (j.base v) = 0) :
    BivariantClass.VanishesOver (TotalChowClass.ofLocallyConstant C sY m 0) j := by
  rw [← chowCohomologyRestriction_eq_zero_iff_vanishesOver, ← TotalChowClass.res_rfl_apply,
    TotalChowClass.res_ofLocallyConstant _ _ _ 0 hm, Int.cast_zero]
  rfl

/-- **The localized class of a pulled back locally constant function.** Let `n` be a locally
constant function on `X` vanishing off `Z`, and let `q ∈ A^0(W)` be the class of `n ∘ π`, where
`π : W ⟶ X`. Then the localized class `q'` of Stacks 0F9K is the class of `n` in `A^0(Z ⟶ X)`
(`Stacks.Chow.supportedOfLocallyConstant`). Both are extensions along the closed cover
`X = {n = 0} ∪ Z` (Stacks 0F9H): `q'` caps classes from `Z` as `n` does, because
`(Z ⟶ X)_* ∘ q'` is the restriction of `q` to `X × {0}` (Stacks 0F9K), which is the class of `n`;
and `q'` kills classes from `{n = 0}`, because over `{n = 0}` the class `q` vanishes, so that
`(q|_E)'` kills the classes from the inverse image of `{n = 0}` in `W_∞`. -/
theorem localizedModificationClass_eq_supportedOfLocallyConstant (n : LocallyConstant X ℤ)
    (hn : ∀ x, x ∉ Set.range z → n x = 0) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
      ((0 : ℕ) : ℤ)}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hqe : q = TotalChowClass.ofLocallyConstant C (modificationProjection f b ≫ f)
      (n.comap (modificationProjection f b).base.hom) 0) :
    localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq =
      supportedOfLocallyConstant C f z (z ≫ f) rfl n hn := by
  subst hqe
  set π := modificationProjectionAtInfinity f b
  set t₀ := (TotalChowClass.levelSets (n.comap π.base.hom) (ULift.up 0)).ι
  have : IsClosedImmersion t₀ := isClosedImmersion_levelSets_zero_ι _
  have hT₀ : ∀ w, π w ∉ Set.range z → w ∈ Set.range t₀ := fun w hw ↦ by
    rw [Scheme.Opens.range_ι]
    exact hn _ hw
  have hq₀ : BivariantClass.VanishesOver (TotalChowClass.ofLocallyConstant C
      (modificationProjection f b ≫ f) (n.comap (modificationProjection f b).base.hom) 0)
      (t₀ ≫ modificationInclusionAtInfinity f b) :=
    vanishesOver_ofLocallyConstant C _ _ fun v ↦ by
      have hv : n (π (t₀ v)) = 0 := v.2
      exact hv
  rw [localizedModificationClass_eq _ z t t₀ hT hT₀ hq hq₀]
  set i₁ := (TotalChowClass.levelSets n (ULift.up 0)).ι
  have : IsClosedImmersion i₁ := isClosedImmersion_levelSets_zero_ι n
  have hcover : Set.range i₁ ∪ Set.range z = Set.univ := range_levelSets_zero_union_eq_univ hn
  have hva : BivariantClass.VanishesOver
      (TotalChowClass.res z rfl (TotalChowClass.ofLocallyConstant C f n) 0) (pullback.snd i₁ z) :=
    vanishesOver_res_ofLocallyConstant_of_eq C f i₁ rfl fun y ↦ y.2
  set D := gysinAtInfinityData C f b hA
  have hs₀ : ∀ x, (modificationProjection f b) (modificationSectionAtZero f b D.isIsoFibreAtZero x)
      = x := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, D.sectionAtZero_comp]
    rfl
  have hext : IsClosedCoverExtension C (gysinSystemOfInvertible C) f i₁ z (z ≫ f) rfl
      (TotalChowClass.res z rfl (TotalChowClass.ofLocallyConstant C f n) 0)
      (localizedModificationClass D z t₀ hT₀ hq₀) := by
    refine isClosedCoverExtension_of_capVanishesOver i₁ (fun g _ k α ↦ ?_) ?_
    · refine BivariantClass.cap_chowPush_pullbackSnd_of_isRestriction _ ?_ g k α
      have hn' : (n.comap (modificationProjection f b).base.hom).comap
          (modificationSectionAtZero f b D.isIsoFibreAtZero).base.hom = n :=
        LocallyConstant.ext fun x ↦ congrArg n (hs₀ x)
      rw [properPushforwardChowCohomology_localizedModificationClass,
        ← TotalChowClass.res_apply_eq_bivariantClassCongrBase,
        show ∀ hs, TotalChowClass.res (modificationSectionAtZero f b D.isIsoFibreAtZero) hs
          (TotalChowClass.ofLocallyConstant C (modificationProjection f b ≫ f)
            (n.comap (modificationProjection f b).base.hom)) =
            TotalChowClass.ofLocallyConstant C f n from fun hs ↦ by
          rw [TotalChowClass.res_ofLocallyConstant_comap, hn']]
      exact TotalChowClass.isRestriction_res (TotalChowClass.ofLocallyConstant C f n) z rfl 0
    · rw [localizedModificationClass_eq_modificationLocalization]
      refine modificationLocalization_capVanishesOver C f b hA z _ i₁ ?_
      have h₀ := (isClosedCoverExtension_closedCoverExtension C (π ≫ f) t₀ (pullback.fst π z) _
        rfl (range_union_range_pullbackFst_eq_univ z t₀ hT₀)
        (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t₀ _
          (hq₀.chowCohomologyRestriction_modificationInclusionAtInfinity t₀))).capVanishesOver
      refine BivariantClass.CapVanishesOver.of_range_subset t₀ t₀ _ ?_ h₀ h₀
      rintro w ⟨v, rfl⟩
      left
      rw [Scheme.Opens.range_ι]
      change n (π (pullback.fst π i₁ v)) = 0
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact (pullback.snd π i₁ v).2
  exact hext.eq_closedCoverExtension hcover hva

/-- **The localized class of a locally constant function agreeing with `n ∘ π` over `𝐀¹_X`.** Let
`n` be a locally constant function on `X` vanishing off `Z`, and let `m` be a locally constant
function on `W` with `m = n ∘ π` on `b^{-1}(𝐀¹_X)`. Then the localized class of Stacks 0F9K of the
class of `m` is the class of `n` in `A^0(Z ⟶ X)`.

The two functions agree on the open and closed subscheme `U = {m = n ∘ π}` of `W`, which contains
`b^{-1}(𝐀¹_X)`, so `U ⟶ W ⟶ 𝐏¹_X` is again proper and an isomorphism over `𝐀¹_X`. By the generic
form of the second assertion of Stacks 0FAU the localized class may be computed on `U`, where
`m = n ∘ π` and `Stacks.Chow.localizedModificationClass_eq_supportedOfLocallyConstant` applies.
The function `m` need not equal `n ∘ π` on all of `W`: components of `W` lying entirely over
`∞` are not seen by the class at infinity. -/
theorem localizedModificationClass_ofLocallyConstant_eq (n : LocallyConstant X ℤ)
    (hn : ∀ x, x ∉ Set.range z → n x = 0) (m : LocallyConstant W ℤ)
    (hm : ∀ w ∈ Set.range (pullback.fst b (projectiveLineAffineChart f)),
      m w = n (modificationProjection f b w)) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
      ((0 : ℕ) : ℤ)}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hqe : q = TotalChowClass.ofLocallyConstant C (modificationProjection f b ≫ f) m 0) :
    localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq =
      supportedOfLocallyConstant C f z (z ≫ f) rfl n hn := by
  subst hqe
  -- the open and closed subscheme `U ⊆ W` on which `m = n ∘ π`
  set d : LocallyConstant W ℤ := m - n.comap (modificationProjection f b).base.hom
  set U := TotalChowClass.levelSets d (ULift.up 0)
  have : IsClosedImmersion U.ι := isClosedImmersion_levelSets_zero_ι d
  have hmU : ∀ w : U, m (U.ι w) = n (modificationProjection f b (U.ι w)) := fun w ↦ by
    have : d (U.ι w) = 0 := w.2
    exact sub_eq_zero.1 this
  have hrange : Set.range (pullback.fst b (projectiveLineAffineChart f)) ⊆ Set.range U.ι := by
    rintro w hw
    rw [Scheme.Opens.range_ι]
    change d w = 0
    exact sub_eq_zero.2 (hm w hw)
  have hι : IsIso (pullback.snd U.ι (pullback.fst b (projectiveLineAffineChart f))) := by
    rw [← (IsOpenImmersion.isPullback_lift_id _ U.ι hrange).isoPullback_inv_snd,
      Category.comp_id]
    infer_instance
  have hA' := isIso_pullbackSnd_comp_projectiveLineAffineChart f b U.ι hA hι
  set b' := U.ι ≫ b
  have hs : U.ι ≫ (modificationProjection f b ≫ f) = modificationProjection f b' ≫ f := by
    simp only [b', modificationProjection, Category.assoc]
  have hqe : TotalChowClass.res U.ι hs
      (TotalChowClass.ofLocallyConstant C (modificationProjection f b ≫ f) m) 0 =
      TotalChowClass.ofLocallyConstant C (modificationProjection f b' ≫ f)
        (n.comap (modificationProjection f b').base.hom) 0 := by
    rw [TotalChowClass.res_ofLocallyConstant_comap]
    have : m.comap U.ι.base.hom = n.comap (modificationProjection f b').base.hom :=
      LocallyConstant.ext fun w ↦ hmU w
    rw [this]
  set q' := TotalChowClass.res U.ι hs
    (TotalChowClass.ofLocallyConstant C (modificationProjection f b ≫ f) m) 0
  set t' := (TotalChowClass.levelSets
    (n.comap (modificationProjectionAtInfinity f b').base.hom) (ULift.up 0)).ι
  have : IsClosedImmersion t' := isClosedImmersion_levelSets_zero_ι _
  have hT' : ∀ w, modificationProjectionAtInfinity f b' w ∉ Set.range z → w ∈ Set.range t' :=
    fun w hw ↦ by
      rw [Scheme.Opens.range_ι]
      exact hn _ hw
  have hq' : BivariantClass.VanishesOver q' (t' ≫ modificationInclusionAtInfinity f b') := by
    rw [hqe]
    exact vanishesOver_ofLocallyConstant C (t' ≫ modificationInclusionAtInfinity f b')
      (n.comap (modificationProjection f b').base.hom) fun v ↦ v.2
  rw [← localizedModificationClass_eq_of_modification z hA U.ι rfl hA' t t' hT hT' hq hq'
    fun y _ _ k γ γ' h ↦ TotalChowClass.isRestriction_res _ U.ι hs 0 y k γ γ' h]
  exact localizedModificationClass_eq_supportedOfLocallyConstant C f b' hA' z n hn t' hT' hq' hqe

end Core

section RankChoose

namespace LocalizedChernData

variable (D : LocalizedChernData.{u}) (h : D.IsZeroOnComplement) {W : Scheme.{u}}
  (b : W ⟶ projectiveLineProduct D.a) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart D.a)))
  {Q : DerivedCategory W.Modules} (hQ : RingedSpace.IsPerfect.{u, u + 1} Q)
  (e : Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst b (projectiveLineAffineChart D.a)).toLRSHom.toShHom).obj Q ≅
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst b (projectiveLineAffineChart D.a) ≫
        modificationProjection D.a b).toLRSHom.toShHom).obj D.E))

omit [IsProper b] in
include e in
/-- If `Q|_{b^{-1}(𝐀¹_X)}` is the pullback of `E`, the rank of `Q` at a point of `b^{-1}(𝐀¹_X)` is
the rank of `E` at its image in `X`: the Euler characteristic of the derived fibre commutes with
base change. -/
theorem perfectRank_eq_perfectRank_modificationProjection :
    ∀ w ∈ Set.range (pullback.fst b (projectiveLineAffineChart D.a)),
      perfectRank Q hQ w = perfectRank D.E D.perfect (modificationProjection D.a b w) := by
  rintro w ⟨v, rfl⟩
  set u := pullback.fst b (projectiveLineAffineChart D.a)
  have hpcQ := DerivedFibreBetti.isPseudoCoherent_of_isPerfect Q hQ
  have hpcE := DerivedFibreBetti.isPseudoCoherent_of_isPerfect D.E D.perfect
  have h₁ := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback u Q hpcQ) v
  have h₂ := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback
    (u ≫ modificationProjection D.a b) D.E hpcE) v
  have h₃ := congrFun (DerivedFibreBetti.chiDerivedFibre_congr
    (Limits.pullback b (projectiveLineAffineChart D.a))
    (DerivedFibreBetti.isPseudoCoherent_derivedPullback u Q hpcQ)
    (DerivedFibreBetti.isPseudoCoherent_derivedPullback (u ≫ modificationProjection D.a b) D.E
      hpcE) e.some) v
  exact h₁.symm.trans (h₃.trans h₂)

include e in
/-- **The localized class of `C(χ_Q, n)` is `C(r, n)`.** Let `b : W ⟶ 𝐏¹_X`, `Q` and `T` be as in
Stacks 0F9K for `(X, Z, E)` with `E|_{X ∖ Z}` zero, with `Q|_{b^{-1}(𝐀¹_X)}` the pullback of `E`.
The localized class of the class of `x ↦ C(χ_Q(x), n)` is the class
`C(r, n) ∈ A^0(Z ⟶ X)` of `Stacks.Chow.LocalizedChernData.rankChoose`. -/
theorem localizedModificationClass_eq_rankChoose (n : ℕ) (hn : 0 < n) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t]
    (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
    {q : chowCohomologyComponent D.base (gysinSystemOfInvertible D.base)
      (modificationProjection D.a b ≫ D.a) ((0 : ℕ) : ℤ)}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity D.a b))
    (hqe : q = TotalChowClass.ofLocallyConstant D.base (modificationProjection D.a b ≫ D.a)
        ((perfectRank Q hQ).map fun k ↦ Ring.choose k n) 0) :
    localizedModificationClass (gysinAtInfinityData D.base D.a b hA) D.i t hT hq =
      D.rankChoose h n hn :=
  localizedModificationClass_ofLocallyConstant_eq D.base D.a b hA D.i _
    (D.rankChoose_eq_zero_of_isZeroOnComplement h hn) _ (fun w hw ↦ by
      rw [LocallyConstant.map_apply, LocallyConstant.map_apply, Function.comp_apply,
        Function.comp_apply, D.perfectRank_eq_perfectRank_modificationProjection b hQ e w hw])
    t hT hq hqe

include e in
/-- **The localization of `C(r', n)` on `W_∞` is `C(r, n)`.** Let `b : W ⟶ 𝐏¹_X`, `Q` and `T` be as
in Stacks 0F9K for `(X, Z, E)` with `E|_{X ∖ Z}` zero and `Q|_T` zero, with
`Q|_{b^{-1}(𝐀¹_X)}` the pullback of `E`. Then the localization
`(E' ⟶ Z)_* ∘ C(r', n) ∘ C ∈ A^0(Z ⟶ X)` of the class `C(r', n) ∈ A^0(E' ⟶ W_∞)` of Stacks 0FE5
for `Q|_{W_∞}` along the closed cover `W_∞ = T ∪ E'`, `E' = W_∞ ×_X Z`
(`Stacks.Chow.closedCoverRankChoose`), is the class `C(r, n)` of
`Stacks.Chow.LocalizedChernData.rankChoose`, `r = P_0(Z ⟶ X, E)`. This is how the terms `C(r_i, 2)`
of the formula for `c_2` in Stacks 0FBF arise from those of Stacks 0FE5. -/
theorem modificationLocalization_closedCoverRankChoose (n : ℕ) (hn : 0 < n) {T : Scheme.{u}}
    (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t]
    (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity D.a b).toLRSHom.toShHom).obj Q)) :
    modificationLocalization D.base D.a b hA D.i
        (closedCoverRankChoose D.base (modificationProjectionAtInfinity D.a b ≫ D.a) t
          (pullback.fst (modificationProjectionAtInfinity D.a b) D.i)
          (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q hQ)
          (range_union_range_pullbackFst_eq_univ D.i t hT)
          (isZero_derivedPullback_inclusionAtInfinity D.base D.a b hzero) n hn) =
      D.rankChoose h n hn := by
  set π := modificationProjectionAtInfinity D.a b
  set ι := modificationInclusionAtInfinity D.a b
  set E := pullback.fst π D.i
  set N : ℤ → ℤ := fun k ↦ Ring.choose k n
  have hq : BivariantClass.VanishesOver
      (TotalChowClass.ofLocallyConstant D.base (modificationProjection D.a b ≫ D.a)
        ((perfectRank Q hQ).map N) 0) (t ≫ ι) :=
    vanishesOver_ofLocallyConstant _ _ _ fun v ↦ by
      rw [LocallyConstant.map_apply, Function.comp_apply,
        perfectRank_eq_zero_of_isZero hQ (t ≫ ι) hzero v]
      exact Ring.choose_zero_pos ℤ hn
  rw [← D.localizedModificationClass_eq_rankChoose h b hA hQ e n hn t hT hq rfl,
    localizedModificationClass_eq_modificationLocalization]
  congr 1
  -- the two classes restricted to `E` agree
  have hs : ι ≫ (modificationProjection D.a b ≫ D.a) = π ≫ D.a := (Category.assoc _ _ _).symm
  have hm : (perfectRank ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      ι.toLRSHom.toShHom).obj Q)
        (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q hQ)).map N =
      ((perfectRank Q hQ).map N).comap ι.base.hom := by
    refine LocallyConstant.ext fun w ↦ ?_
    have := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback ι Q
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect Q hQ)) w
    exact congrArg N this
  have ha : TotalChowClass.res E rfl (TotalChowClass.ofLocallyConstant D.base (π ≫ D.a)
      ((perfectRank ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        ι.toLRSHom.toShHom).obj Q)
        (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q hQ)).map N)) 0 =
      Stacks.Chow.chowCohomologyRestriction D.base (gysinSystemOfInvertible D.base) (π ≫ D.a) E
        ((0 : ℕ) : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
        (Stacks.Chow.chowCohomologyRestriction D.base (gysinSystemOfInvertible D.base)
          (modificationProjection D.a b ≫ D.a) ι ((0 : ℕ) : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
          (TotalChowClass.ofLocallyConstant D.base (modificationProjection D.a b ≫ D.a)
            ((perfectRank Q hQ).map N) 0)) := by
    rw [hm, ← TotalChowClass.res_ofLocallyConstant_comap ι hs]
    refine BivariantClass.eq_of_idRule_eq _ _ _ _ _ fun g _ k α ↦ eq_of_heq ?_
    have h1 := chowCohomologyRestriction_idRule D.base (π ≫ D.a) E
      (Stacks.Chow.chowCohomologyRestriction D.base (gysinSystemOfInvertible D.base)
          (modificationProjection D.a b ≫ D.a) ι ((0 : ℕ) : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
          (TotalChowClass.ofLocallyConstant D.base (modificationProjection D.a b ≫ D.a)
            ((perfectRank Q hQ).map N) 0)) g k α
    have h2 := chowCohomologyRestriction_idRule D.base (modificationProjection D.a b ≫ D.a) ι
      (TotalChowClass.ofLocallyConstant D.base (modificationProjection D.a b ≫ D.a)
        ((perfectRank Q hQ).map N) 0) (g ≫ E) k
      (chowGroupCongr D.base (Category.assoc g E (π ≫ D.a)).symm k α)
    refine ((TotalChowClass.isRestriction_res _ E rfl 0 g k α _
      (chowGroupCongr_heq _ (Category.assoc g E (π ≫ D.a)).symm k α).symm).trans
      ((TotalChowClass.isRestriction_res _ ι hs 0 (g ≫ E) k _ _
        ((chowGroupCongr_heq _ (by simp only [π, ι, Category.assoc]) _ _).symm)).trans ?_)).trans
      (heq_of_eq h1.symm)
    exact heq_of_eq h2.symm
  unfold closedCoverRankChoose modificationExtension
  have key : ∀ {a a' : chowCohomologyComponent D.base (gysinSystemOfInvertible D.base)
      (E ≫ π ≫ D.a) ((0 : ℕ) : ℤ)} (_ : a = a') (hv hv'), closedCoverExtension D.base (π ≫ D.a) t E
        (E ≫ π ≫ D.a) rfl a (range_union_range_pullbackFst_eq_univ D.i t hT) hv =
      closedCoverExtension D.base (π ≫ D.a) t E (E ≫ π ≫ D.a) rfl a'
        (range_union_range_pullbackFst_eq_univ D.i t hT) hv' := by
    intro a a' h' _ _
    subst h'
    rfl
  exact key ha _ _

/-- **`r = C(r, 1)` for the classes of Stacks 0FB2.** In Situation 0GUJ with `E|_{X ∖ Z}` zero, the
rank `r = P_0(Z ⟶ X, E)` is the class `C(r, 1)`. -/
theorem _root_.Stacks.Chow.LocalizedSituation.localizedPowerSum_zero_eq_rankChoose_one
    (S : LocalizedSituation.{u}) (h : S.IsZeroOnComplement) :
    S.localizedPowerSum h 0 = S.toLocalizedChernData.rankChoose h 1 one_pos := by
  have := isProper_graphBlowupToBase S.a S.E S.perfect
  have := isClosedImmersion_graphZeroLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
  have : IsClosedImmersion ((graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology).ι ≫ S.graphSubschemeι) :=
    IsClosedImmersion.comp _ _
  have hA := isIso_pullback_snd_graphBlowupToBase S.a S.E S.perfect
  have hQ := isPerfect_graphObject S.base S.a S.E S.perfect
  have e := nonempty_derivedPullback_graphObject S.a S.E S.perfect
    (pullback.fst (graphBlowupToBase S.a S.E S.perfect) (projectiveLineAffineChart S.a))
    fun v ↦ ⟨pullback.snd (graphBlowupToBase S.a S.E S.perfect) (projectiveLineAffineChart S.a) v,
      by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
  unfold LocalizedSituation.localizedPowerSum
    graphPowerSumClass modificationPowerSum
  refine S.toLocalizedChernData.localizedModificationClass_eq_rankChoose h
    (graphBlowupToBase S.a S.E S.perfect) hA hQ e 1 one_pos _ _
    (vanishesOver_perfectPowerSumClass_of_isZero S.base _ _ S.hasDefinedChernClasses_graphObject 0
      (isZero_derivedPullback_graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
        S.isFiniteLocallyFree_graphObjectRestrictHomology)) ?_
  rw [perfectPowerSumComponent, perfectPowerSum_zero_eq_ofLocallyConstant _ _ _ hQ]
  congr 2
  exact LocallyConstant.ext fun w ↦ by simp

/-- **`r = C(r, 1)`** for the classes of Remark 0GUK: for `E|_{X ∖ Z}` zero, the rank
`r = P_0(Z ⟶ X, E)` is the class `C(r, 1)`. -/
theorem localizedPowerSum_zero_eq_rankChoose_one (hE : HasDefinedChernClasses D.E) :
    D.localizedPowerSum hE h 0 = D.rankChoose h 1 one_pos := by
  set H := hE.some
  have hgys : (gysinSystemOfInvertible D.base).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base
  refine bivariantRestrictionAddHom_injective_of_isEnvelope' D.base _ _ _ _ _ H.f _ hgys
    H.envelope ?_
  refine (bivariantClassCongrBase D.base (gysinSystemOfInvertible D.base) (pullback.snd D.i H.f)
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f).symm rfl
    (hv := pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f)
    (hv' := rfl) _).injective ?_
  rw [bivariantRestrictionAddHom_apply, bivariantRestrictionAddHom_apply,
    D.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum hE H.f H.envelope
      (D.exists_isLocallyBoundedFiniteLocallyFree_envelope H) h 0,
    D.bivariantClassCongrBase_bivariantRestriction_rankChoose h H.f 1 one_pos]
  exact LocalizedSituation.localizedPowerSum_zero_eq_rankChoose_one
    ((D.pullback H.f).toSituation (D.exists_isLocallyBoundedFiniteLocallyFree_envelope H))
    (IsZeroOnComplement.pullback h)

end LocalizedChernData

end RankChoose

end Stacks.Chow

end
