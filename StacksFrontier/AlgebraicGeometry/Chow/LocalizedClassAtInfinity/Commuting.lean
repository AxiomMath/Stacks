module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Chern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectChernCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChernBivariantCommute
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Commuting
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized classes of Stacks 0F9K commute with every bivariant class (Stacks 0FAW)

Let `(S, δ)` be as in Situation 02QL and place ourselves in the situation of Stacks 0F9K: `X`
locally of finite type over `S`, `Z ⊆ X` a closed subscheme, `b : W ⟶ 𝐏¹_X` proper and an
isomorphism over `𝐀¹_X`, `Q ∈ D(𝒪_W)` perfect with defined Chern classes, and `T ⊆ W_∞` a closed
subscheme containing all points of `W_∞` over `X \ Z` on which `Q` is zero, resp. finite locally
free of rank `< p` in degree `0`. **Stacks 0FAW**: for `Y ⟶ X` locally of finite type and
`c ∈ A^*(Y ⟶ X)`,

  `P'_p(Q) ∘ c = c ∘ P'_p(Q)`   resp.   `c'_p(Q) ∘ c = c ∘ c'_p(Q)`   in `A^*(Y ×_X Z ⟶ X)`.

## The argument

The source's: `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C` with `E = W_∞ ×_X Z`. The class `C` of
Stacks 0F9J commutes with `c` (Stacks 0FAS); the class `c'_p(Q|_E)` of Stacks 0F9H commutes with
the restriction of `c` to `W_∞` (Stacks 0FAJ, whose input Stacks 0FAC is
`Stacks.Chow.TotalChowClass.commutesWith_perfectChernClass`); so their composite does
(`Stacks.Chow.bivariantCommute_of_isBivariantClassComposition`), and `c` commutes with the proper
pushforward along `E ⟶ Z` because it is bivariant
(`Stacks.Chow.bivariantCommute_of_isBivariantProperPushforward`).

## Main results

* `Stacks.Chow.bivariantCommute_closedCoverLocalizedClass_of_commutesWith` — the localized class
  of Stacks 0F9H of a class `x_p`, for a total class `x` commuting with `c`, commutes with `c`.
* `Stacks.Chow.GysinAtInfinity.bivariantCommute_localizedClassAtInfinityOf` — the class
  `(E ⟶ Z)_* ∘ κ' ∘ C` commutes with `c` when `κ` does.
* `Stacks.Chow.GysinAtInfinity.localizedPowerSumAtInfinity_comp_comm`,
  `Stacks.Chow.GysinAtInfinity.localizedChernClassAtInfinity_comp_comm` — **Stacks 0FAW**.

## References

* [Stacks Project, Tag 0FAW](https://stacks.math.columbia.edu/tag/0FAW)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0FAJ](https://stacks.math.columbia.edu/tag/0FAJ)
* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The localized class of a closed cover -/

section ClosedCover

variable (C : ChowSituation.{u}) {X X₁ X₂ Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (f : Y ⟶ X) [LocallyOfFiniteType f] {r : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl r)

/-- **Stacks 0FAC in the form Stacks 0FAJ consumes**: if a total class `x` of `X₂` commutes with
`c` along `i₂`, its degree-`p` component commutes with `c` in the sense of
`Stacks.Chow.ChowCohomologyCommutesWith`. -/
theorem chowCohomologyCommutesWith_of_commutesWith (x : TotalChowClass C (i₂ ≫ sX))
    (hx : x.CommutesWith C sX f c i₂ (i₂ ≫ sX) rfl) (p : ℕ) :
    ChowCohomologyCommutesWith C (gysinSystemOfInvertible C) sX i₂ f (p : ℤ) r (x p) c := by
  intro W v _ k γ
  have h := (TotalChowClass.commutesWith_iff C sX f c i₂ (i₂ ≫ sX) rfl x).1 hx v p k γ
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans (HEq.trans ?_
    (chowGroupCongr_heq C _ _ _).symm))
  refine HEq.trans ?_ (h.trans ?_)
  · exact (TotalChowClass.capAlong_heq C sX f c i₂ (i₂ ≫ sX) rfl v (k - p) _ _
      (chowGroupCongr_heq C _ _ _).symm).symm
  · refine TotalChowClass.op_heq_of_eq x rfl (k - r) p ?_
    exact (TotalChowClass.capAlong_heq C sX f c i₂ (i₂ ≫ sX) rfl v k γ _
      (chowGroupCongr_heq C _ _ _).symm).trans (chowGroupCongr_heq C _ _ _).symm

/-- **Stacks 0FAJ, as commuting in the sense of Remark 0FA2.** For `X = X₁ ∪ X₂` set
theoretically, a total class `x` of `X₂` commuting with `c` along `i₂` and `p` such that `x_p`
vanishes on `X₁ ∩ X₂`, the localized class `x_p' ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H commutes with `c`.

This is `Stacks.Chow.bivariantCommute_of_isClosedCoverLocalizedClass`, the source's proof, with
its inputs supplied: the commuting of `x_p` with `c` by
`Stacks.Chow.chowCohomologyCommutesWith_of_commutesWith`, and the two composites by the composite
classes of Stacks 0FE0. -/
theorem bivariantCommute_closedCoverLocalizedClass_of_commutesWith
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) (x : TotalChowClass C (i₂ ≫ sX))
    (hx : x.CommutesWith C sX f c i₂ (i₂ ≫ sX) rfl) (p : ℕ)
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) (p : ℤ)) (hκx : κ = x p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) (pullback.snd i₁ i₂)
      (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0) :
    BivariantCommute C (gysinSystemOfInvertible C) sX i₂ f (p : ℤ) r
      (closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ) c := by
  subst hκx
  exact bivariantCommute_of_isClosedCoverLocalizedClass C (gysinSystemOfInvertible C) sX i₁ i₂ f
      (p : ℤ)
      r (x p) _ c (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (properPushforwardDescends C) hcover
      (GysinAtInfinity.isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX (i₁ ≫ sX)
        (i₂ ≫ sX) i₁ rfl i₂ rfl hcover (x p) hκ)
      (chowCohomologyCommutesWith_of_commutesWith C sX i₂ f c x hx p) _ _
      (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)
      (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)

end ClosedCover

/-! ### Transports -/

section Transport

variable {C : ChowSituation.{u}} {G : GysinSystem C}

/-- Commuting does not see a transport of the degree of the first class. -/
theorem bivariantCommute_copy_degree {X Z₁ Z₂ : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {f₁ : Z₁ ⟶ X} [LocallyOfFiniteType f₁] {f₂ : Z₂ ⟶ X}
    [LocallyOfFiniteType f₂] {p₁ p₁' p₂ : ℤ} (hp : p₁ = p₁')
    {c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁}
    {c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂}
    (h : BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂) :
    BivariantCommute C G sX f₁ f₂ p₁' p₂ (BivariantClass.copy C G _ sX rfl rfl rfl hp c₁) c₂ := by
  subst hp
  exact h

/-- The class read along an equal morphism caps as the class does. -/
theorem bivariantClassCongrMor_cap_heq {X Z₁ : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {f₁ f₁' : Z₁ ⟶ X} [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₁']
    (hf : f₁ = f₁') (p : ℤ) (c : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (bivariantClassCongrMor C G sX hf p c).cap t k α ≍ c.cap t k α := by
  subst hf
  rfl

/-- The composite of Stacks 0FE0 commutes with a transport of the source structure morphism of
its first factor. -/
theorem bivariantCompositeOfInvertible_congrBase {A B D : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hA : sA = sA') (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (f : A ⟶ B)
    [LocallyOfFiniteType f] (g : B ⟶ D) [LocallyOfFiniteType g] (hf : f ≫ sB = sA)
    (hf' : f ≫ sB = sA') (hg : g ≫ sD = sB) (p q : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sA sB f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sB sD g hg q) :
    bivariantCompositeOfInvertible C sA' sB sD f g hf' hg p q
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) f hA rfl p a) b =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) (f ≫ g) hA rfl (p + q)
        (bivariantCompositeOfInvertible C sA sB sD f g hf hg p q a b) := by
  subst hA
  rfl

end Transport

namespace GysinAtInfinity

/-! ### The class `(E ⟶ Z)_* ∘ a ∘ C` -/

section Push

variable (C : ChowSituation.{u}) {X W Z Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (iZ : Z ⟶ X) [IsClosedImmersion iZ] (fY : Y ⟶ X) [LocallyOfFiniteType fY] {r : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl r)

/-- **`(E ⟶ Z)_* ∘ a ∘ C` commutes with `c`** as soon as `a ∈ A^p(E ⟶ W_∞)` commutes with the
restriction of `c` to `W_∞`: `C` commutes with `c` by Stacks 0FAS, so `a ∘ C` does by the
composite rule, and `c` commutes with the proper pushforward along `E ⟶ Z`. -/
theorem bivariantCommute_pushAtInfinity {p : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f))
      (modificationProjectionAtInfinity f b ≫ f) (preimageInclusion f b iZ) rfl p)
    (ha : BivariantCommute C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f)
      (preimageInclusion f b iZ) (pullback.snd fY (modificationProjectionAtInfinity f b)) p r a
      (bivariantRestrictionCommute C (gysinSystemOfInvertible C) f fY
        (modificationProjectionAtInfinity f b) r
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)) :
    BivariantCommute C (gysinSystemOfInvertible C) f iZ fY p r
      (pushAtInfinity C f b hA iZ (modificationProjectionAtInfinity f b ≫ f) rfl a) c := by
  have hfac : preimageInclusion f b iZ ≫ modificationProjectionAtInfinity f b =
      preimageProjection f b iZ ≫ iZ :=
    pullback.condition (f := modificationProjectionAtInfinity f b) (g := iZ)
  have hdK := bivariantCompositeOfInvertible_congrBase
    (Category.assoc (preimageInclusion f b iZ) (modificationProjectionAtInfinity f b) f).symm
    (modificationProjectionAtInfinity f b ≫ f) f (preimageInclusion f b iZ)
    (modificationProjectionAtInfinity f b) rfl (Category.assoc _ _ _).symm rfl p 0 a
    (classAtInfinityOf C f b hA (modificationProjectionAtInfinity f b ≫ f) rfl)
  have hC : BivariantCommute C (gysinSystemOfInvertible C) f
      (modificationProjectionAtInfinity f b) fY 0 r
      (classAtInfinityOf C f b hA (modificationProjectionAtInfinity f b ≫ f) rfl) c :=
    gysinAtInfinityClass_bivariantCommute C f b hA fY r
      (BivariantChowClass.equivBivariantClass.symm c)
  set d := bivariantCompositeOfInvertible C
    ((preimageInclusion f b iZ ≫ modificationProjectionAtInfinity f b) ≫ f)
    (modificationProjectionAtInfinity f b ≫ f) f (preimageInclusion f b iZ)
    (modificationProjectionAtInfinity f b) (Category.assoc _ _ _).symm rfl p 0
    (bivariantClassAssocSource C (gysinSystemOfInvertible C) f
      (modificationProjectionAtInfinity f b) (preimageInclusion f b iZ) p a)
    (classAtInfinityOf C f b hA (modificationProjectionAtInfinity f b ≫ f) rfl)
  set e := bivariantClassCongrMor C (gysinSystemOfInvertible C) f hfac p
    (BivariantClass.copy C (gysinSystemOfInvertible C) _ f rfl rfl rfl (add_zero p) d)
  have hd : BivariantCommute C (gysinSystemOfInvertible C) f
      (preimageInclusion f b iZ ≫ modificationProjectionAtInfinity f b) fY (p + 0) r d c :=
    bivariantCommute_of_isBivariantClassComposition C (gysinSystemOfInvertible C) f fY
    (modificationProjectionAtInfinity f b) (preimageInclusion f b iZ) p 0 r a c
    (classAtInfinityOf C f b hA (modificationProjectionAtInfinity f b ≫ f) rfl) _
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (properPushforwardDescends C)
    (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _) hC ha
  have hc₁ : BivariantCommute C (gysinSystemOfInvertible C) f
      (preimageProjection f b iZ ≫ iZ) fY p r e c :=
    bivariantCommute_congrMor C (gysinSystemOfInvertible C) f hfac fY p r _ c
      (bivariantCommute_copy_degree (add_zero p) hd)
  have hpush : IsBivariantProperPushforward C (gysinSystemOfInvertible C)
      ((preimageProjection f b iZ ≫ iZ) ≫ f) (iZ ≫ f) f (preimageProjection f b iZ) iZ
      (Category.assoc _ _ _).symm rfl (properPushforwardDescends C) p e
      (pushAtInfinity C f b hA iZ (modificationProjectionAtInfinity f b ≫ f) rfl a) := by
    intro T t _ k α
    rw [bivariantProperPushforwardCap_apply]
    unfold pushAtInfinity
    rw [canonicalBivariantProperPushforward_cap]
    refine eq_of_heq (properChowPushforward_heq_congr_base C _ ?_ rfl _ _ rfl _ _ _ _ ?_)
    · change pullback.fst (preimageProjection f b iZ ≫ iZ) t ≫
          (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f)) = _
      rw [← Category.assoc (preimageInclusion f b iZ), hfac, Category.assoc]
    · refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans ?_
      refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans ?_
      refine HEq.symm ((bivariantClassCongrMor_cap_heq f hfac p _ t k α).trans ?_)
      refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans ?_
      refine (heq_of_eq (congrArg (fun d ↦ d.cap t k α) hdK)).trans ?_
      exact bivariantClassCongrBase_cap C _ _ _ _ _ _ t k α α HEq.rfl
  intro T t _ k α
  exact bivariantCommute_of_isBivariantProperPushforward C (gysinSystemOfInvertible C) f iZ
    (preimageProjection f b iZ) fY (properPushforwardDescends C) p r _ c _ hpush hc₁ t k α

variable {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
  (hT : ∀ w : modificationFibreAtInfinity f b,
    (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)

/-- **The class `(E ⟶ Z)_* ∘ κ' ∘ C` of Stacks 0F9K commutes with `c`** when `κ` is the
degree-`p` component of a total class `x` of `E` commuting with every bivariant class over
`W_∞` along `E ⟶ W_∞`. -/
theorem bivariantCommute_localizedClassAtInfinityOf (p : ℕ)
    (x : TotalChowClass C (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f)))
    (hx : ∀ {Y' : Scheme.{u}} (g : Y' ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType g]
      {q : ℤ} (c' : BivariantClass C (gysinSystemOfInvertible C)
        (g ≫ (modificationProjectionAtInfinity f b ≫ f)) (modificationProjectionAtInfinity f b ≫ f)
        g rfl q),
      x.CommutesWith C (modificationProjectionAtInfinity f b ≫ f) g c' (preimageInclusion f b iZ)
        _ rfl)
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f)) (p : ℤ))
    (hκx : κ = x p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ (modificationProjectionAtInfinity f b ≫ f))
      (pullback.snd iT (preimageInclusion f b iZ)) (p : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0) :
    BivariantCommute C (gysinSystemOfInvertible C) f iZ fY (p : ℤ) r
      (localizedClassAtInfinityOf C f b hA iZ (modificationProjectionAtInfinity f b ≫ f) rfl iT
        hT κ hκ) c :=
  bivariantCommute_pushAtInfinity C f b hA iZ fY c _
    (bivariantCommute_closedCoverLocalizedClass_of_commutesWith C
      (modificationProjectionAtInfinity f b ≫ f) iT (preimageInclusion f b iZ)
      (pullback.snd fY (modificationProjectionAtInfinity f b)) _
      (range_union_range_preimageInclusion f b iZ iT hT) x (hx _ _) p κ hκx hκ)

end Push

/-! ### Stacks 0FAW -/

section Statement

variable (C : ChowSituation.{u}) {X W Z Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (iZ : Z ⟶ X) [IsClosedImmersion iZ] (Q : DerivedCategory W.Modules)
  {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
  (fY : Y ⟶ X) [LocallyOfFiniteType fY]

/-- `c'_p(Q)` commutes with every bivariant class `c ∈ A^r(Y ⟶ X)`, in the sense of
Remark 0FA2. -/
theorem bivariantCommute_localizedChernClassAtInfinity (hQ : HasDefinedChernClasses Q)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (p : ℕ)
    (hsmall : RestrictionIsLocallyFreeOfRankLT f b iT Q p)
    {r : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl r) :
    BivariantCommute C (gysinSystemOfInvertible C) f iZ fY (p : ℤ) r
      (localizedChernClassAtInfinity C hA iZ hQ hT hsmall) c := by
  rw [localizedChernClassAtInfinity_eq C f b hA iZ Q iT hQ p hT hsmall]
  exact bivariantCommute_localizedClassAtInfinityOf C f b hA iZ fY c iT hT p _
    (fun g _ _ c' ↦ TotalChowClass.commutesWith_perfectChernClass C _ g c' _ _ rfl _) _ rfl _

/-- `P'_p(Q)` commutes with every bivariant class `c ∈ A^r(Y ⟶ X)`, in the sense of
Remark 0FA2. -/
theorem bivariantCommute_localizedPowerSumAtInfinity
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (p : ℕ) (hzero : IsZero (restrictToInfinity C f b Q iT))
    {r : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl r) :
    BivariantCommute C (gysinSystemOfInvertible C) f iZ fY (p : ℤ) r
      (localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT hzero) c := by
  rw [localizedPowerSumClassAtInfinity_eq C f b hA iZ Q iT perfect hQ p hT hzero]
  exact bivariantCommute_localizedClassAtInfinityOf C f b hA iZ fY c iT hT p _
    (fun g _ _ c' ↦ TotalChowClass.commutesWith_perfectPowerSumTotal C _ g c' _ _ rfl
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
        (preimageInclusion f b iZ).toLRSHom.toShHom _
        (isPerfect_restrictionAtInfinity C f b perfect)) _) _
    (perfectPowerSumTotal_apply C _ _ p).symm _

/-- **Stacks 0FAW, for the classes `P'_p`.** Let `(S, δ)` be as in Situation 02QL, let `X` be
locally of finite type over `S`, let `Z ⊆ X` be a closed subscheme, let `b : W ⟶ 𝐏¹_X` be a
proper morphism which is an isomorphism over `𝐀¹_X` (A1), let `Q ∈ D(𝒪_W)` be perfect with
defined Chern classes (A0), and let `T ⊆ W_∞` be a closed subscheme containing all points of
`W_∞` lying over `X \ Z` with `Q|_T` zero (A2). Let `fY : Y ⟶ X` be locally of finite type and
`c ∈ A^r(Y ⟶ X)`. Then

  `P'_p(Q) ∘ c = c ∘ P'_p(Q)`   in   `A^{p+r}(Y ×_X Z ⟶ X)`,

where `P'_p(Q) ∈ A^p(Z ⟶ X)` is the class of Stacks 0F9K. As in Remark 0FA2 (and Stacks 0FAS),
`P'_p(Q) ∘ c = res(P'_p(Q)) ∘ c` with `res(P'_p(Q)) ∈ A^p(Z ×_X Y ⟶ Y)` the restriction along
`fY` (Remark 0F9Z), and `c ∘ P'_p(Q) = res(c) ∘ P'_p(Q)` with `res(c) ∈ A^r(Y ×_X Z ⟶ Z)`; the
second composite is read on `Z ×_X Y` through the canonical isomorphism and in degree `p + r`.
The bivariant classes are those of Stacks 0B76, `Stacks.Chow.BivariantChowClass`. -/
@[stacks 0FAW "the classes P'_p: P'_p(Q) ∘ c = c ∘ P'_p(Q) for every bivariant class c"]
theorem localizedPowerSumAtInfinity_comp_comm
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (p : ℕ) (hzero : IsZero (restrictToInfinity C f b Q iT)) {r : ℤ} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] (hY : fY ≫ f = sY) (c : BivariantChowClass C sY f fY hY r) :
    ((BivariantChowClass.equivBivariantClass.symm
        (localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT
          hzero)).restrict fY hY).comp c =
      (((c.restrict iZ rfl).comp (BivariantChowClass.equivBivariantClass.symm
          (localizedPowerSumClassAtInfinity (p := p) C hA iZ hQ perfect hT hzero))).degreeCongr
        (add_comm r (p : ℤ))).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl fY hY) hY)
        (pullbackSymmetry fY iZ) (pullbackSymmetry_hom_comp_snd_comp iZ fY) := by
  subst hY
  exact BivariantChowClass.restrict_comp_eq_of_bivariantCommute f iZ fY _ c
    (bivariantCommute_localizedPowerSumAtInfinity C f b hA iZ Q iT fY perfect hQ hT p hzero
      (BivariantChowClass.equivBivariantClass c))

/-- **Stacks 0FAW, for the classes `c'_p`.** Let `(S, δ)` be as in Situation 02QL, let `X` be
locally of finite type over `S`, let `Z ⊆ X` be a closed subscheme, let `b : W ⟶ 𝐏¹_X` be a
proper morphism which is an isomorphism over `𝐀¹_X` (A1), let `Q ∈ D(𝒪_W)` be perfect with
defined Chern classes (A0), and let `T ⊆ W_∞` be a closed subscheme containing all points of
`W_∞` lying over `X \ Z` with `Q|_T` isomorphic to a finite locally free `𝒪_T`-module of
rank `< p` sitting in cohomological degree `0` (A2). Let `fY : Y ⟶ X` be locally of finite type
and `c ∈ A^r(Y ⟶ X)`. Then

  `c'_p(Q) ∘ c = c ∘ c'_p(Q)`   in   `A^{p+r}(Y ×_X Z ⟶ X)`,

where `c'_p(Q) ∈ A^p(Z ⟶ X)` is the class of Stacks 0F9K, the composites being read as in
`Stacks.Chow.GysinAtInfinity.localizedPowerSumAtInfinity_comp_comm`. -/
@[stacks 0FAW "the classes c'_p: c'_p(Q) ∘ c = c ∘ c'_p(Q) for every bivariant class c"]
theorem localizedChernClassAtInfinity_comp_comm
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (p : ℕ)
    (hsmall : RestrictionIsLocallyFreeOfRankLT f b iT Q p)
    {r : ℤ} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] (hY : fY ≫ f = sY)
    (c : BivariantChowClass C sY f fY hY r) :
    ((BivariantChowClass.equivBivariantClass.symm
        (localizedChernClassAtInfinity C hA iZ hQ hT hsmall)).restrict fY hY).comp c =
      (((c.restrict iZ rfl).comp (BivariantChowClass.equivBivariantClass.symm
          (localizedChernClassAtInfinity C hA iZ hQ hT hsmall))).degreeCongr
        (add_comm r (p : ℤ))).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl fY hY) hY)
        (pullbackSymmetry fY iZ) (pullbackSymmetry_hom_comp_snd_comp iZ fY) := by
  subst hY
  exact BivariantChowClass.restrict_comp_eq_of_bivariantCommute f iZ fY _ c
    (bivariantCommute_localizedChernClassAtInfinity C f b hA iZ Q iT fY hQ hT p hsmall
      (BivariantChowClass.equivBivariantClass c))

end Statement

end GysinAtInfinity

end Stacks.Chow

end
