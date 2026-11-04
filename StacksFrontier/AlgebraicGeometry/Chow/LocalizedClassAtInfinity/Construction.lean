module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ProperModification
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ClosedCoverLocalizedClass
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernGysinCommute

/-!
# The class `(E ⟶ Z)_* ∘ κ' ∘ C` of Stacks 0F9K

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let `Z ⊆ X` be
a closed subscheme and let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre
at infinity `W_∞`. Let `E = W_∞ ×_X Z` be the inverse image of `Z` in `W_∞` and let `T ⊆ W_∞` be
a closed subscheme containing every point of `W_∞` lying over `X \ Z`, so that `W_∞ = T ∪ E`.

For a Chow cohomology class `κ ∈ A^p(E)` vanishing on `T ∩ E`, Stacks 0F9H gives the localized
class `κ' ∈ A^p(E ⟶ W_∞)` of the cover `W_∞ = T ∪ E`, and Stacks 0F9J gives the class
`C ∈ A⁰(W_∞ ⟶ X)`. The construction of Stacks 0F9K is

  `(E ⟶ Z)_* ∘ κ' ∘ C ∈ A^p(Z ⟶ X)`,

the proper pushforward of Stacks 0EPK of the composite of Stacks 0B75. Taking for `κ` the class
`P_p(Q|_E)`, resp. `c_p(Q|_E)`, of a perfect object `Q` on `W` gives `P'_p(Q)`, resp. `c'_p(Q)`
(see `StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Chern`).

## Main definitions

* `Stacks.Chow.GysinAtInfinity.pushAtInfinity` — the class `(E ⟶ Z)_* ∘ a ∘ C` for any
  `a ∈ A^p(E ⟶ W_∞)`.
* `Stacks.Chow.GysinAtInfinity.localizedClassAtInfinityOf` — the class
  `(E ⟶ Z)_* ∘ κ' ∘ C` of Stacks 0F9K, with `κ'` the localized class of Stacks 0F9H.

## Main results

* `Stacks.Chow.GysinAtInfinity.pushAtInfinity_isLocalizedClassAtInfinity` — the cap formula of
  the construction: on a test scheme it is "cap with `C`, cap with `a`, push forward along the
  base change of `E ⟶ Z`".

## Implementation notes

The structure morphism `W_∞ ⟶ S` is a parameter `sW` equal to `W_∞ ⟶ X ⟶ S` rather than that
composite itself. The canonical choice is the composite; the freedom is what lets the class of
a modification `W' ⟶ W` be compared with the restriction of Remark 0F9Z, whose structure
morphisms are the composites through `W'_∞ ⟶ W_∞`. The class does not depend on the choice
(`Stacks.Chow.GysinAtInfinity.localizedClassAtInfinityOf_congr`).

## References

* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Changing the structure morphism of the source -/

/-- A bivariant class for `f : X ⟶ Y`, read against a structure morphism of `X` equal to the
given one. -/
def BivariantClass.congrSource {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX sX' : X ⟶ C.S} [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (h : sX = sX') (hf' : f ≫ sY = sX') (c : BivariantClass C G sX sY f hf p) :
    BivariantClass C G sX' sY f hf' p := by
  subst h
  exact c

/-- Capping with `c.congrSource h hf'` is capping with `c`, followed by the identification of
Chow groups induced by `h`. -/
theorem BivariantClass.congrSource_cap {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX sX' : X ⟶ C.S} [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
    {hf : f ≫ sY = sX} {p : ℤ} (h : sX = sX') (hf' : f ≫ sY = sX')
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (c.congrSource h hf').cap t k α = chowGroupCongr C (by rw [h]) (k - p) (c.cap t k α) := by
  subst h
  rfl

namespace GysinAtInfinity

/-! ### The class `(E ⟶ Z)_* ∘ a ∘ C` -/

section Push

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  (sW : modificationFibreAtInfinity f b ⟶ C.S) [LocallyOfFiniteType sW]
  (hsW : modificationProjectionAtInfinity f b ≫ f = sW)

/-- The class `C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J, read against the structure morphism `sW`. -/
def classAtInfinityOf :
    BivariantClass C (gysinSystemOfInvertible C) sW f (modificationProjectionAtInfinity f b) hsW
      0 :=
  (gysinAtInfinityClass C f b hA).congrSource hsW hsW

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] [LocallyOfFiniteType sW] in
include hsW in
/-- `E ⟶ Z ⟶ X ⟶ S` is the structure morphism `E ⟶ W_∞ ⟶ S`. -/
theorem preimageProjection_comp_structure :
    preimageProjection f b iZ ≫ (iZ ≫ f) = preimageInclusion f b iZ ≫ sW := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, hsW]

/-- The degree-`p` class `a ∘ C ∈ A^p(E ⟶ X)`, for `a ∈ A^p(E ⟶ W_∞)`. -/
def compAtInfinity {p : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW) sW
      (preimageInclusion f b iZ) rfl p) :
    BivariantClass C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW) f
      (preimageInclusion f b iZ ≫ modificationProjectionAtInfinity f b)
      (comp_comp_structureMorphism_eq rfl hsW) p :=
  BivariantClass.copy C _ _ _ rfl _ _ (add_zero p)
    (bivariantCompositeOfInvertible C (preimageInclusion f b iZ ≫ sW) sW f
      (preimageInclusion f b iZ) (modificationProjectionAtInfinity f b) rfl hsW p 0 a
      (classAtInfinityOf C f b hA sW hsW))

/-- **The class `(E ⟶ Z)_* ∘ a ∘ C ∈ A^p(Z ⟶ X)`** of a class `a ∈ A^p(E ⟶ W_∞)`: the proper
pushforward (Stacks 0EPK) along `E ⟶ Z` of the composite (Stacks 0B75) of `a` with the class
`C` of Stacks 0F9J. -/
def pushAtInfinity {p : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW) sW
      (preimageInclusion f b iZ) rfl p) :
    BivariantClass C (gysinSystemOfInvertible C) (iZ ≫ f) f iZ rfl p :=
  canonicalBivariantProperPushforward C (preimageInclusion f b iZ ≫ sW) (iZ ≫ f) f
    (preimageProjection f b iZ) iZ (preimageProjection_comp_structure C f b iZ sW hsW) rfl p
    (BivariantClass.copy C (canonicalGysinSystem C) _ _ pullback.condition _ _ rfl
      (compAtInfinity C f b hA iZ sW hsW a))

/-- The base change `E ×_{W_∞} (W_∞ ×_X T) ⟶ Z ×_X T` of `E ⟶ Z` along a test scheme `t`. -/
def infinityPreimageBaseChange {T : Scheme.{u}} (t : T ⟶ X) :
    pullback (preimageInclusion f b iZ) (pullback.fst (modificationProjectionAtInfinity f b) t) ⟶
      pullback iZ t :=
  (pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) t
      (preimageInclusion f b iZ)).hom ≫
    (pullback.congrHom pullback.condition rfl).hom ≫
      bivariantPushforwardBaseChange (preimageProjection f b iZ) iZ t

/-- The base change `E ×_{W_∞} (W_∞ ×_X T) ⟶ Z ×_X T` of `E ⟶ Z` is proper. -/
instance isProper_infinityPreimageBaseChange {T : Scheme.{u}} (t : T ⟶ X) :
    IsProper (infinityPreimageBaseChange C f b iZ t) := by
  unfold infinityPreimageBaseChange
  infer_instance

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] in
/-- The base change of `E ⟶ Z` followed by the projection to `Z` is the projection to `E`
followed by `E ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageBaseChange_fst {T : Scheme.{u}} (t : T ⟶ X) :
    infinityPreimageBaseChange C f b iZ t ≫ pullback.fst iZ t =
      pullback.fst _ _ ≫ preimageProjection f b iZ := by
  simp [infinityPreimageBaseChange]

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] in
/-- The base change of `E ⟶ Z` commutes with the projections to the test scheme `T`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageBaseChange_snd {T : Scheme.{u}} (t : T ⟶ X) :
    infinityPreimageBaseChange C f b iZ t ≫ pullback.snd iZ t =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp [infinityPreimageBaseChange]

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] [LocallyOfFiniteType sW] in
include hsW in
/-- The base change of `E ⟶ Z` is compatible with the structure morphisms to `S`, those of
`Z ×_X T` and of `E ×_{W_∞} (W_∞ ×_X T)` being taken through `Z ⟶ X ⟶ S` and `E ⟶ W_∞ ⟶ S`. -/
theorem infinityPreimageBaseChange_comp {T : Scheme.{u}} (t : T ⟶ X) :
    infinityPreimageBaseChange C f b iZ t ≫ (pullback.fst iZ t ≫ (iZ ≫ f)) =
      pullback.fst (preimageInclusion f b iZ)
          (pullback.fst (modificationProjectionAtInfinity f b) t) ≫
        (preimageInclusion f b iZ ≫ sW) := by
  rw [infinityPreimageBaseChange_fst_assoc, preimageProjection_comp_structure C f b iZ sW hsW]

/-- **The cap formula of `(E ⟶ Z)_* ∘ a ∘ C`**: it is the factorization of Stacks 0F9K, read on
the cap operation of every test scheme. -/
theorem pushAtInfinity_isLocalizedClassAtInfinity {p : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW) sW
      (preimageInclusion f b iZ) rfl p) :
    IsLocalizedClassAtInfinity C (gysinSystemOfInvertible C) f sW
      (preimageInclusion f b iZ ≫ sW) iZ (modificationProjectionAtInfinity f b) hsW
      (preimageInclusion f b iZ) rfl p (fun t _ ↦ infinityPreimageBaseChange C f b iZ t)
      (fun _t _ ↦ inferInstance) (fun t _ ↦ infinityPreimageBaseChange_comp C f b iZ sW hsW t)
      (classAtInfinityOf C f b hA sW hsW) a (pushAtInfinity C f b hA iZ sW hsW a) := by
  intro T t _ k α
  set q := preimageInclusion f b iZ ≫ modificationProjectionAtInfinity f b
  set m : pullback q t ⟶ pullback iZ t :=
    (pullback.congrHom pullback.condition rfl).hom ≫
      bivariantPushforwardBaseChange (preimageProjection f b iZ) iZ t with hm
  have hm₁ : m ≫ pullback.fst iZ t = pullback.fst q t ≫ preimageProjection f b iZ := by
    simp [hm]
    rfl
  have hm₂ : m ≫ pullback.snd iZ t = pullback.snd q t := by
    simp [hm]
    rfl
  have hms : m ≫ (pullback.fst iZ t ≫ (iZ ≫ f)) =
      pullback.fst q t ≫ (preimageInclusion f b iZ ≫ sW) := by
    rw [← Category.assoc, hm₁, Category.assoc, preimageProjection_comp_structure C f b iZ sW hsW]
  unfold pushAtInfinity
  rw [canonicalBivariantProperPushforward_copy_cap C (preimageInclusion f b iZ ≫ sW) (iZ ≫ f) f
    (preimageProjection f b iZ) iZ q pullback.condition
    (preimageProjection_comp_structure C f b iZ sW hsW) rfl
    (comp_comp_structureMorphism_eq rfl hsW) p
    (compAtInfinity C f b hA iZ sW hsW a) t m hm₁ hm₂ hms k α]
  have hcomp : (compAtInfinity C f b hA iZ sW hsW a).cap t k α =
      chowGroupDegreeEquiv C _ (by ring : k - 0 - p = k - p)
        (properChowPushforward C
          (pullback.fst (preimageInclusion f b iZ)
            (pullback.fst (modificationProjectionAtInfinity f b) t) ≫
              (preimageInclusion f b iZ ≫ sW))
          (pullback.fst q t ≫ (preimageInclusion f b iZ ≫ sW))
          (pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) t
            (preimageInclusion f b iZ)).hom
          (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ t) (k - 0 - p)
          (properPushforwardDescends C _ _ _ _ _)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) t) (k - 0)
            ((classAtInfinityOf C f b hA sW hsW).cap t k α))) :=
    eq_of_heq ((BivariantClass.copy_cap C _ _ _ rfl _ _ (add_zero p) _ t k α).trans
      ((chowGroupDegreeEquiv_heq C _ (by ring : k - 0 - p = k - (p + 0)) _).trans
        (chowGroupDegreeEquiv_heq C _ (by ring : k - 0 - p = k - p) _).symm))
  rw [hcomp, ← chowGroupDegreeEquiv_properChowPushforward_comp C _ _ m hms _
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  refine congrArg (chowGroupDegreeEquiv C _ _) ?_
  exact (properChowPushforward_comp_apply C _ _ _ _ m _ rfl _ hms _ (k - 0 - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).symm

end Push

/-! ### The class of Stacks 0F9K attached to a class on `E` -/

/-- The localized class of Stacks 0F9H satisfies the characterizing property of Stacks 0F9H in
the form `Stacks.Chow.IsClosedCoverLocalizedClass` in which Stacks 0FAH is stated. -/
theorem isClosedCoverLocalizedClass_closedCoverLocalizedClass (C : ChowSituation.{u})
    {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sX₁ : X₁ ⟶ C.S)
    [LocallyOfFiniteType sX₁] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (i₁ : X₁ ⟶ X)
    [IsClosedImmersion i₁] (hi₁ : i₁ ≫ sX = sX₁) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
    (hi₂ : i₂ ≫ sX = sX₂) (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ (pullback.snd i₁ i₂) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0) :
    IsClosedCoverLocalizedClass C (gysinSystemOfInvertible C) sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ p κ
      (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ) :=
  ⟨fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_left C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂
      hcover κ hκ g k α,
    fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_right C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂
      hcover κ hκ g k α⟩

section Localized

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  (sW : modificationFibreAtInfinity f b ⟶ C.S) [LocallyOfFiniteType sW]
  (hsW : modificationProjectionAtInfinity f b ≫ f = sW)
  {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
  (hT : ∀ w : modificationFibreAtInfinity f b,
    (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
  {p : ℤ} (κ : chowCohomologyComponent C (gysinSystemOfInvertible C)
    (preimageInclusion f b iZ ≫ sW) p)

/-- **The class `(E ⟶ Z)_* ∘ κ' ∘ C ∈ A^p(Z ⟶ X)` of Stacks 0F9K**, for a class `κ ∈ A^p(E)`
vanishing on `T ∩ E`: `κ'` is the localized class of Stacks 0F9H of `κ` for the cover
`W_∞ = T ∪ E`, and `C` the class of Stacks 0F9J. -/
def localizedClassAtInfinityOf
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW)
      (pullback.snd iT (preimageInclusion f b iZ)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0) :
    BivariantClass C (gysinSystemOfInvertible C) (iZ ≫ f) f iZ rfl p :=
  pushAtInfinity C f b hA iZ sW hsW
    (closedCoverLocalizedClass C sW (iT ≫ sW) (preimageInclusion f b iZ ≫ sW) iT rfl
      (preimageInclusion f b iZ) rfl (range_union_range_preimageInclusion f b iZ iT hT) κ hκ)

/-- **Independence of `T`.** The class `(E ⟶ Z)_* ∘ κ' ∘ C` does not depend on the closed
subscheme `T ⊆ W_∞`: the localized class `κ'` of Stacks 0F9H does not, by Stacks 0FAH. -/
theorem localizedClassAtInfinityOf_eq_of_closed {T₁ T₂ : Scheme.{u}}
    (iT₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₁]
    (hT₁ : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT₁.base)
    (iT₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT₂]
    (hT₂ : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT₂.base)
    (hκ₁ : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ sW) (pullback.snd iT₁ (preimageInclusion f b iZ)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
    (hκ₂ : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ sW) (pullback.snd iT₂ (preimageInclusion f b iZ)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0) :
    localizedClassAtInfinityOf C f b hA iZ sW hsW iT₁ hT₁ κ hκ₁ =
      localizedClassAtInfinityOf C f b hA iZ sW hsW iT₂ hT₂ κ hκ₂ :=
  congrArg (pushAtInfinity C f b hA iZ sW hsW)
    (eq_of_isClosedCoverLocalizedClass C (gysinSystemOfInvertible C) sW (iT₁ ≫ sW) (iT₂ ≫ sW)
      (preimageInclusion f b iZ ≫ sW) iT₁ rfl iT₂ rfl (preimageInclusion f b iZ) rfl p
      (range_union_range_preimageInclusion f b iZ iT₁ hT₁)
      (range_union_range_preimageInclusion f b iZ iT₂ hT₂)
      (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sW _ _ iT₁ rfl _ rfl _ κ hκ₁)
      (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sW _ _ iT₂ rfl _ rfl _ κ hκ₂))

/-- The class `(E ⟶ Z)_* ∘ κ' ∘ C` does not depend on how the structure morphism of `W_∞` is
written. -/
theorem localizedClassAtInfinityOf_congr {sW₁ sW₂ : modificationFibreAtInfinity f b ⟶ C.S}
    [LocallyOfFiniteType sW₁] [LocallyOfFiniteType sW₂]
    (hsW₁ : modificationProjectionAtInfinity f b ≫ f = sW₁)
    (hsW₂ : modificationProjectionAtInfinity f b ≫ f = sW₂)
    {κ₁ : chowCohomologyComponent C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW₁) p}
    {κ₂ : chowCohomologyComponent C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW₂) p}
    (hκ : κ₁ ≍ κ₂)
    (hκ₁ : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ sW₁) (pullback.snd iT (preimageInclusion f b iZ)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ₁ = 0)
    (hκ₂ : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f b iZ ≫ sW₂) (pullback.snd iT (preimageInclusion f b iZ)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ₂ = 0) :
    localizedClassAtInfinityOf C f b hA iZ sW₁ hsW₁ iT hT κ₁ hκ₁ =
      localizedClassAtInfinityOf C f b hA iZ sW₂ hsW₂ iT hT κ₂ hκ₂ := by
  subst hsW₁ hsW₂
  obtain rfl := eq_of_heq hκ
  rfl

end Localized

end GysinAtInfinity

end Stacks.Chow

end
