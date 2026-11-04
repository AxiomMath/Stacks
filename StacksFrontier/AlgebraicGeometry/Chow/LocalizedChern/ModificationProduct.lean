module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedProductPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Modification
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.AssociativityOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantClassCopy

/-!
# Products of localized classes of a modification
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section RestrictionProduct

variable (C : ChowSituation.{u}) {Z Z' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : Z' ⟶ Z) [LocallyOfFiniteType f] {p q : ℤ}

/-- The restriction of Stacks 0B7F is multiplicative: the restriction of a product `a b` of Chow
cohomology classes along `f : Z' ⟶ Z` is the product of the restrictions. -/
theorem chowCohomologyRestriction_mulId
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ q) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ f (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (a.mulId C sZ b) =
      (chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a).mulId C (f ≫ sZ)
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ f q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b) := by
  refine BivariantClass.eq_of_idRule_eq C (f ≫ sZ) _ _ _ fun {T} n _ k α ↦ eq_of_heq ?_
  rw [chowCohomologyRestriction_idRule]
  refine (BivariantClass.idRule_mulId C sZ a b (n ≫ f) k _).trans (HEq.trans ?_
    (BivariantClass.idRule_mulId C (f ≫ sZ) _ _ n k α).symm)
  rw [chowCohomologyRestriction_idRule, chowCohomologyRestriction_idRule]
  refine IdentityCapRule.heq_congr C sZ _ rfl rfl ?_
  exact (chowGroupCongr_heq C _ _ _).symm
end RestrictionProduct

/-! ### Congruences for heterogeneous equality -/

section HEqCongr

variable {C : ChowSituation.{u}} {G : GysinSystem C}

/-- A class read for an equal morphism (`Stacks.Chow.BivariantClass.congrHom`) is heterogeneously
equal to the class. -/
theorem BivariantClass.congrHom_heq {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] {hf : f ≫ sY = sX} (e : f = f') (hf' : f' ≫ sY = sX) {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) : c.congrHom e hf' ≍ c := by
  subst e
  rfl

/-- The pushforward of Stacks 0EPK is compatible with heterogeneous equality of the class, over
equal morphisms and degrees. -/
theorem bivariantProperPushforward_heq_congr {X Y Z : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f] {g g' : Y ⟶ Z} [LocallyOfFiniteType g]
    [LocallyOfFiniteType g'] (hgg' : g = g') (hf : f ≫ sY = sX) {hg : g ≫ sZ = sY}
    {hg' : g' ≫ sZ = sY} {p p' : ℤ} (hp : p = p')
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) p}
    {c' : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g')
      (comp_comp_structureMorphism_eq hf hg') p'} (hc : c ≍ c') :
    bivariantProperPushforwardOfInvertible C sX sY sZ f g hf hg p c ≍
      bivariantProperPushforwardOfInvertible C sX sY sZ f g' hf hg' p' c' := by
  subst hgg' hp
  cases hc
  rfl

end HEqCongr


/-! ### The first multiplication with a localized class -/

section Modification

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  (D : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA)
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {p r : ℤ}

/-- The extension along a closed cover (Stacks 0F9H) only depends on the class extended, not on
the proof that it vanishes. -/
theorem closedCoverExtension_congr {X₁ X₂ Y : Scheme.{u}} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] (i₁ : X₁ ⟶ Y) (i₂ : X₂ ⟶ Y) [IsClosedImmersion i₁]
    [IsClosedImmersion i₂] (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {p : ℤ}
    {a a' : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sY) p} (h : a = a')
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (ha' : BivariantClass.VanishesOver a' (pullback.snd i₁ i₂)) :
    closedCoverExtension C sY i₁ i₂ (i₂ ≫ sY) rfl a hcover ha =
      closedCoverExtension C sY i₁ i₂ (i₂ ≫ sY) rfl a' hcover ha' := by
  subst h
  rfl

/-- **The first multiplication of Stacks 0FA0 on a localized class**, given the commutation
`C ∘ i_0^* d = d|_{W_∞} ∘ C` of the class at infinity with the restriction to the section at
zero. For `q ∈ A^p(W)` vanishing over `T` and `d ∈ A^r(W)`, `q' ∘ i_0^* d = (q d)'`. -/
theorem localizedModificationClass_supportedRightComp_of_heq
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) r)
    (h3 : bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
        (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 r
        D.bivariantClass
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 X)
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (hv := Category.id_comp _) (hv' := Category.id_comp f) r
          (chowCohomologyRestriction C (gysinSystemOfInvertible C)
            (modificationProjection f b ≫ f) (modificationSectionAtZero f b D.isIsoFibreAtZero) r
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)) ≍
      bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
        (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _) (modificationProjectionAtInfinity f b)
        (Category.id_comp _) rfl r 0
        (chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) r
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)
        D.bivariantClass) :
    supportedRightComp C (z ≫ f) f z rfl (localizedModificationClass D z t hT hq)
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 X)
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (hv := Category.id_comp _) (hv' := Category.id_comp f) r
          (chowCohomologyRestriction C (gysinSystemOfInvertible C)
            (modificationProjection f b ≫ f) (modificationSectionAtZero f b D.isIsoFibreAtZero) r
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)) =
      localizedModificationClass D z t hT (BivariantClass.VanishesOver.mulId_right C hq d) := by
  unfold supportedRightComp localizedModificationClass
  refine eq_of_heq ((BivariantClass.congrHom_heq _ _ _).trans ?_)
  rw [← bivariantProperPushforwardOfInvertible_bivariantCompositeOfInvertible]
  refine bivariantProperPushforward_heq_congr _ (Category.comp_id z) _ rfl ?_
  refine (BivariantClass.congrHom_heq _ _ _).trans ?_
  refine (bivariantCompositeOfInvertible_heq_congr (pullback.condition).symm rfl
    (add_zero p).symm rfl (BivariantClass.copy_heq _ _ _ _ _) HEq.rfl).trans ?_
  refine (bivariantCompositeOfInvertible_assoc C _ (modificationProjectionAtInfinity f b ≫ f) f f
    (pullback.fst (modificationProjectionAtInfinity f b) z) (modificationProjectionAtInfinity f b)
    (𝟙 X) rfl rfl (Category.id_comp f) p 0 r _ D.bivariantClass _).trans ?_
  refine (bivariantCompositeOfInvertible_heq_congr rfl
    (by rw [Category.comp_id, Category.id_comp]) rfl (by rw [zero_add, add_zero]) HEq.rfl
    h3).trans ?_
  refine (bivariantCompositeOfInvertible_assoc C _ (modificationProjectionAtInfinity f b ≫ f)
    (modificationProjectionAtInfinity f b ≫ f) f
    (pullback.fst (modificationProjectionAtInfinity f b) z) (𝟙 _)
    (modificationProjectionAtInfinity f b) rfl (Category.id_comp _) rfl p r 0 _ _
    D.bivariantClass).symm.trans ?_
  refine (bivariantCompositeOfInvertible_heq_congr (Category.comp_id _) rfl rfl rfl ?_
    HEq.rfl).trans (BivariantClass.copy_heq _ _ _ _ _).symm
  refine (BivariantClass.congrHom_heq (Category.comp_id _) rfl _).symm.trans (heq_of_eq ?_)
  show supportedRightComp C _ (modificationProjectionAtInfinity f b ≫ f) _ rfl _ _ = _
  unfold modificationExtension
  refine (supportedRightComp_closedCoverExtension C (modificationProjectionAtInfinity f b ≫ f) t
    (pullback.fst (modificationProjectionAtInfinity f b) z)
    (range_union_range_pullbackFst_eq_univ z t hT)
    (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)) _).trans ?_
  refine closedCoverExtension_congr _ _ _ ?_
    (BivariantClass.VanishesOver.mulId_right C
      (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
        (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)) _)
    (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (BivariantClass.VanishesOver.chowCohomologyRestriction_modificationInclusionAtInfinity t
        (BivariantClass.VanishesOver.mulId_right C hq d)))
  exact ((congrArg (chowCohomologyRestriction C (gysinSystemOfInvertible C)
    (modificationProjectionAtInfinity f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) z) (p + r)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C))
      (chowCohomologyRestriction_mulId C (modificationProjection f b ≫ f)
        (modificationInclusionAtInfinity f b) q d)).trans
    (chowCohomologyRestriction_mulId C (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) _ _)).symm

/-- **The third multiplication of Stacks 0FA0 on localized classes**, given the commutation of the
class at infinity with the restriction of `q₂` to the section at zero: for `q₁ ∈ A^p(W)` and
`q₂ ∈ A^r(W)` vanishing over `T`, `res(q₁') ∘ q₂' = (q₁ q₂)'`. By Stacks 0FA1
(`Stacks.Chow.supportedMul_eq_supportedRightComp`) the product is `q₁' ∘ (Z ⟶ X)_* ∘ q₂'`, and
`(Z ⟶ X)_* ∘ q₂' = i_0^* q₂` by the generic form of Stacks 0F9K. -/
theorem localizedModificationClass_supportedMul_of_heq
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q₁ : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hq₁ : BivariantClass.VanishesOver q₁ (t ≫ modificationInclusionAtInfinity f b))
    {q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) r}
    (hq₂ : BivariantClass.VanishesOver q₂ (t ≫ modificationInclusionAtInfinity f b))
    (h3 : bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
        (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 r
        D.bivariantClass
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 X)
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (hv := Category.id_comp _) (hv' := Category.id_comp f) r
          (chowCohomologyRestriction C (gysinSystemOfInvertible C)
            (modificationProjection f b ≫ f) (modificationSectionAtZero f b D.isIsoFibreAtZero) r
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₂)) ≍
      bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
        (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _) (modificationProjectionAtInfinity f b)
        (Category.id_comp _) rfl r 0
        (chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) r
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₂)
        D.bivariantClass) :
    supportedMul C (z ≫ f) f z rfl (localizedModificationClass D z t hT hq₁)
        (localizedModificationClass D z t hT hq₂) =
      localizedModificationClass D z t hT (BivariantClass.VanishesOver.mulId_right C hq₁ q₂) := by
  rw [supportedMul_eq_supportedRightComp,
    properPushforwardChowCohomology_localizedModificationClass]
  exact localizedModificationClass_supportedRightComp_of_heq D z t hT hq₁ q₂ h3

/-- The localized class only depends on the class `q`, not on the proof that it vanishes over
`T`. -/
theorem localizedModificationClass_congr
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q q' :
      chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (h : q = q') (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hq' : BivariantClass.VanishesOver q' (t ≫ modificationInclusionAtInfinity f b)) :
    localizedModificationClass D z t hT hq = localizedModificationClass D z t hT hq' := by
  subst h
  rfl

/-- Localized classes of classes with zero sum add up to the localized class of zero. -/
private theorem localizedModificationClass_add_eq_zero
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {q₁ q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) p}
    (h : q₁ + q₂ = 0)
    (hq₁ : BivariantClass.VanishesOver q₁ (t ≫ modificationInclusionAtInfinity f b))
    (hq₂ : BivariantClass.VanishesOver q₂ (t ≫ modificationInclusionAtInfinity f b)) :
    localizedModificationClass D z t hT hq₁ + localizedModificationClass D z t hT hq₂ =
      localizedModificationClass D z t hT BivariantClass.VanishesOver.zero := by
  rw [← localizedModificationClass_add D z t hT hq₁ hq₂]
  exact localizedModificationClass_congr D z t hT h _ _

/-- A class `c ∈ A^p(Z ⟶ X)` *is the localized class* of `q ∈ A^p(W)` when `q` vanishes over `T`
and `c = q'` (`Stacks.Chow.localizedModificationClass`). -/
def IsLocalizedModificationClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p)
    (c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p) : Prop :=
  ∃ hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b),
    c = localizedModificationClass D z t hT hq

namespace IsLocalizedModificationClass

variable {D z t}
variable {hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t}

/-- The localized class of `q` is the localized class of `q`. -/
theorem of_vanishesOver
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    IsLocalizedModificationClass D z t hT q (Stacks.Chow.localizedModificationClass D z t hT hq) :=
  ⟨hq, rfl⟩

/-- A class which is the localized class of `q` is `q'`, for every proof that `q` vanishes over
`T`. -/
theorem eq
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h : IsLocalizedModificationClass D z t hT q c)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b)) :
    c = Stacks.Chow.localizedModificationClass D z t hT hq := by
  obtain ⟨hq', rfl⟩ := h
  rfl

/-- Localized classes add. -/
theorem add
    {q₁ q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) p}
    {c₁ c₂ : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h₁ : IsLocalizedModificationClass D z t hT q₁ c₁)
    (h₂ : IsLocalizedModificationClass D z t hT q₂ c₂) :
    IsLocalizedModificationClass D z t hT (q₁ + q₂) (c₁ + c₂) := by
  obtain ⟨hq₁, rfl⟩ := h₁
  obtain ⟨hq₂, rfl⟩ := h₂
  exact ⟨BivariantClass.VanishesOver.add hq₁ hq₂,
    (localizedModificationClass_add D z t hT hq₁ hq₂).symm⟩

/-- The zero class is the localized class of the zero class. -/
theorem zero : IsLocalizedModificationClass D z t hT
    (0 : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p)
    0 := by
  exact ⟨BivariantClass.VanishesOver.zero, (add_eq_left.mp
    (localizedModificationClass_add_eq_zero D z t hT (add_zero 0) _ _)).symm⟩

/-- Localized classes negate. -/
theorem neg
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h : IsLocalizedModificationClass D z t hT q c) :
    IsLocalizedModificationClass D z t hT (-q) (-c) := by
  obtain ⟨hq, rfl⟩ := h
  refine ⟨BivariantClass.VanishesOver.neg hq, neg_eq_of_add_eq_zero_right ?_⟩
  exact (localizedModificationClass_add_eq_zero D z t hT (add_neg_cancel q) hq _).trans
    ((zero (D := D) (z := z) (t := t) (hT := hT)).eq _).symm

/-- Localized classes subtract. -/
theorem sub
    {q₁ q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) p}
    {c₁ c₂ : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h₁ : IsLocalizedModificationClass D z t hT q₁ c₁)
    (h₂ : IsLocalizedModificationClass D z t hT q₂ c₂) :
    IsLocalizedModificationClass D z t hT (q₁ - q₂) (c₁ - c₂) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add h₂.neg

/-- Localized classes are stable under integer multiples. -/
theorem zsmul
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h : IsLocalizedModificationClass D z t hT q c) (n : ℤ) :
    IsLocalizedModificationClass D z t hT (n • q) (n • c) := by
  induction n using Int.induction_on with
  | zero => simpa using zero
  | succ n ih => simpa [add_smul] using ih.add h
  | pred n ih =>
    rw [sub_smul, one_smul, sub_eq_add_neg, sub_smul, one_smul, sub_eq_add_neg]
    exact ih.add h.neg

/-- Localized classes are stable under finite sums. -/
theorem sum {ι : Type*} (s : Finset ι)
    {q : ι → chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) p}
    {c : ι → BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h : ∀ i ∈ s, IsLocalizedModificationClass D z t hT (q i) (c i)) :
    IsLocalizedModificationClass D z t hT (∑ i ∈ s, q i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))

/-- Localized classes are stable under transport along an equality of degrees. -/
theorem bivariantClassDegreeCongr {r : ℤ} (hpr : p = r)
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h : IsLocalizedModificationClass D z t hT q c) :
    IsLocalizedModificationClass D z t hT
      (Stacks.Chow.bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _) hpr q)
      (Stacks.Chow.bivariantClassDegreeCongr C _ (z ≫ f) f z rfl hpr c) := by
  subst hpr
  exact h

end IsLocalizedModificationClass

/-- The commutation `C ∘ i_0^* d = d|_{W_∞} ∘ C` of the class at infinity recorded by `D` with
the restriction of `d ∈ A^r(W)` to the section at zero, as a heterogeneous equality of classes
of `A^{0+r}(W_∞ ⟶ X)` and `A^{r+0}(W_∞ ⟶ X)`. For the class of Stacks 0F9J it holds for every
`d`. -/
def CommutesAtInfinity {r : ℤ}
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) r) :
    Prop :=
  bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f) f f
      (modificationProjectionAtInfinity f b) (𝟙 X) rfl (Category.id_comp f) 0 r
      D.bivariantClass
      (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 X)
        (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
        (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
        (hv := Category.id_comp _) (hv' := Category.id_comp f) r
        (chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationSectionAtZero f b D.isIsoFibreAtZero) r
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)) ≍
    bivariantCompositeOfInvertible C (modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f) f (𝟙 _) (modificationProjectionAtInfinity f b)
      (Category.id_comp _) rfl r 0
      (chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) r
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)
      D.bivariantClass

omit [IsClosedImmersion z] [IsClosedImmersion t] in
variable {D z t} in
/-- Localized classes multiply, by the third multiplication of Stacks 0FA0, when the class at
infinity commutes with the second factor: if `c₁ = q₁'` and `c₂ = q₂'` then
`res(c₁) ∘ c₂ = (q₁ q₂)'`. -/
theorem IsLocalizedModificationClass.supportedMul [IsClosedImmersion z] [IsClosedImmersion t]
    {hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t}
    {q₁ : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) r}
    {c₁ : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    {c₂ : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl r}
    (h₁ : IsLocalizedModificationClass D z t hT q₁ c₁)
    (h₂ : IsLocalizedModificationClass D z t hT q₂ c₂) (hc : CommutesAtInfinity D q₂) :
    IsLocalizedModificationClass D z t hT (q₁.mulId C _ q₂)
      (Stacks.Chow.supportedMul C (z ≫ f) f z rfl c₁ c₂) := by
  obtain ⟨hq₁, rfl⟩ := h₁
  obtain ⟨hq₂, rfl⟩ := h₂
  exact ⟨_, localizedModificationClass_supportedMul_of_heq D z t hT hq₁ hq₂ hc⟩

/-- **Newton's recursion for localized classes (the generic form of Stacks 0FAX).** Let `c` be a
total class on `W` and `P` a sequence of total classes on `W` satisfying Newton's recursion
(`Stacks.Chow.IsNewtonPowerSums`), with `c_i` (`i ≥ 1`) and `P_q ∈ A^q(W)` (`q ≥ 1`) vanishing
over `T`, and with the class at infinity commuting with every `P_q`. Then the localized classes
`c'_i`, `P'_q ∈ A^*(Z ⟶ X)` satisfy Newton's recursion with the multiplication of Stacks 0FA0:
`P'_{q+1} = ∑_{j < q} (-1)^j c'_{j+1} P'_{q-j} + (-1)^q (q + 1) c'_{q+1}`. -/
theorem localizedModificationClass_isNewtonPowerSums
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    {c : TotalChowClass C (modificationProjection f b ≫ f)}
    {P : ℕ → TotalChowClass C (modificationProjection f b ≫ f)}
    (hN : TotalChowClass.IsNewtonPowerSums c P)
    (hc : ∀ i, 0 < i → BivariantClass.VanishesOver (c i) (t ≫ modificationInclusionAtInfinity f b))
    (hP : ∀ q, 0 < q →
      BivariantClass.VanishesOver (P q q) (t ≫ modificationInclusionAtInfinity f b))
    (hcomm : ∀ q, 0 < q → CommutesAtInfinity D (P q q)) (q : ℕ) :
    localizedModificationClass D z t hT (hP (q + 1) (Nat.succ_pos q)) =
      ∑ j ∈ (Finset.range q).attach, ((-1 : ℤ) ^ (j : ℕ)) •
          Stacks.Chow.bivariantClassDegreeCongr C _ (z ≫ f) f z rfl
            (newton_degree_eq (Finset.mem_range.mp j.2))
            (Stacks.Chow.supportedMul C (z ≫ f) f z rfl
              (localizedModificationClass D z t hT (hc ((j : ℕ) + 1) (Nat.succ_pos _)))
              (localizedModificationClass D z t hT
                (hP (q - j) (by have := Finset.mem_range.mp j.2; omega)))) +
        ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) •
          localizedModificationClass D z t hT (hc (q + 1) (Nat.succ_pos q)) := by
  have key := congrArg (fun x : TotalChowClass C (modificationProjection f b ≫ f) => x (q + 1))
    (hN q)
  simp only [TotalChowClass.add_apply, TotalChowClass.sum_apply] at key
  have hterm : ∀ j : Finset.range q,
      (((-1 : ℤ) ^ (j : ℕ)) • (TotalChowClass.homComponent ((j : ℕ) + 1) c * P (q - j))) (q + 1) =
        ((-1 : ℤ) ^ (j : ℕ)) • Stacks.Chow.bivariantClassDegreeCongr C _ _ _ (𝟙 W)
          (Category.id_comp _) (newton_degree_eq (Finset.mem_range.mp j.2))
          ((c ((j : ℕ) + 1)).mulId C _ (P (q - j) (q - j))) := fun j => by
    have hj := Finset.mem_range.mp j.2
    show ((-1 : ℤ) ^ (j : ℕ)) •
      (TotalChowClass.homComponent ((j : ℕ) + 1) c * P (q - j)) (q + 1) = _
    rw [TotalChowClass.homPart_mul_apply C _ c (P (q - j))
      (by omega : (j : ℕ) + 1 + (q - j) = q + 1)]
  have hlast : (((-1 : ℤ) ^ q * ((q : ℤ) + 1)) • TotalChowClass.homComponent (q + 1) c) (q + 1) =
      ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) • c (q + 1) := by
    show ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) • (TotalChowClass.homComponent (q + 1) c) (q + 1) = _
    rw [TotalChowClass.homComponent_apply, if_pos rfl]
  rw [← Finset.sum_attach, Finset.sum_congr rfl fun j _ => hterm j, hlast] at key
  refine (IsLocalizedModificationClass.eq (q := P (q + 1) (q + 1)) ?_ _).symm
  rw [key]
  refine IsLocalizedModificationClass.add (IsLocalizedModificationClass.sum _ fun j _ => ?_)
    ((IsLocalizedModificationClass.of_vanishesOver (hc (q + 1) (Nat.succ_pos q))).zsmul _)
  have hj := Finset.mem_range.mp j.2
  refine IsLocalizedModificationClass.zsmul ?_ _
  refine IsLocalizedModificationClass.bivariantClassDegreeCongr _ ?_
  exact (IsLocalizedModificationClass.of_vanishesOver
    (hc ((j : ℕ) + 1) (Nat.succ_pos _))).supportedMul
    (IsLocalizedModificationClass.of_vanishesOver (hP (q - j) (by omega)))
    (hcomm (q - j) (by omega))

end Modification

end Stacks.Chow

end
