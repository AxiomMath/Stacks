module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CompositeCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible

/-!
# A composite of commuting classes commutes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, and let `j : W ⟶ U` and `i : U ⟶ X` be morphisms locally of
finite type. Let `a ∈ A^p(W ⟶ U)` and `b ∈ A^q(U ⟶ X)` be bivariant classes, and let
`a ∘ b ∈ A^{p+q}(W ⟶ X)` be their composite (Stacks 0B75), which caps by `a ∩ (b ∩ -)`.

Suppose that `b` commutes, in the sense of Stacks 0FA2, with a bivariant class
`c ∈ A^{p₂}(Z₂ ⟶ X)`, and that `a` commutes with every bivariant class over `U`. Then `a ∘ b`
commutes with `c`:

  `c ∩ (a ∩ (b ∩ α)) = a ∩ (c ∩ (b ∩ α)) = a ∩ (b ∩ (c ∩ α))`,

the first equality being the commutation of `a` with the restriction
`res(c) ∈ A^{p₂}(Z₂ ×_X U ⟶ U)` of `c` along `i` (Stacks 0F9Z), the second the commutation of `b`
with `c`.

## Main results

* `Stacks.Chow.bivariantCommute_bivariantComposite` — if `a` commutes with every bivariant class
  over `U` and `b` commutes with `c`, then `a ∘ b` commutes with `c`.
* `Stacks.Chow.bivariantCommute_bivariantCompositeOfInvertible` — the same at the Gysin system of
  the first Chern class rule, where the composite exists unconditionally: if `a` commutes with
  everything over `U` and `b` commutes with everything over `X`, so does `a ∘ b`.

## References

* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The composite of commuting classes -/

section Composite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {W U X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (j : W ⟶ U) [LocallyOfFiniteType j] (i : U ⟶ X)
  [LocallyOfFiniteType i] (p q : ℤ)

/-- **A composite of commuting classes commutes.** Let `a ∈ A^p(W ⟶ U)` commute with every
bivariant class over `U`, and let `b ∈ A^q(U ⟶ X)` commute with `c₂ ∈ A^{p₂}(Z₂ ⟶ X)`. Then the
composite `a ∘ b ∈ A^{p+q}(W ⟶ X)` of Stacks 0B75 commutes with `c₂`:

  `c₂ ∩ (a ∩ (b ∩ α)) = a ∩ (res(c₂) ∩ (b ∩ α)) = a ∩ (b ∩ (c₂ ∩ α))`,

where `res(c₂)` is the restriction of `c₂` along `i` (Stacks 0F9Z), with which `a` commutes by
hypothesis. -/
theorem bivariantCommute_bivariantComposite
    (hgys : G.IsNaturalUnderBaseChangeIso) (hgysc : G.IsNaturalUnderPullbackCompPushforward)
    (a : BivariantClass C G (j ≫ (i ≫ sX)) (i ≫ sX) j rfl p)
    (b : BivariantClass C G (i ≫ sX) sX i rfl q)
    (ha : ∀ {Z₂' : Scheme.{u}} (f₂' : Z₂' ⟶ U) [LocallyOfFiniteType f₂'] (p₂' : ℤ)
      (c₂' : BivariantClass C G (f₂' ≫ (i ≫ sX)) (i ≫ sX) f₂' rfl p₂'),
      BivariantCommute C G (i ≫ sX) j f₂' p p₂' a c₂')
    {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ X) [LocallyOfFiniteType f₂] (p₂ : ℤ)
    (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)
    (hb : BivariantCommute C G sX i f₂ q p₂ b c₂) {f₁ : W ⟶ X} [LocallyOfFiniteType f₁]
    (e : j ≫ i = f₁) :
    BivariantCommute C G sX f₁ f₂ (p + q) p₂
      (BivariantClass.congrHom e rfl
        (bivariantClassCongrBase C G (j ≫ i)
          ((Category.assoc j i sX).symm.trans (congrArg (· ≫ sX) e)) rfl
          (hv' := congrArg (· ≫ sX) e) (p + q)
          (bivariantComposite C G (j ≫ (i ≫ sX)) (i ≫ sX) sX j i rfl rfl p q a b hgys hgysc)))
      c₂ := by
  subst e
  show BivariantCommute C G sX (j ≫ i) f₂ (p + q) p₂
    (bivariantClassCongrBase C G (j ≫ i) (Category.assoc j i sX).symm rfl (hv' := rfl) (p + q)
      (bivariantComposite C G (j ≫ (i ≫ sX)) (i ≫ sX) sX j i rfl rfl p q a b hgys hgysc)) c₂
  set c₁ := bivariantClassCongrBase C G (j ≫ i) (Category.assoc j i sX).symm rfl (hv' := rfl)
    (p + q) (bivariantComposite C G (j ≫ (i ≫ sX)) (i ≫ sX) sX j i rfl rfl p q a b hgys hgysc)
    with hc₁
  have h₁ : ∀ {S : Scheme.{u}} (s : S ⟶ X) [LocallyOfFiniteType s] (k' : ℤ)
      (ε : chowGroup C (s ≫ sX) k'),
      c₁.cap s k' ε ≍ chowPushforwardOfIso C (pullback.fst j (pullback.fst i s) ≫ (j ≫ (i ≫ sX)))
        (pullback.fst (j ≫ i) s ≫ (j ≫ (i ≫ sX))) (pullbackRightPullbackFstIso i s j).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp _ j i s) ((k' - q) - p)
        (a.cap (pullback.fst i s) (k' - q) (b.cap s k' ε)) := by
    intro S s _ k' ε
    exact (bivariantClassCongrBase_cap C G (j ≫ i) _ rfl (p + q) _ s k' ε ε HEq.rfl).trans
      (chowGroupDegreeEquiv_heq C _ _ _)
  set c₂' : BivariantClass C G (pullback.snd f₂ i ≫ (i ≫ sX)) (i ≫ sX) (pullback.snd f₂ i) rfl
      p₂ := bivariantClassCongrBase C G (pullback.snd f₂ i)
    (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl i).symm rfl p₂
    (bivariantRestriction C G (f₂ ≫ sX) sX f₂ rfl i p₂ hgys c₂) with hc₂'
  have h₂ : ∀ {V : Scheme.{u}} (v : V ⟶ U) [LocallyOfFiniteType v] (k' : ℤ)
      (δ : chowGroup C (v ≫ (i ≫ sX)) k'),
      c₂'.cap v k' δ ≍ chowPushforwardOfIso C (pullback.fst f₂ (v ≫ i) ≫ (f₂ ≫ sX))
        (pullback.fst (pullback.snd f₂ i) v ≫ (pullback.fst f₂ i ≫ (f₂ ≫ sX)))
        (pullbackLeftPullbackSndIso f₂ i v).inv (by simp) (k' - p₂)
        (c₂.cap (v ≫ i) k' (chowGroupCongr C (Category.assoc v i sX).symm k' δ)) := by
    intro V v _ k' δ
    exact bivariantClassCongrBase_cap C G (pullback.snd f₂ i) _ rfl p₂ _ v k' δ δ HEq.rfl
  intro T t _ k α
  have hA := ha (pullback.snd f₂ i) p₂ c₂' (pullback.fst i t) (k - q) (b.cap t k α)
  have hB := hb t k α
  simp only [bivariantIteratedCap_apply] at hA hB ⊢
  have hR : c₂.cap (pullback.fst (j ≫ i) t ≫ (j ≫ i)) (k - (p + q))
        (chowGroupCongr C (Category.assoc (pullback.fst (j ≫ i) t) (j ≫ i) sX).symm (k - (p + q))
          (c₁.cap t k α)) ≍
      chowPushforwardOfIso C
        (pullback.fst f₂ ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) ≫ (f₂ ≫ sX))
        (pullback.fst f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ (f₂ ≫ sX))
        (testBaseChangeIso f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i))
          (pullbackRightPullbackFstIso i t j).hom
          ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (by simp)).hom (by simp)
        ((k - q - p) - p₂)
        (c₂.cap ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (k - q - p)
          (chowGroupCongr C (by simp) (k - q - p)
            (a.cap (pullback.fst i t) (k - q) (b.cap t k α)))) := by
    have hmb : (pullbackRightPullbackFstIso i t j).hom ≫
        ((pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ sX) =
        pullback.fst j (pullback.fst i t) ≫ (j ≫ (i ≫ sX)) := by simp
    refine HEq.trans (BivariantClass.cap_heq c₂ _ (by ring)
      (y := chowPushforwardOfIso C _ _ (pullbackRightPullbackFstIso i t j).hom hmb (k - q - p)
        (a.cap (pullback.fst i t) (k - q) (b.cap t k α))) ?_) (heq_of_eq ?_)
    · refine (chowGroupCongr_heq C _ _ _).trans ((h₁ t k α).trans ?_)
      exact chowPushforwardOfIso_heq _ _ _ rfl (by simp) rfl HEq.rfl
    · exact BivariantClass.cap_chowPushforwardOfIso c₂ _ _ _ (by simp) _ (by simp) _ hmb _ _ rfl
  have hL : chowPushforwardOfIso C
        (pullback.fst (j ≫ i) (pullback.fst f₂ t ≫ f₂) ≫ ((j ≫ i) ≫ sX))
        (pullback.fst f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ (f₂ ≫ sX))
        (commuteComparisonHom (j ≫ i) f₂ t)
        (commuteComparisonHom_comp_structureMorphism C sX (j ≫ i) f₂ t) ((k - p₂) - (p + q))
        (c₁.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
          (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
            (c₂.cap t k α))) ≍
      chowPushforwardOfIso C
        (pullback.fst j (pullback.fst i (pullback.fst f₂ t ≫ f₂)) ≫ (j ≫ (i ≫ sX)))
        (pullback.fst f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ (f₂ ≫ sX))
        ((pullbackRightPullbackFstIso i (pullback.fst f₂ t ≫ f₂) j).hom ≫
          commuteComparisonHom (j ≫ i) f₂ t) (by
            rw [Category.assoc, commuteComparisonHom_comp_structureMorphism]; simp)
        ((k - p₂ - q) - p)
        (a.cap (pullback.fst i (pullback.fst f₂ t ≫ f₂)) (k - p₂ - q)
          (b.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
            (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
              (c₂.cap t k α)))) := by
    refine HEq.trans (chowPushforwardOfIso_heq _ _
      (commuteComparisonHom_comp_structureMorphism C sX (j ≫ i) f₂ t) (by simp) rfl (by ring)
      (h₁ _ _ _)) (heq_of_eq ?_)
    exact chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ _
  have hm₁ : (commuteComparisonHom i f₂ t ≫
      (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv) ≫
      (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i) =
      pullback.fst i (pullback.fst f₂ t ≫ f₂) := by
    simp
  have hAL : chowPushforwardOfIso C
        (pullback.fst j (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫
          pullback.snd f₂ i) ≫ (j ≫ (i ≫ sX)))
        (pullback.fst (pullback.snd f₂ i) (pullback.fst j (pullback.fst i t) ≫ j) ≫
          (pullback.snd f₂ i ≫ (i ≫ sX)))
        (commuteComparisonHom j (pullback.snd f₂ i) (pullback.fst i t))
        (commuteComparisonHom_comp_structureMorphism C (i ≫ sX) j (pullback.snd f₂ i)
          (pullback.fst i t)) ((k - q - p₂) - p)
        (a.cap (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i)
          (k - q - p₂)
          (chowGroupCongr C (Category.assoc (pullback.fst (pullback.snd f₂ i) (pullback.fst i t))
            (pullback.snd f₂ i) (i ≫ sX)).symm (k - q - p₂)
            (c₂'.cap (pullback.fst i t) (k - q) (b.cap t k α)))) ≍
      chowPushforwardOfIso C
        (pullback.fst j (pullback.fst i (pullback.fst f₂ t ≫ f₂)) ≫ (j ≫ (i ≫ sX)))
        (pullback.fst (pullback.snd f₂ i) (pullback.fst j (pullback.fst i t) ≫ j) ≫
          (pullback.snd f₂ i ≫ (i ≫ sX)))
        ((testBaseChangeIso j
            (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i)
            (commuteComparisonHom i f₂ t ≫
              (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv)
            (pullback.fst i (pullback.fst f₂ t ≫ f₂)) hm₁).hom ≫
          commuteComparisonHom j (pullback.snd f₂ i) (pullback.fst i t))
        (by rw [Category.assoc, commuteComparisonHom_comp_structureMorphism]; simp)
        ((k - p₂ - q) - p)
        (a.cap (pullback.fst i (pullback.fst f₂ t ≫ f₂)) (k - p₂ - q)
          (b.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
            (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
              (c₂.cap t k α)))) := by
    have hmb : (commuteComparisonHom i f₂ t ≫
        (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv) ≫
        ((pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i) ≫ (i ≫ sX)) =
        pullback.fst i (pullback.fst f₂ t ≫ f₂) ≫ (i ≫ sX) := by
      rw [← Category.assoc, hm₁]
    have hcap := BivariantClass.cap_chowPushforwardOfIso a
      (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i)
      (commuteComparisonHom i f₂ t ≫ (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv)
      (pullback.fst i (pullback.fst f₂ t ≫ f₂)) hm₁ _ rfl (k - p₂ - q) hmb
      (b.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
        (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
          (c₂.cap t k α))) _ rfl
    refine HEq.trans (chowPushforwardOfIso_heq _ _
      (commuteComparisonHom_comp_structureMorphism C (i ≫ sX) j (pullback.snd f₂ i)
        (pullback.fst i t)) rfl rfl (by ring) ?_)
      (heq_of_eq (chowPushforwardOfIso_comp_apply C _ _ _ _ _ (by simp) _ _ _))
    refine HEq.trans (BivariantClass.cap_heq a _ (by ring) ?_) (heq_of_eq hcap)
    refine (chowGroupCongr_heq C _ _ _).trans ((h₂ _ _ _).trans ?_)
    refine HEq.trans (chowPushforwardOfIso_heq _ _ (by simp) rfl rfl (by ring)
      (((chowGroupDegreeEquiv_heq C _ _ _).symm.trans (heq_of_eq hB.symm)))) ?_
    rw [chowPushforwardOfIso_comp_apply]
    exact chowPushforwardOfIso_heq _ _ _ rfl (by simp [pullback.condition_assoc]) rfl HEq.rfl
  set A := a.cap (pullback.fst i (pullback.fst f₂ t ≫ f₂)) (k - p₂ - q)
    (b.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
      (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
        (c₂.cap t k α))) with hAdef
  have hX : c₂.cap ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (k - q - p)
        (chowGroupCongr C (by simp) (k - q - p)
          (a.cap (pullback.fst i t) (k - q) (b.cap t k α))) ≍
      chowPushforwardOfIso C
        (pullback.fst j (pullback.fst i (pullback.fst f₂ t ≫ f₂)) ≫ (j ≫ (i ≫ sX)))
        (pullback.fst f₂ ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) ≫ (f₂ ≫ sX))
        (((testBaseChangeIso j
            (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i)
            (commuteComparisonHom i f₂ t ≫
              (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv)
            (pullback.fst i (pullback.fst f₂ t ≫ f₂)) hm₁).hom ≫
          commuteComparisonHom j (pullback.snd f₂ i) (pullback.fst i t)) ≫
          (pullbackLeftPullbackSndIso f₂ i (pullback.fst j (pullback.fst i t) ≫ j)).hom)
        (by
          rw [Category.assoc, Category.assoc, ← Category.assoc _ (pullback.fst _ _) _,
            pullbackLeftPullbackSndIso_hom_fst]
          simp [pullback.condition_assoc])
        ((k - p₂ - q) - p) A := by
    have hinv := h₂ (pullback.fst j (pullback.fst i t) ≫ j) (k - q - p)
      (chowGroupCongr C (Category.assoc (pullback.fst j (pullback.fst i t)) j (i ≫ sX)).symm
        (k - q - p) (a.cap (pullback.fst i t) (k - q) (b.cap t k α)))
    have h3 := hinv.symm.trans ((chowGroupDegreeEquiv_heq C _ _ _).symm.trans
      ((heq_of_eq hA.symm).trans hAL))
    refine HEq.trans (BivariantClass.cap_heq c₂ _ rfl
      (y := chowGroupCongr C (Category.assoc (pullback.fst j (pullback.fst i t) ≫ j) i sX).symm
        (k - q - p)
        (chowGroupCongr C (Category.assoc (pullback.fst j (pullback.fst i t)) j (i ≫ sX)).symm
          (k - q - p) (a.cap (pullback.fst i t) (k - q) (b.cap t k α))))
      ((chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
        (chowGroupCongr_heq C _ _ _)).symm)) ?_
    have hB' : pullback.fst (pullback.snd f₂ i) (pullback.fst j (pullback.fst i t) ≫ j) ≫
        (pullback.snd f₂ i ≫ (i ≫ sX)) =
        pullback.fst (pullback.snd f₂ i) (pullback.fst j (pullback.fst i t) ≫ j) ≫
          (pullback.fst f₂ i ≫ (f₂ ≫ sX)) := by
      simp [pullback.condition_assoc]
    have hu : (pullbackLeftPullbackSndIso f₂ i (pullback.fst j (pullback.fst i t) ≫ j)).hom ≫
        (pullback.fst f₂ ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) ≫ (f₂ ≫ sX)) =
        pullback.fst (pullback.snd f₂ i) (pullback.fst j (pullback.fst i t) ≫ j) ≫
          (pullback.fst f₂ i ≫ (f₂ ≫ sX)) := by
      simp
    have h4 := chowPushforwardOfIso_comp_heq _
      (pullbackLeftPullbackSndIso f₂ i (pullback.fst j (pullback.fst i t) ≫ j)).hom _
      hu hB' (by ring) _ _ h3
    refine HEq.trans (heq_of_eq ?_) h4
    rw [chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (Iso.inv_hom_id _) _ (Category.id_comp _),
      chowPushforwardOfIso_id]
  refine eq_of_heq (hL.trans (HEq.symm ((chowGroupDegreeEquiv_heq C _ _ _).trans
    (hR.trans ?_))))
  refine HEq.trans (chowPushforwardOfIso_comp_heq _ _ _ _ rfl (by ring) _ _ hX) (heq_of_eq ?_)
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp

/-- **A composite of commuting classes commutes**, at the Gysin system of the first Chern class
rule. If `a ∈ A^p(W ⟶ U)` commutes with every bivariant class over `U` and `b ∈ A^q(U ⟶ X)`
commutes with every bivariant class over `X`, then the composite `a ∘ b ∈ A^{p+q}(W ⟶ X)` of
Stacks 0B75 commutes with every bivariant class over `X`. -/
theorem bivariantCommute_bivariantCompositeOfInvertible
    (a : BivariantClass C (gysinSystemOfInvertible C) (j ≫ (i ≫ sX)) (i ≫ sX) j rfl p)
    (b : BivariantClass C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl q)
    (ha : ∀ {Z₂' : Scheme.{u}} (f₂' : Z₂' ⟶ U) [LocallyOfFiniteType f₂'] (p₂' : ℤ)
      (c₂' : BivariantClass C (gysinSystemOfInvertible C) (f₂' ≫ (i ≫ sX)) (i ≫ sX) f₂' rfl p₂'),
      BivariantCommute C (gysinSystemOfInvertible C) (i ≫ sX) j f₂' p p₂' a c₂')
    (hb : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ X) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl p₂),
      BivariantCommute C (gysinSystemOfInvertible C) sX i f₂ q p₂ b c₂)
    {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ X) [LocallyOfFiniteType f₂] (p₂ : ℤ)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl p₂)
    {f₁ : W ⟶ X} [LocallyOfFiniteType f₁] (e : j ≫ i = f₁) :
    BivariantCommute C (gysinSystemOfInvertible C) sX f₁ f₂ (p + q) p₂
      (BivariantClass.congrHom e rfl
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (j ≫ i)
          ((Category.assoc j i sX).symm.trans (congrArg (· ≫ sX) e)) rfl
          (hv' := congrArg (· ≫ sX) e) (p + q)
          (bivariantCompositeOfInvertible C (j ≫ (i ≫ sX)) (i ≫ sX) sX j i rfl rfl p q a b)))
      c₂ :=
  bivariantCommute_bivariantComposite C (gysinSystemOfInvertible C) sX j i p q
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) a b ha f₂ p₂ c₂
    (hb f₂ p₂ c₂) e

end Composite

end Stacks.Chow

end
