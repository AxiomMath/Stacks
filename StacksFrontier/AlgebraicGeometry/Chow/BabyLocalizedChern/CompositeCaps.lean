module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BivariantCommutation

/-!
# Cap operations of composites with Chow cohomology classes, and of localized classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `g : X' ⟶ X` be
locally of finite type and let `c ∈ A^q(X' ⟶ X)` be a bivariant class. For `x ∈ A^p(X)` and
`x' ∈ A^p(X')` (Stacks 0B7E) the composites `c ∘ x` and `x' ∘ c` of Stacks 0B75 cap, on a test
scheme `t : T ⟶ X`, as

  `(c ∘ x) ∩ α = c ∩ (x ∩ α)`  and  `(x' ∘ c) ∩ α = x' ∩ (c ∩ α)`,

where `x ∩ -` and `x' ∩ -` are the operations of the Chow cohomology classes on the test schemes
`T ⟶ X` and `X' ×_X T ⟶ X'`. Both identities hold on the nose, without any identification of
schemes, because each side lands in the Chow group of `X' ×_X T`.

For a set-theoretic cover `X = X₁ ∪ X₂` by closed subschemes and a class `κ ∈ A^p(X)` vanishing on
`X₁`, the localized class `κ' ∈ A^p(X₂ ⟶ X)` of the proof of Stacks 0F9H built from the
restriction of `κ` to `X₂` satisfies `i_{2,*} ∘ κ' = κ`: this is Stacks 0F9I, read on every test
scheme.

## Main results

* `Stacks.Chow.bivariantCompositeIdRightHom_cap_heq_idRule` — `(c ∘ x) ∩ α = c ∩ (x ∩ α)`.
* `Stacks.Chow.bivariantCompositeIdLeftHom_cap_heq_idRule` — `(x' ∘ c) ∩ α = x' ∩ (c ∩ α)`.
* `Stacks.Chow.chowPush_closedCoverLocalizedClass_cap` — `i'_{2,*}(κ' ∩ α) = κ ∩ α`.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Pushforward into a chosen pullback -/

section Pullback

variable (C : ChowSituation.{u})

/-- Two proper morphisms into the chosen pullbacks `Y ×_{f,X} T` and `Y ×_{f',X} T` for equal
`f = f'`, with the same two components, push forward to heterogeneously equal classes. -/
theorem chowPush_heq_of_pullback_comp {Y X T A : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sA : A ⟶ C.S) [LocallyOfFiniteType sA] {f f' : Y ⟶ X}
    (hff : f = f') (t : T ⟶ X) [LocallyOfFiniteType t]
    [LocallyOfFiniteType (pullback.fst f t ≫ sY)] [LocallyOfFiniteType (pullback.fst f' t ≫ sY)]
    (u : A ⟶ pullback f t) [IsProper u] (u' : A ⟶ pullback f' t) [IsProper u']
    (h₁ : u ≫ pullback.fst f t = u' ≫ pullback.fst f' t)
    (h₂ : u ≫ pullback.snd f t = u' ≫ pullback.snd f' t)
    (hu : u ≫ pullback.fst f t ≫ sY = sA) (hu' : u' ≫ pullback.fst f' t ≫ sY = sA) (k : ℤ)
    (x : chowGroup C sA k) :
    chowPush C sA (pullback.fst f t ≫ sY) u hu k x ≍
      chowPush C sA (pullback.fst f' t ≫ sY) u' hu' k x := by
  subst hff
  obtain rfl : u = u' := pullback.hom_ext h₁ h₂
  rfl

/-- **Stacks 0B76 (1) along an isomorphism of test schemes presented by an equality.** For an
isomorphism `h : T'' ⟶ T` with `h ≫ t = m`, the cap of `c` at `t` of the pushforward along `h` is
the pushforward of the cap at `m` along the induced map of base changes. -/
theorem BivariantClass.cap_chowPushforwardOfIso_map {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) {T T'' : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (h : T'' ⟶ T) [IsIso h] (m : T'' ⟶ Y) [LocallyOfFiniteType m]
    (hm : h ≫ t = m) (k : ℤ) (y : chowGroup C (m ≫ sY) k) :
    c.cap t k (chowPushforwardOfIso C (m ≫ sY) (t ≫ sY) h (by rw [← hm, Category.assoc]) k y) =
      chowPush C (pullback.fst f m ≫ sX) (pullback.fst f t ≫ sX)
        (pullback.map f m f t (𝟙 X) h (𝟙 Y) (by simp) (by rw [Category.comp_id, hm]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.comp_id]) (k - p)
        (c.cap m k y) := by
  subst hm
  exact c.cap_properPushforward t h (bivariantBaseChangeMap f t h)
    (isPullback_bivariantBaseChangeMap f t h) (by rw [pullbackMap_fst, Category.comp_id]) k y

end Pullback

/-! ### The two composites with a Chow cohomology class -/

section Composites

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : X' ⟶ X) [LocallyOfFiniteType g]
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward) (p q : ℤ)
  (c : BivariantClass C G (g ≫ sX) sX g rfl q)

/-- **The cap operation of `c ∘ x`.** For `x ∈ A^p(X)` and `c ∈ A^q(X' ⟶ X)`, on a test scheme
`t : T ⟶ X` the composite caps as `c ∩ (x ∩ α)`, with `x ∩ -` the operation of `x` on `T`. The two
sides lie in the Chow groups of `X' ×_X T` of degrees `k - (q + p)` and `(k - p) - q`. -/
theorem bivariantCompositeIdRightHom_cap_heq_idRule (x : chowCohomologyComponent C G sX p)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    (bivariantCompositeIdRightHom C G sX g hgys hgysc p q c x).cap t k α ≍
      c.cap t (k - p) (x.idRule C sX G t k α) := by
  refine (bivariantCompositeIdRightHom_cap C G sX g hgys hgysc p q c x t k α).trans ?_
  rw [bivariantCompositeCap_apply, BivariantClass.idRule_apply]
  have hm : pullback.snd (𝟙 X) t ≫ t = pullback.fst (𝟙 X) t := by
    rw [← pullback.condition, Category.comp_id]
  have key := BivariantClass.cap_chowPushforwardOfIso_map C c t (pullback.snd (𝟙 X) t)
    (pullback.fst (𝟙 X) t) hm (k - p) (x.cap t k α)
  refine HEq.trans ?_ (heq_of_eq key.symm)
  exact chowPush_heq_of_pullback_comp C (g ≫ sX) _ (Category.comp_id g) t _ _
    (by rw [pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst, Category.comp_id])
    (by rw [pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd]) _ _ _ _

/-- **The cap operation of `x' ∘ c`.** For `x' ∈ A^p(X')` and `c ∈ A^q(X' ⟶ X)`, on a test scheme
`t : T ⟶ X` the composite caps as `x' ∩ (c ∩ α)`, with `x' ∩ -` the operation of `x'` on the test
scheme `X' ×_X T ⟶ X'`. The two sides lie in the Chow groups of `X' ×_X T` of degrees
`k - (q + p)` and `(k - q) - p`. -/
theorem bivariantCompositeIdLeftHom_cap_heq_idRule (x' : chowCohomologyComponent C G (g ≫ sX) p)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    (bivariantCompositeIdLeftHom C G sX g hgys hgysc p q c x').cap t k α ≍
      x'.idRule C (g ≫ sX) G (pullback.fst g t) (k - q) (c.cap t k α) := by
  refine (bivariantCompositeIdLeftHom_cap C G sX g hgys hgysc p q c x' t k α).trans ?_
  rw [bivariantCompositeCap_apply, BivariantClass.idRule_apply]
  exact chowPush_heq_of_pullback_comp C (g ≫ sX) _ (Category.id_comp g) t _ _
    (by rw [pullbackRightPullbackFstIso_hom_fst, ← pullback.condition, Category.comp_id])
    (by rw [pullbackRightPullbackFstIso_hom_snd]) _ _ _ _

end Composites

/-! ### Stacks 0F9I for the localized class -/

section Localized

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}
  (κX : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
  (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p)
  (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) (pullback.snd i₁ i₂) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)

/-- The projection formula for the operation of `κX` along the second projection of the base
change of a closed immersion `i` along a test scheme `g`. -/
private theorem idRule_chowPush_pullback_snd {Y T : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (g : T ⟶ X) [LocallyOfFiniteType g] {k : ℤ}
    (y : chowGroup C (pullback.fst i g ≫ (i ≫ sX)) k) :
    κX.idRule C sX (gysinSystemOfInvertible C) g k
        (chowPush C (pullback.fst i g ≫ (i ≫ sX)) (g ≫ sX) (pullback.snd i g)
          (pullbackSnd_comp_structureMorphism_eq C (i ≫ sX) sX i rfl g) k y) =
      chowPush C ((pullback.snd i g ≫ g) ≫ sX) (g ≫ sX) (pullback.snd i g)
        (by rw [Category.assoc]) (k - p)
        (κX.idRule C sX (gysinSystemOfInvertible C) (pullback.snd i g ≫ g) k
          (chowGroupCongr C (by rw [← pullback.condition, Category.assoc]) k y)) :=
  idRule_chowPush_of_eq C sX κX g (pullback.snd i g ≫ g) (pullback.snd i g) rfl
    (pullback.fst i g ≫ (i ≫ sX)) (by rw [← pullback.condition, Category.assoc])
    (by rw [← Category.assoc]; exact pullbackSnd_comp_structureMorphism_eq C (i ≫ sX) sX i rfl g)
    k y

/-- **Stacks 0F9I, on every test scheme.** Let `X = X₁ ∪ X₂` set theoretically, let
`κX ∈ A^p(X)` restrict to `κ ∈ A^p(X₂)` and to `0 ∈ A^p(X₁)`, and let `κ' ∈ A^p(X₂ ⟶ X)` be the
localized class of `κ` (the class of Stacks 0F9H). Then `i'_{2,*}(κ' ∩ α) = κX ∩ α` for every
test scheme `g : T ⟶ X` and `α ∈ A_k(T)`; that is, `i_{2,*} ∘ κ' = κX`. -/
theorem chowPush_closedCoverLocalizedClass_cap
    (hκX₂ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κX = κ)
    (hκX₁ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₁ p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κX = 0)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    chowPush C (pullback.fst i₂ g ≫ (i₂ ≫ sX)) (g ≫ sX) (pullback.snd i₂ g)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl g) (k - p)
        ((closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ).cap g k
          α) =
      κX.idRule C sX (gysinSystemOfInvertible C) g k α := by
  have hF := closedCover_addMonoidHom_ext C (g ≫ sX) _ _
    (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism_eq C (i₁ ≫ sX) sX i₁ rfl g)
    (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl g)
    (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover g) k
    ((chowPush C (pullback.fst i₂ g ≫ (i₂ ≫ sX)) (g ≫ sX) (pullback.snd i₂ g)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl g) (k - p)).comp
      ((closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ).cap g k))
    (κX.idRule C sX (gysinSystemOfInvertible C) g k) ?_ ?_
  · exact DFunLike.congr_fun hF α
  · intro x
    rw [AddMonoidHom.comp_apply, closedCoverLocalizedClass_cap_pushforward_left, map_zero,
      idRule_chowPush_pullback_snd C sX κX i₁ g,
      idRule_eq_zero_of_chowCohomologyRestriction_eq_zero C sX κX i₁ hκX₁
        (pullback.snd i₁ g ≫ g) (pullback.fst i₁ g) pullback.condition, map_zero]
  · intro y
    rw [AddMonoidHom.comp_apply, closedCoverLocalizedClass_cap_pushforward_right,
      idRule_chowPush_pullback_snd C sX κX i₂ g]
    subst hκX₂
    refine eq_of_heq (properChowPushforward_heq_congr_base C (pullback.snd i₂ g)
      (by rw [← Category.assoc, pullback.condition, Category.assoc]) rfl _ _ rfl _ _ _ _ ?_)
    refine (BivariantClass.idRule_chowCohomologyRestriction_heq i₂ κX (pullback.fst i₂ g) k y
      (chowGroupCongr C (Category.assoc _ _ _).symm k y) (chowGroupCongr_heq C _ k y).symm).trans
      ?_
    exact IdentityCapRule.heq_congr C sX (κX.idRule C sX (gysinSystemOfInvertible C))
      pullback.condition rfl ((chowGroupCongr_heq C _ k y).trans (chowGroupCongr_heq C _ k y).symm)

end Localized

end Stacks.Chow

end
