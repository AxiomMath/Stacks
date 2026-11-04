module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCoverProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedImmersionCoverExactSequence

/-!
# Products of classes supported on two closed subschemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f₁ : Z₁ ⟶ X`,
`f₂ : Z₂ ⟶ X` be closed immersions of schemes locally of finite type over `S`. A class
`c₁ ∈ A^p(Z₁ ⟶ X)` and a class `c₂ ∈ A^q(Z₂ ⟶ X)` have a product
`c₁ c₂ = res(c₁) ∘ c₂ ∈ A^{p+q}(Z₁ ×_X Z₂ ⟶ X)`, where `res(c₁) ∈ A^p(Z₁ ×_X Z₂ ⟶ Z₂)` is the
restriction of Stacks 0F9Z along `f₂` and `∘` is the composition of Stacks 0B75; on a test scheme
it caps with `c₂` and then with `c₁`. This is the product by juxtaposition of Stacks 0FE5.

This file computes the product on classes extended from members of closed covers (Stacks 0F9H,
`Stacks.Chow.closedCoverExtension`): if `c₁` extends `a ∈ A^p(Z₁)` along `X = X₁ ∪ Z₁` and `c₂`
extends `b ∈ A^q(Z₂)` along `X = X₁' ∪ Z₂`, then `c₁ c₂` extends the product of the restrictions of
`a` and `b` to `Z₁ ×_X Z₂` along every closed cover `X = Y ∪ (Z₁ ×_X Z₂)` with `Y` inside
`X₁ ∪ X₁'`.

## Main definitions

* `Stacks.Chow.supportedIntersectionMul` — the product
  `A^p(Z₁ ⟶ X) × A^q(Z₂ ⟶ X) ⟶ A^{p+q}(W ⟶ X)`, for `W` presented as `Z₁ ×_X Z₂` by a pullback
  square.
* `Stacks.Chow.BivariantClass.CapVanishesOver` — a bivariant class kills the classes coming from
  schemes over a given morphism; for a class of `A^*(Z)` this is
  `Stacks.Chow.BivariantClass.VanishesOver` read through pushforwards.
* `Stacks.Chow.BivariantClass.IsRestriction` — a Chow cohomology class operates on test schemes
  as the restriction of another one does.

## Main results

* `Stacks.Chow.supportedIntersectionMul_cap` — the product on the test schemes.
* `Stacks.Chow.supportedIntersectionMul_cap_second` — the first formula of Stacks 0F9H for a
  product of extensions.
* `Stacks.Chow.IsClosedCoverExtension.supportedIntersectionMul` — a product of extensions is an
  extension.
* `Stacks.Chow.IsClosedCoverExtension.capVanishesOver`,
  `Stacks.Chow.isClosedCoverExtension_of_capVanishesOver` — the second formula of Stacks 0F9H as
  capping to zero over the first member of the cover.
* `Stacks.Chow.IsClosedCoverExtension.vanishesOver` — a class admitting an extension along a
  closed cover vanishes over the intersection of the two members.
* `Stacks.Chow.BivariantClass.CapVanishesOver.of_range_subset` — capping to zero over two closed
  subschemes implies capping to zero over every morphism with image in their union (Stacks 0F94).

## Implementation notes

The product is defined for any pullback square `W = Z₁ ×_X Z₂` rather than for the chosen
fibre product, by transporting along the comparison isomorphism (`Stacks.Chow.bivariantTransport`).
This makes both orders of the factors land in the same group: the product of a class on `Z₂` and
a class on `Z₁` is the product along the flipped square.

## References

* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Classes capping to zero over a morphism -/

section CapVanishes

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X W V : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {f : W ⟶ X}
  [LocallyOfFiniteType f] {hf : f ≫ sX = sW} {p : ℤ}

/-- A bivariant class `c ∈ A^p(W ⟶ X)` *caps to zero over* a morphism `z : V ⟶ X` when, on every
test scheme `g : T ⟶ X`, it kills the pushforward `e_* γ` along every proper `e : T₀ ⟶ T` such
that `e ≫ g` factors through `z`. The second formula `c ∩ i_{1,*} α₁ = 0` of Stacks 0F9H is this
property for `z = i₁` (`Stacks.Chow.IsClosedCoverExtension.capVanishesOver`). -/
def BivariantClass.CapVanishesOver (c : BivariantClass C G sW sX f hf p) (z : V ⟶ X) : Prop :=
  ∀ ⦃T T₀ : Scheme.{u}⦄ (g : T ⟶ X) [LocallyOfFiniteType g] (e : T₀ ⟶ T) [IsProper e]
    (m : T₀ ⟶ V), m ≫ z = e ≫ g → ∀ (sT₀ : T₀ ⟶ C.S) [LocallyOfFiniteType sT₀]
    (he : e ≫ g ≫ sX = sT₀) (k : ℤ) (γ : chowGroup C sT₀ k),
    c.cap g k (chowPush C sT₀ (g ≫ sX) e he k γ) = 0

variable {c : BivariantClass C G sW sX f hf p}

/-- **Capping to zero over a closed cover of the image.** Let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be
closed immersions. If `c` caps to zero over `i₁` and over `i₂`, it caps to zero over every
`z : V ⟶ X` whose image lies in the union of their images: by Stacks 0F94, a class on a scheme
`T₀` over `V` is the sum of the pushforwards of classes on `T₀ ×_X X₁` and `T₀ ×_X X₂`. -/
theorem BivariantClass.CapVanishesOver.of_range_subset {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X)
    (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂] (z : V ⟶ X)
    (hz : Set.range z ⊆ Set.range i₁ ∪ Set.range i₂) (h₁ : c.CapVanishesOver i₁)
    (h₂ : c.CapVanishesOver i₂) : c.CapVanishesOver z := by
  intro T T₀ g _ e _ m hm sT₀ _ he k γ
  set n := m ≫ z
  have hrange : Set.range (pullback.snd i₁ n) ∪ Set.range (pullback.snd i₂ n) = Set.univ := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union]
    refine Set.eq_univ_of_forall fun t ↦ hz ⟨m.base t, ?_⟩
    simp [n, Scheme.Hom.comp_base]
  obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := surjective_chowPushforwardOfIsClosedImmersion_coprod C sT₀
    (pullback.snd i₁ n) (pullback.snd i₂ n) _ _ rfl rfl k hrange γ
  have hcap : ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i], c.CapVanishesOver i →
      ∀ γ' : chowGroup C (pullback.snd i n ≫ sT₀) k,
      c.cap g k (chowPush C sT₀ (g ≫ sX) e he k (chowPush C _ sT₀ (pullback.snd i n) rfl k γ')) =
        0 := by
    intro Y i _ h γ'
    rw [chowPush_comp C _ _ _ (pullback.snd i n) e _ rfl rfl he (by rw [Category.assoc, he])]
    exact h g _ _ (by rw [pullback.condition, hm, Category.assoc]) _ _ k γ'
  change chowPush C _ sT₀ _ rfl k γ₁ + chowPush C _ sT₀ _ rfl k γ₂ = γ at hγ
  rw [← hγ, map_add, map_add, hcap i₁ h₁, hcap i₂ h₂, add_zero]

end CapVanishes

/-! ### The characterization of Stacks 0F9H, on classes pushed forward to a test scheme -/

section Characterization

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X X₁ X₂ : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {i₁ : X₁ ⟶ X} {i₂ : X₂ ⟶ X} [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] {sX₂ : X₂ ⟶ C.S} [LocallyOfFiniteType sX₂] {hi₂ : i₂ ≫ sX = sX₂}
  {p : ℤ} {a : chowCohomologyComponent C G sX₂ p} {c : BivariantClass C G sX₂ sX i₂ hi₂ p}

/-- **The first formula of Stacks 0F9H on classes from schemes over `X₂`.** If `c` extends `a`,
then for a proper `e : T₀ ⟶ T` whose composite with the test morphism factors as `m ≫ i₂`, the
cap product of `e_* γ` is the pushforward of `a ∩ γ` along the induced `T₀ ⟶ T ×_X X₂`. -/
theorem IsClosedCoverExtension.cap_chowPush_second
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c) {T T₀ : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (e : T₀ ⟶ T) [IsProper e] (m : T₀ ⟶ X₂) [LocallyOfFiniteType m]
    (hm : m ≫ i₂ = e ≫ g) (k : ℤ) (γ : chowGroup C (m ≫ sX₂) k) :
    c.cap g k (chowPush C _ _ e (by rw [← hi₂, ← Category.assoc, ← hm, Category.assoc]) k γ) =
      chowPush C _ _ (pullback.lift m e hm) (by rw [← Category.assoc, pullback.lift_fst]) (k - p)
        (a.idRule C sX₂ G m k γ) := by
  rw [← chowPush_comp C _ _ _ (pullback.lift m e hm) (pullback.snd i₂ g) e
    (pullback.lift_snd _ _ _) (by rw [← Category.assoc, pullback.lift_fst])
    (pullbackSnd_comp_structureMorphism hi₂ g), hc.1]
  exact a.idRule_chowPush C G sX₂ (pullback.fst i₂ g) (pullback.lift m e hm) m
    (pullback.lift_fst _ _ _) k γ

/-- **The second formula of Stacks 0F9H on classes from schemes over `X₁`.** An extension caps to
zero over `i₁`. -/
theorem IsClosedCoverExtension.capVanishesOver
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c) : c.CapVanishesOver i₁ := by
  intro T T₀ g _ e _ m hm sT₀ _ he k γ
  have hu : pullback.lift m e hm ≫ (pullback.fst i₁ g ≫ (i₁ ≫ sX)) = sT₀ := by
    rw [← he, pullback.lift_fst_assoc, ← Category.assoc, hm, Category.assoc]
  rw [← chowPush_comp C _ _ _ (pullback.lift m e hm) (pullback.snd i₁ g) e
    (pullback.lift_snd _ _ _) hu (pullbackSnd_comp_structureMorphism rfl g), hc.2]

variable (i₁) in
/-- **The characterization of Stacks 0F9H from the first formula and capping to zero.** A class
which caps the classes from `T ×_X X₂` as `a` does and caps to zero over `i₁` extends `a`. -/
theorem isClosedCoverExtension_of_capVanishesOver
    (h₂ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (pullback.fst i₂ g ≫ sX₂) k),
      c.cap g k
          (chowPush C _ _ (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism hi₂ g) k α) =
        a.idRule C sX₂ G (pullback.fst i₂ g) k α)
    (h₁ : c.CapVanishesOver i₁) : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c :=
  ⟨h₂, fun g _ k α ↦ h₁ g (pullback.snd i₁ g) (pullback.fst i₁ g) pullback.condition _
    (pullbackSnd_comp_structureMorphism rfl g) k α⟩

/-- The base change of a closed immersion `i₂` along a morphism factoring through it is an
isomorphism, with inverse the induced section. -/
theorem isIso_pullbackLift_of_comp {T : Scheme.{u}} (m : T ⟶ X₂) (g : T ⟶ X)
    (hm : m ≫ i₂ = 𝟙 T ≫ g) : IsIso (pullback.lift m (𝟙 T) hm) := by
  refine ⟨⟨pullback.snd i₂ g, pullback.lift_snd _ _ _, pullback.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono i₂, Category.assoc,
      hm, Category.id_comp, pullback.condition]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

/-- **An extension forces the vanishing.** If `c ∈ A^p(X₂ ⟶ X)` extends `a ∈ A^p(X₂)` along the
closed cover, then `a` vanishes over `X₁ ×_X X₂ ⟶ X₂`: a class on a scheme `T` over
`X₁ ×_X X₂` is pushed forward from `T ×_X X₂` and from `T ×_X X₁` at once, so its cap product
with `c` is both `a ∩ α` and `0`. -/
theorem IsClosedCoverExtension.vanishesOver
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c) :
    BivariantClass.VanishesOver a (pullback.snd i₁ i₂) := by
  intro T t _ k α
  set m := t ≫ pullback.snd i₁ i₂
  have hm : m ≫ i₂ = 𝟙 T ≫ m ≫ i₂ := (Category.id_comp _).symm
  have hm₁ : (t ≫ pullback.fst i₁ i₂) ≫ i₁ = 𝟙 T ≫ m ≫ i₂ := by
    rw [Category.id_comp, Category.assoc, pullback.condition, ← Category.assoc]
  have h₂ := hc.cap_chowPush_second (m ≫ i₂) (𝟙 T) m hm k α
  have h₁ := hc.capVanishesOver (m ≫ i₂) (𝟙 T) (t ≫ pullback.fst i₁ i₂) hm₁ (m ≫ sX₂)
    (by rw [Category.id_comp, Category.assoc, hi₂]) k α
  rw [h₁] at h₂
  have := isIso_pullbackLift_of_comp m (m ≫ i₂) hm
  have hid : a.idRule C sX₂ G m k α = 0 :=
    chowPushforwardOfIso_injective C _ _ (pullback.lift m (𝟙 T) hm) _ (k - p)
      (h₂.symm.trans (map_zero _).symm)
  rw [BivariantClass.idRule_apply] at hid
  exact chowPushforwardOfIso_injective C _ _ _ _ (k - p) (hid.trans (map_zero _).symm)

end Characterization

/-! ### Restrictions of Chow cohomology classes, read on the test schemes -/

section Restriction

variable {C : ChowSituation.{u}} {G : GysinSystem C} {W Z : Scheme.{u}} {sW : W ⟶ C.S}
  [LocallyOfFiniteType sW] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {p q : ℤ}

/-- A class `d ∈ A^p(W)` *is the restriction* of `a ∈ A^p(Z)` along `w : W ⟶ Z` when on every
test scheme `t : T ⟶ W` it operates as `a` does on `t ≫ w`. This is how the restriction of
Stacks 0B7F operates (`Stacks.Chow.TotalChowClass.isRestriction_res`), for any presentation of
the structure morphism of `W`. -/
def BivariantClass.IsRestriction (d : chowCohomologyComponent C G sW p)
    (a : chowCohomologyComponent C G sZ p) (w : W ⟶ Z) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ W) [LocallyOfFiniteType t] [LocallyOfFiniteType (t ≫ w)] (k : ℤ)
    (x : chowGroup C (t ≫ sW) k) (y : chowGroup C ((t ≫ w) ≫ sZ) k),
    x ≍ y → d.idRule C sW G t k x ≍ a.idRule C sZ G (t ≫ w) k y

/-- Restriction is compatible with products: if `d` and `e` are the restrictions of `a` and `b`,
then `d e` is the restriction of `a b`. -/
theorem BivariantClass.IsRestriction.mulId {w : W ⟶ Z}
    {d : chowCohomologyComponent C (gysinSystemOfInvertible C) sW p}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p}
    {e : chowCohomologyComponent C (gysinSystemOfInvertible C) sW q}
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ q}
    (hd : d.IsRestriction a w) (he : e.IsRestriction b w) :
    (d.mulId C sW e).IsRestriction (a.mulId C sZ b) w := by
  intro T t _ _ k x y hxy
  exact (BivariantClass.idRule_mulId C sW d e t k x).trans
    ((hd t (k - q) _ _ (he t k x y hxy)).trans
      (BivariantClass.idRule_mulId C sZ a b (t ≫ w) k y).symm)

/-- **The restriction of a total class is the restriction in every degree.** The component of
degree `p` of the restriction of a total class `A` along `w : W ⟶ Z`, for any presentation of the
structure morphism of `W`, is the restriction of the component `A_p`. -/
theorem TotalChowClass.isRestriction_res (A : TotalChowClass C sZ) (w : W ⟶ Z)
    [LocallyOfFiniteType w] (hs : w ≫ sZ = sW) (p : ℕ) :
    BivariantClass.IsRestriction (TotalChowClass.res w hs A p) (A p) w := by
  intro T t _ _ k x y hxy
  exact TotalChowClass.op_res_apply w hs A t k p x y hxy

end Restriction

/-! ### The product of classes supported on two closed subschemes -/

/-- Proper pushforward takes heterogeneously equal classes, for equal structure morphisms and
degrees, to heterogeneously equal classes. -/
theorem chowPush_heq (C : ChowSituation.{u}) {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB sB' : B ⟶ C.S}
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (u : A ⟶ B) [IsProper u]
    (hu : u ≫ sB = sA) (hu' : u ≫ sB' = sA') (hsA : sA = sA') (hsB : sB = sB') {k k' : ℤ}
    (hk : k = k') {x : chowGroup C sA k} {x' : chowGroup C sA' k'} (hx : x ≍ x') :
    chowPush C sA sB u hu k x ≍ chowPush C sA' sB' u hu' k' x' := by
  subst hsA hsB hk
  cases hx
  rfl

/-- Proper pushforward commutes with the transport of Chow groups along equalities of the
structure morphisms of its source and of its target. -/
private theorem chowGroupCongr_chowPush_chowGroupCongr (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    (hA : sA = sA') (hB : sB = sB') (u : A ⟶ B) [IsProper u] (hu : u ≫ sB = sA)
    (hu' : u ≫ sB' = sA') (k : ℤ) (x : chowGroup C sA k) :
    chowGroupCongr C hB k (chowPush C sA sB u hu k x) =
      chowPush C sA' sB' u hu' k (chowGroupCongr C hA k x) :=
  properChowPushforward_chowGroupCongr C hA hB u hu hu' k _ _ x

section IntersectionProduct

variable (C : ChowSituation.{u}) {X Z₁ Z₂ W : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] {w₁ : W ⟶ Z₁} {w₂ : W ⟶ Z₂} (sq : IsPullback w₁ w₂ f₁ f₂)
  (iW : W ⟶ X) [LocallyOfFiniteType iW] (hW : w₂ ≫ f₂ = iW) {p q : ℤ}

include hW in
omit [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂] [LocallyOfFiniteType iW] in
/-- The comparison `Z₁ ×_X Z₂ ≅ W` is an isomorphism over `X`. -/
theorem isoPullback_inv_comp_eq : sq.isoPullback.symm.hom ≫ iW = pullback.snd f₁ f₂ ≫ f₂ := by
  rw [Iso.symm_hom, ← hW, IsPullback.isoPullback_inv_snd_assoc]

/-- **The product `A^p(Z₁ ⟶ X) × A^q(Z₂ ⟶ X) ⟶ A^{p+q}(W ⟶ X)` of classes supported on two
closed subschemes**, with `W = Z₁ ×_X Z₂` presented by a pullback square:
`(c₁, c₂) ↦ res(c₁) ∘ c₂`, where `res(c₁) ∈ A^p(Z₁ ×_X Z₂ ⟶ Z₂)` is the restriction of Stacks 0F9Z
along `f₂` and `∘` is the composition of Stacks 0B75, transported to `W` along the comparison
isomorphism. This is the product written as juxtaposition in Stacks 0FE5; on test schemes it caps
with `c₂` and then with `c₁`. -/
def supportedIntersectionMul
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    BivariantClass C (gysinSystemOfInvertible C) (iW ≫ sX) sX iW rfl (p + q) :=
  bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (iW ≫ sX) sX
    (pullback.snd f₁ f₂ ≫ f₂)
    (comp_comp_structureMorphism_eq
      (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl)
    iW rfl sq.isoPullback.symm (isoPullback_inv_comp_eq f₁ f₂ sq iW hW) (p + q)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (bivariantCompositeOfInvertible C (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
      (pullback.snd f₁ f₂) f₂ (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂)
      rfl p q
      (bivariantRestriction C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl f₂ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₁) c₂)

/-- The identification `Z₁ ×_X (Z₂ ×_X T) ≅ W ×_X T` of the two schemes on which the iterated cap
product `c₁ ∩ (c₂ ∩ -)` and the cap product with the product class land. -/
def supportedIntersectionTestIso {T : Scheme.{u}} (g : T ⟶ X) :
    pullback f₁ (pullback.fst f₂ g ≫ f₂) ≅ pullback iW g :=
  (pullbackLeftPullbackSndIso f₁ f₂ (pullback.fst f₂ g)).symm ≪≫
    pullbackRightPullbackFstIso f₂ g (pullback.snd f₁ f₂) ≪≫
    transportPullbackIso (pullback.snd f₁ f₂ ≫ f₂) iW sq.isoPullback.symm
      (isoPullback_inv_comp_eq f₁ f₂ sq iW hW) g

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
  [LocallyOfFiniteType iW] in
/-- The identification of `Stacks.Chow.supportedIntersectionTestIso` is compatible with the
projections to the test scheme. -/
@[reassoc]
theorem supportedIntersectionTestIso_hom_snd {T : Scheme.{u}} (g : T ⟶ X) :
    (supportedIntersectionTestIso f₁ f₂ sq iW hW g).hom ≫ pullback.snd iW g =
      pullback.snd f₁ (pullback.fst f₂ g ≫ f₂) ≫ pullback.snd f₂ g := by
  simp [supportedIntersectionTestIso, transportPullbackIso]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
  [LocallyOfFiniteType iW] in
/-- The identification of `Stacks.Chow.supportedIntersectionTestIso` is compatible with the
projections to `Z₁`. -/
@[reassoc]
theorem supportedIntersectionTestIso_hom_fst_w₁ {T : Scheme.{u}} (g : T ⟶ X) :
    (supportedIntersectionTestIso f₁ f₂ sq iW hW g).hom ≫ pullback.fst iW g ≫ w₁ =
      pullback.fst f₁ (pullback.fst f₂ g ≫ f₂) := by
  simp [supportedIntersectionTestIso, transportPullbackIso]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
  [LocallyOfFiniteType iW] in
/-- The identification of `Stacks.Chow.supportedIntersectionTestIso` is compatible with the
projections to `Z₂`. -/
@[reassoc]
theorem supportedIntersectionTestIso_hom_fst_w₂ {T : Scheme.{u}} (g : T ⟶ X) :
    (supportedIntersectionTestIso f₁ f₂ sq iW hW g).hom ≫ pullback.fst iW g ≫ w₂ =
      pullback.snd f₁ (pullback.fst f₂ g ≫ f₂) ≫ pullback.fst f₂ g := by
  simp [supportedIntersectionTestIso, transportPullbackIso]

include sq hW in
omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
  [LocallyOfFiniteType iW] in
/-- The two structure morphisms of `W` over the base, through `Z₁` and through `X`, agree. -/
theorem comp_comp_eq_of_isPullback : w₁ ≫ f₁ ≫ sX = iW ≫ sX := by
  rw [← hW, Category.assoc, sq.w_assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
  [LocallyOfFiniteType iW] in
/-- The identification of `Stacks.Chow.supportedIntersectionTestIso` lies over the base. -/
theorem supportedIntersectionTestIso_hom_comp_base {T : Scheme.{u}} (g : T ⟶ X) :
    (supportedIntersectionTestIso f₁ f₂ sq iW hW g).hom ≫ (pullback.fst iW g ≫ (iW ≫ sX)) =
      pullback.fst f₁ (pullback.fst f₂ g ≫ f₂) ≫ (f₁ ≫ sX) := by
  rw [← comp_comp_eq_of_isPullback C sX f₁ f₂ sq iW hW,
    supportedIntersectionTestIso_hom_fst_w₁_assoc]

/-- **The product on the test schemes.** On a test scheme `g : T ⟶ X`, the cap product with
`res(c₁) ∘ c₂` is the iterated cap product `c₁ ∩ (c₂ ∩ α)`, computed on `Z₁ ×_X (Z₂ ×_X T)`, pushed
forward along the identification with `W ×_X T`; the two sides lie in the Chow groups of degrees
`k - (p + q)` and `(k - q) - p`. -/
theorem supportedIntersectionMul_cap
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂).cap g k α ≍
      chowPush C (pullback.fst f₁ (pullback.fst f₂ g ≫ f₂) ≫ (f₁ ≫ sX))
        (pullback.fst iW g ≫ (iW ≫ sX)) (supportedIntersectionTestIso f₁ f₂ sq iW hW g).hom
        (supportedIntersectionTestIso_hom_comp_base C sX f₁ f₂ sq iW hW g) ((k - q) - p)
        (c₁.cap (pullback.fst f₂ g ≫ f₂) (k - q)
          (chowGroupCongr C (Category.assoc _ _ _).symm (k - q) (c₂.cap g k α))) := by
  have hcomp : (bivariantCompositeOfInvertible C (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
      (pullback.snd f₁ f₂) f₂ (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂)
      rfl p q (bivariantRestriction C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl f₂ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₁) c₂).cap g k α =
      chowGroupDegreeEquiv C _ (by ring : (k - q) - p = k - (p + q))
        (bivariantCompositeCap C _ _ _ _ _ _ _ _ (properPushforwardDescends C) p q
          (bivariantRestriction C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl f₂ p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₁) c₂ g k α) := rfl
  rw [supportedIntersectionMul, bivariantTransport_cap, bivariantTransportCap_apply, hcomp,
    bivariantCompositeCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    (chowGroupDegreeEquiv_heq C _ _ _)).trans (heq_of_eq ?_)
  change chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _)) = _
  rw [chowPush_comp C _ _ _ _ _ _ rfl, chowPush_comp C _ _ _ _ _ _ rfl]
  · rfl
  all_goals
    rw [← comp_comp_eq_of_isPullback C sX f₁ f₂ sq iW hW]
    simp [transportPullbackIso]

/-- **The product caps to zero where the second factor does.** -/
theorem BivariantClass.CapVanishesOver.supportedIntersectionMul_right {V : Scheme.{u}}
    {z : V ⟶ X} (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    {c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q}
    (h : c₂.CapVanishesOver z) :
    (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂).CapVanishesOver z := by
  intro T T₀ g _ e _ m hm sT₀ _ he k γ
  have key := supportedIntersectionMul_cap C sX f₁ f₂ sq iW hW c₁ c₂ g k
    (chowPush C sT₀ (g ≫ sX) e he k γ)
  rw [h g e m hm sT₀ he k γ, map_zero, map_zero, map_zero] at key
  exact chowGroup_eq_zero_of_heq_zero C (by ring) key

/-- **The product caps to zero where the first factor does.** By Stacks 0B76 (1) for `c₂`, the
class `c₂ ∩ e_* γ` is pushed forward from `(T₀ ×_X Z₂)`, which lies over `z` when `T₀` does. -/
theorem BivariantClass.CapVanishesOver.supportedIntersectionMul_left {V : Scheme.{u}}
    {z : V ⟶ X} {c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p}
    (h : c₁.CapVanishesOver z)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂).CapVanishesOver z := by
  intro T T₀ g _ e _ m hm sT₀ _ he k γ
  subst he
  have hs : e ≫ g ≫ sX = (e ≫ g) ≫ sX := (Category.assoc _ _ _).symm
  set e' := bivariantBaseChangeMap f₂ g e
  have sq' := isPullback_bivariantBaseChangeMap f₂ g e
  have he'fst : e' ≫ pullback.fst f₂ g = pullback.fst f₂ (e ≫ g) :=
    bivariantBaseChangeMap_fst f₂ g e
  have : IsProper e' := MorphismProperty.of_isPullback sq' (P := @IsProper) inferInstance
  have hγ : chowPush C (e ≫ g ≫ sX) (g ≫ sX) e rfl k γ =
      chowPush C ((e ≫ g) ≫ sX) (g ≫ sX) e hs k (chowGroupCongr C hs k γ) :=
    chowGroupCongr_chowPush_chowGroupCongr C hs rfl e rfl hs k γ
  have hnat := c₂.proper_naturality g e e' sq' (bivariantBaseChangeMap_fst f₂ g e) k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (chowGroupCongr C hs k γ)
  have key := supportedIntersectionMul_cap C sX f₁ f₂ sq iW hW c₁ c₂ g k
    (chowPush C (e ≫ g ≫ sX) (g ≫ sX) e rfl k γ)
  rw [hγ] at key
  change _ ≍ chowPush C _ _ _ _ _ (c₁.cap _ (k - q) (chowGroupCongr C _ (k - q)
    (c₂.cap g k (chowPush C _ _ e _ k _)))) at key
  rw [hnat] at key
  set δ := c₂.cap (e ≫ g) k (chowGroupCongr C hs k γ)
  have hs' : pullback.fst f₂ (e ≫ g) ≫ f₂ ≫ sX = (pullback.fst f₂ (e ≫ g) ≫ f₂) ≫ sX :=
    (Category.assoc _ _ _).symm
  have hcongr : chowGroupCongr C (Category.assoc _ _ _).symm (k - q)
      (properChowPushforward C _ _ e' (by rw [← Category.assoc, bivariantBaseChangeMap_fst])
        (k - q) (properPushforwardDescends C _ _ _ _ _) δ) =
      chowPush C (pullback.fst f₂ (e ≫ g) ≫ f₂ ≫ sX) ((pullback.fst f₂ g ≫ f₂) ≫ sX) e'
        (by rw [← Category.assoc, ← Category.assoc, he'fst, Category.assoc]) (k - q) δ :=
    chowGroupCongr_chowPush_chowGroupCongr C rfl (Category.assoc _ _ _).symm e' _ _ (k - q) δ
  have hm' : (pullback.snd f₂ (e ≫ g) ≫ m) ≫ z = e' ≫ pullback.fst f₂ g ≫ f₂ := by
    rw [← Category.assoc e', he'fst, pullback.condition, Category.assoc, hm]
  rw [hcongr, h (pullback.fst f₂ g ≫ f₂) e' _ hm', map_zero] at key
  exact chowGroup_eq_zero_of_heq_zero C (by ring) key

variable [IsClosedImmersion f₁] [IsClosedImmersion f₂]

variable {C sX f₁ f₂ sq iW hW} in
/-- **The first formula of Stacks 0F9H for a product.** Let `c₁ ∈ A^p(Z₁ ⟶ X)` extend
`a ∈ A^p(Z₁)` and `c₂ ∈ A^q(Z₂ ⟶ X)` extend `b ∈ A^q(Z₂)` along closed covers `X = X₁ ∪ Z₁` and
`X = X₁' ∪ Z₂`, and let `d₁, d₂ ∈ A^*(W)` be the restrictions of `a` and `b` to `W = Z₁ ×_X Z₂`.
Then on every test scheme `g : T ⟶ X` the product
`c₁ c₂` caps the classes pushed forward from `T ×_X W` as `d₁ d₂ ∈ A^{p+q}(W)` does. -/
theorem supportedIntersectionMul_cap_second [IsClosedImmersion iW] {X₁ X₁' : Scheme.{u}}
    {g₁ : X₁ ⟶ X} {h₁ : X₁' ⟶ X} [IsClosedImmersion g₁] [IsClosedImmersion h₁]
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (f₁ ≫ sX) p}
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) (f₂ ≫ sX) q}
    {c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p}
    {c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q}
    (hc₁ : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX g₁ f₁ (f₁ ≫ sX) rfl a c₁)
    (hc₂ : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX h₁ f₂ (f₂ ≫ sX) rfl b c₂)
    {d₁ : chowCohomologyComponent C (gysinSystemOfInvertible C) (iW ≫ sX) p}
    {d₂ : chowCohomologyComponent C (gysinSystemOfInvertible C) (iW ≫ sX) q}
    (hd₁ : d₁.IsRestriction a w₁) (hd₂ : d₂.IsRestriction b w₂)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (pullback.fst iW g ≫ (iW ≫ sX)) k) :
    (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂).cap g k
        (chowPush C _ _ (pullback.snd iW g) (pullbackSnd_comp_structureMorphism rfl g) k α) =
      (d₁.mulId C (iW ≫ sX) d₂).idRule C (iW ≫ sX) _ (pullback.fst iW g) k α := by
  have : IsClosedImmersion w₁ := MorphismProperty.of_isPullback sq.flip
    (P := @IsClosedImmersion) inferInstance
  have : IsClosedImmersion w₂ := MorphismProperty.of_isPullback sq (P := @IsClosedImmersion)
    inferInstance
  set m := pullback.fst iW g
  set e := pullback.snd iW g
  have hw : w₁ ≫ f₁ = iW := sq.w.trans hW
  have hm₂ : (m ≫ w₂) ≫ f₂ = e ≫ g := by rw [Category.assoc, hW, pullback.condition]
  have hl₂ : pullback.lift (m ≫ w₂) e hm₂ ≫ pullback.fst f₂ g = m ≫ w₂ := pullback.lift_fst _ _ _
  have hl₂' : pullback.lift (m ≫ w₂) e hm₂ ≫ pullback.snd f₂ g = e := pullback.lift_snd _ _ _
  set lift₂ := pullback.lift (m ≫ w₂) e hm₂
  have hm₁ : (m ≫ w₁) ≫ f₁ = lift₂ ≫ pullback.fst f₂ g ≫ f₂ := by
    rw [reassoc_of% hl₂, Category.assoc, hw, hW]
  have hl₁ : pullback.lift (m ≫ w₁) lift₂ hm₁ ≫ pullback.fst f₁ _ = m ≫ w₁ :=
    pullback.lift_fst _ _ _
  have hl₁' : pullback.lift (m ≫ w₁) lift₂ hm₁ ≫ pullback.snd f₁ _ = lift₂ :=
    pullback.lift_snd _ _ _
  set lift₁ := pullback.lift (m ≫ w₁) lift₂ hm₁
  have h₂ : m ≫ iW ≫ sX = (m ≫ w₂) ≫ f₂ ≫ sX := by rw [Category.assoc, ← Category.assoc w₂, hW]
  have h₁₂ : (m ≫ w₂) ≫ f₂ ≫ sX = (m ≫ w₁) ≫ f₁ ≫ sX := by
    rw [Category.assoc, ← Category.assoc w₂, hW, Category.assoc, ← Category.assoc w₁, hw]
  set α₂ := chowGroupCongr C h₂ k α
  set β := b.idRule C (f₂ ≫ sX) _ (m ≫ w₂) k α₂
  set β₁ := chowGroupCongr C h₁₂ (k - q) β
  -- the cap product with `c₂`
  have hpush : chowPush C _ (g ≫ sX) e (pullbackSnd_comp_structureMorphism rfl g) k α =
      chowPush C ((m ≫ w₂) ≫ f₂ ≫ sX) (g ≫ sX) e
        (by rw [← Category.assoc, ← hm₂, Category.assoc]) k α₂ :=
    chowGroupCongr_chowPush_chowGroupCongr C h₂ rfl e
        (pullbackSnd_comp_structureMorphism rfl g) _ k α
  have hcap₂ := hc₂.cap_chowPush_second g e (m ≫ w₂) hm₂ k α₂
  -- transport to the test scheme `T ×_X Z₂ ⟶ X`
  have hcongr : chowGroupCongr C (Category.assoc _ _ _).symm (k - q)
      (chowPush C ((m ≫ w₂) ≫ f₂ ≫ sX) (pullback.fst f₂ g ≫ f₂ ≫ sX) lift₂
        (by rw [reassoc_of% hl₂, Category.assoc]) (k - q) β) =
      chowPush C ((m ≫ w₁) ≫ f₁ ≫ sX) ((pullback.fst f₂ g ≫ f₂) ≫ sX) lift₂
        (by rw [← h₁₂]; simp only [Category.assoc, reassoc_of% hl₂]) (k - q) β₁ :=
    chowGroupCongr_chowPush_chowGroupCongr C h₁₂ (Category.assoc _ _ _).symm lift₂ _ _ (k - q) β
  have hcap₁ := hc₁.cap_chowPush_second (pullback.fst f₂ g ≫ f₂) lift₂ (m ≫ w₁) hm₁ (k - q) β₁
  -- the identification of the two fibre products
  have hid : lift₁ ≫ (supportedIntersectionTestIso f₁ f₂ sq iW hW g).hom = 𝟙 _ := by
    refine pullback.hom_ext (sq.hom_ext ?_ ?_) ?_
    · rw [Category.assoc, Category.assoc, supportedIntersectionTestIso_hom_fst_w₁, hl₁,
        Category.id_comp]
    · rw [Category.assoc, Category.assoc, supportedIntersectionTestIso_hom_fst_w₂,
        reassoc_of% hl₁', hl₂, Category.id_comp]
    · rw [Category.assoc, supportedIntersectionTestIso_hom_snd, reassoc_of% hl₁', hl₂',
        Category.id_comp]
  have hbase : 𝟙 _ ≫ (m ≫ iW ≫ sX) = (m ≫ w₁) ≫ f₁ ≫ sX := by
    rw [Category.id_comp, h₂, h₁₂]
  rw [hpush]
  have key := supportedIntersectionMul_cap C sX f₁ f₂ sq iW hW c₁ c₂ g k
    (chowPush C ((m ≫ w₂) ≫ f₂ ≫ sX) (g ≫ sX) e
        (by rw [← Category.assoc, ← hm₂, Category.assoc]) k α₂)
  rw [hcap₂, hcongr, hcap₁, chowPush_comp C _ _ _ lift₁ _ (𝟙 _) hid _ _ hbase,
    chowPush_id_eq_chowGroupCongr] at key
  refine eq_of_heq (key.trans ((chowGroupCongr_heq C _ _ _).trans ?_))
  refine HEq.trans ?_ (BivariantClass.idRule_mulId C (iW ≫ sX) d₁ d₂ m k α).symm
  exact (hd₁ m (k - q) _ β₁ ((hd₂ m k α α₂ (chowGroupCongr_heq C h₂ k α).symm).trans
    (chowGroupCongr_heq C h₁₂ (k - q) β).symm)).symm

variable {C sX f₁ f₂ sq iW hW} in
/-- **The product of two extensions is an extension.** Let `c₁ ∈ A^p(Z₁ ⟶ X)` extend
`a ∈ A^p(Z₁)` along the closed cover `X = X₁ ∪ Z₁`, let `c₂ ∈ A^q(Z₂ ⟶ X)` extend `b ∈ A^q(Z₂)`
along `X = X₁' ∪ Z₂`, and let `d₁`, `d₂` be the restrictions of `a`, `b` to `W = Z₁ ×_X Z₂`. For
every closed subscheme `Y ⊆ X` whose points lie in `X₁ ∪ X₁'`, the product `c₁ c₂ ∈ A^{p+q}(W ⟶ X)`
satisfies the characterization of Stacks 0F9H for the extension of `d₁ d₂` along `X = Y ∪ W`. -/
theorem IsClosedCoverExtension.supportedIntersectionMul [IsClosedImmersion iW]
    {X₁ X₁' Y : Scheme.{u}} {g₁ : X₁ ⟶ X} {h₁ : X₁' ⟶ X} (iY : Y ⟶ X) [IsClosedImmersion g₁]
    [IsClosedImmersion h₁] [IsClosedImmersion iY]
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (f₁ ≫ sX) p}
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) (f₂ ≫ sX) q}
    {c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p}
    {c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q}
    (hc₁ : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX g₁ f₁ (f₁ ≫ sX) rfl a c₁)
    (hc₂ : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX h₁ f₂ (f₂ ≫ sX) rfl b c₂)
    {d₁ : chowCohomologyComponent C (gysinSystemOfInvertible C) (iW ≫ sX) p}
    {d₂ : chowCohomologyComponent C (gysinSystemOfInvertible C) (iW ≫ sX) q}
    (hd₁ : d₁.IsRestriction a w₁) (hd₂ : d₂.IsRestriction b w₂)
    (hY : Set.range iY ⊆ Set.range g₁ ∪ Set.range h₁) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX iY iW (iW ≫ sX) rfl
      (d₁.mulId C (iW ≫ sX) d₂) (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂) :=
  isClosedCoverExtension_of_capVanishesOver iY
    (fun g _ k α ↦ supportedIntersectionMul_cap_second hc₁ hc₂ hd₁ hd₂ g k α)
    (BivariantClass.CapVanishesOver.of_range_subset g₁ h₁ iY hY
      (hc₁.capVanishesOver.supportedIntersectionMul_left C sX f₁ f₂ sq iW hW c₂)
      (hc₂.capVanishesOver.supportedIntersectionMul_right C sX f₁ f₂ sq iW hW c₁))

end IntersectionProduct

end Stacks.Chow

end
