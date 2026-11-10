module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseTensor
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BivariantCommute

/-!
# The classes of the baby case commute with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions with
`X = X₁ ∪ X₂` set-theoretically, and let `E₂ ∈ D(𝒪_{X₂})` have defined Chern classes and
restrict on `X₁ ∩ X₂` to zero, resp. to a finite locally free module of rank `< p` in degree `0`.
Let `P'_p(E₂)`, resp. `c'_p(E₂)`, in `A^p(X₂ ⟶ X)` be the classes of Stacks 0F9H. **Stacks 0FAJ**
says that for `f : Y ⟶ X` locally of finite type and `c ∈ A^*(Y ⟶ X)`

  `c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c`,   resp.   `c ∘ c'_p(E₂) = c'_p(Lf₂^*E₂) ∘ c`,

where `f₂ : Y₂ ⟶ X₂` is the base change of `f`, `P'_p(Lf₂^*E₂)`, resp. `c'_p(Lf₂^*E₂)`, is the
class of Stacks 0F9H for the base-changed cover `Y = Y₁ ∪ Y₂`, and `c ∘ -` on the left is the
composite with the restriction of `c` to `X₂`.

To prove it, write a class on a test scheme `T ⟶ X` as `α₁ + α₂` along the cover (Stacks 0F94). On
the summand from `T ×_X X₁` both sides vanish: `P'_p(E₂)` kills it, and `c` maps it to a class from
`Y ×_X (T ×_X X₁)`, which lies over `Y₁`. On the summand from `T ×_X X₂` the class `P'_p(E₂)` acts
as `P_p(E₂)`, and the two sides are `c ∩ P_p(E₂) ∩ α₂` and `P_p(Lf₂^*E₂) ∩ c ∩ α₂`, which agree by
Stacks 0FAC. The argument uses about `P_p(E₂)` only that every bivariant class carries it to its
restriction (`Stacks.Chow.BivariantClass.IsBivariantCentral`), so it is carried out for the
extension `a'` of every such class `a ∈ A^p(X₂)`
(`Stacks.Chow.closedCoverExtension_commutesWithEveryClass`); the conclusion there is that `a'`
commutes with every bivariant class in the sense of Stacks 0FA2, from which the displayed equation
follows by Stacks 0FA2 and Stacks 0F9Z for the extension.

## Main definitions

* `Stacks.Chow.BivariantClass.IsBivariantCentral` — that every bivariant class `c ∈ A^q(Y ⟶ Z)`
  satisfies `c ∘ a = res(a) ∘ c`, the property Stacks 0FAC (2) asserts of the Chern classes.

## Main results

* `Stacks.Chow.isBivariantCentral_perfectPowerSumClass`,
  `Stacks.Chow.isBivariantCentral_perfectChernClass` — Stacks 0FAC (2), read as this property.
* `Stacks.Chow.closedCoverExtension_commutesWithEveryClass` — the extension of Stacks 0F9H of a
  class with this property commutes with every bivariant class.
* `Stacks.Chow.closedCoverPowerSum_commutesWithEveryClass`,
  `Stacks.Chow.closedCoverChernClass_commutesWithEveryClass` — so do `P'_p(E₂)` and `c'_p(E₂)`.
* `Stacks.Chow.bivariantRestriction_closedCoverPowerSum`,
  `Stacks.Chow.bivariantRestriction_closedCoverChernClass` — the restriction of `P'_p(E₂)`,
  resp. `c'_p(E₂)`, along `f` is `P'_p(Lf₂^*E₂)`, resp. `c'_p(Lf₂^*E₂)`.
* `Stacks.Chow.BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq` — two
  commuting classes satisfy `res(c₁) ∘ c₂ = res(c₂) ∘ c₁` as classes, Stacks 0FA2.
* `Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute` —
  the same for nonhomogeneous classes whose homogeneous components commute, as an equality in
  the graded group.
* `Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_closedCoverPowerSum`,
  `Stacks.Chow.nonhomogeneousBivariantTransport_compositeOfInvertible_closedCoverChernClass` —
  **Stacks 0FAJ**;
  `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible_closedCoverPowerSum`,
  `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible_closedCoverChernClass` are its
  case of a homogeneous `c`.

## Implementation notes

The source writes the equation in `A^*(Y₂ ⟶ Y)`; the two composites are classes for
`Y₂ ⟶ Y ⟶ X`, so they lie in `A^*(Y₂ ⟶ X)`, which is where it is stated here. The scheme `Y₂` is
`X₂ ×_X Y`, the second member of the base-changed cover of `Y`, on which `P'_p(Lf₂^*E₂)` is
defined; the composite `c ∘ P'_p(E₂) = res(c) ∘ P'_p(E₂)` is a class for `Y ×_X X₂ ⟶ X`, and it
is carried to `X₂ ×_X Y` by the transport of Stacks 0F9Z along the symmetry of the fibre product
(`Stacks.Chow.bivariantTransport`). The two composites have the degrees `q + p` and `p + q`,
whence the heterogeneous equality for a homogeneous `c`. For a general
`c ∈ A^*(Y ⟶ X) = ⊕_q A^q(Y ⟶ X)` the composition, restriction and transport are their additive
extensions to the graded groups, the two degrees are the same summand, and the equation is an
equality in `A^*(Y₂ ⟶ X)`. The structure morphism of
`X₂` is `i₂ ≫ sX`. The hypotheses on `Lf₂^*E₂` that the classes of Stacks 0F9H on `Y` require
follow from those on `E₂`, by `Stacks.Chow.isZero_derivedPullback_of_isZero_of_comp_eq` and
`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq`.

## References

* [Stacks Project, Tag 0FAJ](https://stacks.math.columbia.edu/tag/0FAJ)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Bookkeeping for cap products and pushforwards -/

section Helpers

variable {C : ChowSituation.{u}} {G : GysinSystem C}

/-- **Stacks 0B76 (1)** for a pushforward from an arbitrary structure morphism: capping
`c ∈ A^q(Z ⟶ X)` on the pushforward `e_* γ` along a proper `e : T₀ ⟶ T` of test schemes is the
pushforward of `c ∩ γ` along the base change of `e`, read against any structure morphism of
`Z ×_X T₀` equal to the given one. -/
theorem BivariantClass.cap_chowPush_eq {X Z T T₀ : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : Z ⟶ X}
    [LocallyOfFiniteType f] {hf : f ≫ sX = sZ} {q : ℤ} (c : BivariantClass C G sZ sX f hf q)
    (t : T ⟶ X) [LocallyOfFiniteType t] (e : T₀ ⟶ T) [IsProper e] {sT₀ : T₀ ⟶ C.S}
    [LocallyOfFiniteType sT₀] (he : e ≫ (t ≫ sX) = sT₀) {sB : pullback f (e ≫ t) ⟶ C.S}
    [LocallyOfFiniteType sB] (hB : pullback.fst f (e ≫ t) ≫ sZ = sB) (k : ℤ)
    (γ : chowGroup C sT₀ k) :
    c.cap t k (chowPush C sT₀ (t ≫ sX) e he k γ) =
      chowPush C sB (pullback.fst f t ≫ sZ) (bivariantBaseChangeMap f t e)
        (by rw [← hB, ← Category.assoc, bivariantBaseChangeMap_fst]) (k - q)
        (chowGroupCongr C hB (k - q)
          (c.cap (e ≫ t) k (chowGroupCongr C (by rw [← he, Category.assoc]) k γ))) := by
  subst he hB
  exact c.cap_properChowPushforward (properPushforwardDescends C) t e (e ≫ t) rfl _
    (bivariantBaseChangeMap_fst f t e) (by simp [bivariantBaseChangeMap]) k γ

/-- The operation of a class `a ∈ A^p(Z)` on a class pushed forward along an isomorphism of test
schemes is the pushforward of its operation, up to heterogeneous equality of the arguments. -/
theorem BivariantClass.idRule_chowPushforwardOfIso_heq {Z T T' : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {p : ℤ}
    (a : BivariantClass C G sZ sZ (𝟙 Z) (Category.id_comp sZ) p) (n : T ⟶ Z)
    [LocallyOfFiniteType n] (φ : T' ⟶ T) [IsIso φ] (m : T' ⟶ Z) [LocallyOfFiniteType m]
    (hm : φ ≫ n = m) {sT : T ⟶ C.S} [LocallyOfFiniteType sT] (hsT : sT = n ≫ sZ)
    {sT' : T' ⟶ C.S} [LocallyOfFiniteType sT'] (hφ : φ ≫ sT = sT')
    (k : ℤ) (x : chowGroup C sT' k) (z : chowGroup C (n ≫ sZ) k)
    (hz : z ≍ chowPushforwardOfIso C sT' sT φ hφ k x) (x' : chowGroup C (m ≫ sZ) k)
    (hx' : x ≍ x') :
    a.idRule C sZ G n k z ≍
      chowPushforwardOfIso C (m ≫ sZ) (n ≫ sZ) φ (by rw [← hm, Category.assoc]) (k - p)
        (a.idRule C sZ G m k x') := by
  subst hsT hm hφ
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hx'
  exact heq_of_eq (a.idRule_chowPush C G sZ n φ (φ ≫ n) rfl k x)

/-- Pushforward along an isomorphism is injective, up to heterogeneous equality of the structure
morphisms and of the degrees. -/
theorem heq_of_chowPushforwardOfIso_heq_heq {A D : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sD sD' : D ⟶ C.S}
    [LocallyOfFiniteType sD] [LocallyOfFiniteType sD'] (φ : A ⟶ D) [IsIso φ]
    (hφ : φ ≫ sD = sA) (hφ' : φ ≫ sD' = sA') (hA : sA = sA') (hD : sD = sD') {k l : ℤ}
    (hkl : k = l) {x : chowGroup C sA k} {y : chowGroup C sA' l}
    (h : chowPushforwardOfIso C sA sD φ hφ k x ≍ chowPushforwardOfIso C sA' sD' φ hφ' l y) :
    x ≍ y := by
  subst hA hD hkl
  exact heq_of_eq (chowPushforwardOfIso_injective C sA sD φ hφ k (eq_of_heq h))

end Helpers

/-! ### Classes carried to their restrictions by every bivariant class -/

section Central

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : ChowSituation.{u}} {Z : Scheme.{u}} {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
  {p : ℤ}

/-- A class `a ∈ A^p(Z)` is *bivariant central* when every bivariant class `c ∈ A^q(Y ⟶ Z)`, for
every `g : Y ⟶ Z` locally of finite type, satisfies

  `c ∘ a = res(a) ∘ c`   in   `A^{p+q}(Y ⟶ Z)`,

where `res(a) ∈ A^p(Y)` is the restriction of Stacks 0B7F. This is what Stacks 0FAC (2) asserts
of the Chern classes of a perfect object; for `g = 𝟙 Z` it says that `a` lies in the center of
`A^*(Z)`, Stacks 0FAC (1). The two composites have the degrees `q + p` and `p + q`, whence the
heterogeneous equality. -/
def BivariantClass.IsBivariantCentral
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p) : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (hg : g ≫ sZ = sY) (q : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q),
    bivariantCompositeOfInvertible C sY sZ sZ g (𝟙 Z) hg (Category.id_comp sZ) q p c a ≍
      bivariantCompositeOfInvertible C sY sY sZ (𝟙 Y) g (Category.id_comp sY) hg p q
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y) hg hg
          (hv := Category.id_comp _) (hv' := Category.id_comp sY) p
          (chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ g p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a)) c

variable {E : DerivedCategory Z.Modules} (hE : HasDefinedChernClasses E)

/-- **The power sums `P_p(E)` are bivariant central**: `c ∘ P_p(E) = P_p(Lg^*E) ∘ c` and
`P_p(Lg^*E)` is the restriction of `P_p(E)` along `g`. -/
theorem isBivariantCentral_perfectPowerSumClass (n : ℕ) :
    (perfectPowerSumComponent C sZ hE n).IsBivariantCentral := by
  intro Y sY _ g _ hg q c
  have h := c.heq_bivariantCompositeOfInvertible_perfectPowerSum hE n
  have e := TotalChowClass.res_apply_eq_bivariantClassCongrBase g hg
    (perfectPowerSum C sZ hE n) n
  rw [res_perfectPowerSum_derivedPullback C sZ hE g hg (hE.derivedPullback g) n] at e
  exact e ▸ h

/-- **The Chern classes `c_p(E)` are bivariant central** (Stacks 0FAC (2)):
`c ∘ c_p(E) = c_p(Lg^*E) ∘ c` and `c_p(Lg^*E)` is the restriction of `c_p(E)` along `g`. -/
theorem isBivariantCentral_perfectChernClass (n : ℕ) :
    (perfectChernClass C sZ hE n).IsBivariantCentral := by
  intro Y sY _ g _ hg q c
  have h := c.heq_bivariantCompositeOfInvertible_perfectChernClass hE n
  have e := TotalChowClass.res_apply_eq_bivariantClassCongrBase g hg
    (perfectChernClass C sZ hE) n
  rw [res_perfectChernClass_derivedPullback_of_comp_eq C sZ hE g hg (hE.derivedPullback g)] at e
  exact e ▸ h

/-- The restriction of `P_p(E)` along `h : Z' ⟶ Z` is `P_p(Lh^*E)`. -/
theorem chowCohomologyRestriction_perfectPowerSumClass {Z' : Scheme.{u}} (h : Z' ⟶ Z)
    [LocallyOfFiniteType h] (n : ℕ) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ h n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (perfectPowerSumComponent C sZ hE n) =
      perfectPowerSumComponent C (h ≫ sZ) (hE.derivedPullback h) n := by
  change _ = perfectPowerSum C (h ≫ sZ) (hE.derivedPullback h) n n
  rw [← res_perfectPowerSum_derivedPullback C sZ hE h rfl (hE.derivedPullback h),
    TotalChowClass.res_rfl_apply]
  rfl

/-- The restriction of `c_p(E)` along `h : Z' ⟶ Z` is `c_p(Lh^*E)`. -/
theorem chowCohomologyRestriction_perfectChernClass {Z' : Scheme.{u}} (h : Z' ⟶ Z)
    [LocallyOfFiniteType h] (n : ℕ) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ h n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (perfectChernClass C sZ hE n) =
      perfectChernClass C (h ≫ sZ) (hE.derivedPullback h) n := by
  rw [← res_perfectChernClass_derivedPullback_of_comp_eq C sZ hE h rfl (hE.derivedPullback h),
    TotalChowClass.res_rfl_apply]

end Central

/-! ### The extension along a closed cover of a bivariant central class -/

section Commute

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂] {p : ℤ}

/-- **The extension of a bivariant central class commutes with every class.** Let
`a ∈ A^p(X₂)` vanish over `X₁ ×_X X₂` and be bivariant central. Then its extension
`a' ∈ A^p(X₂ ⟶ X)` along the closed cover `X = X₁ ∪ X₂` (Stacks 0F9H) commutes, in the sense of
Stacks 0FA2, with every bivariant class `c ∈ A^q(Y ⟶ X)`. -/
theorem closedCoverExtension_commutesWithEveryClass
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p)
    (hcomm : a.IsBivariantCentral) (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha).CommutesWithEveryClass := by
  intro Y g _ q c
  change BivariantCommute C _ sX i₂ g p q
    (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) c
  -- the restriction of `c` to `X₂`
  set c₂ := bivariantRestriction C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl i₂ q
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c with hc₂
  -- `a` commutes with `c` on test schemes over `X₂`
  have hK : ∀ {T : Scheme.{u}} (u : T ⟶ X₂) [LocallyOfFiniteType u] (m : T ⟶ X)
      [LocallyOfFiniteType m] (hm : u ≫ i₂ = m) (k : ℤ) (α : chowGroup C (u ≫ (i₂ ≫ sX)) k),
      c.cap m (k - p) (chowGroupCongr C (show u ≫ (i₂ ≫ sX) = m ≫ sX by
          rw [← hm, Category.assoc]) (k - p)
          (a.idRule C (i₂ ≫ sX) (gysinSystemOfInvertible C) u k α)) ≍
        a.idRule C (i₂ ≫ sX) (gysinSystemOfInvertible C) (pullback.snd g m ≫ u) (k - q)
          (chowGroupCongr C (by subst hm; simp [pullback.condition_assoc]) (k - q)
            (c.cap m k (chowGroupCongr C (show u ≫ (i₂ ≫ sX) = m ≫ sX by
              rw [← hm, Category.assoc]) k α))) := by
    intro T u _ m _ hm k α
    subst hm
    have h1 := (c₂.heq_bivariantCompositeOfInvertible_iff a _).1
      (hcomm _ (pullback.snd g i₂) _ q c₂) u k α
    rw [hc₂, bivariantRestriction_cap, bivariantRestrictionCap_apply, bivariantRestriction_cap,
      bivariantRestrictionCap_apply, BivariantClass.idRule_bivariantClassCongrBase,
      chowCohomologyRestriction_idRule] at h1
    refine heq_of_chowPushforwardOfIso_heq_heq
      (sD' := (pullback.fst (pullback.snd g i₂) u ≫ pullback.snd g i₂) ≫ (i₂ ≫ sX))
      (pullbackLeftPullbackSndIso g i₂ u).inv _ (by simp [pullback.condition_assoc])
      (by simp [pullback.condition_assoc]) (by simp [pullback.condition_assoc])
      (show k - p - q = k - q - p by ring) (h1.trans ?_)
    refine (chowGroupCongr_heq C _ _ _).trans ?_
    refine BivariantClass.idRule_chowPushforwardOfIso_heq
      (sT := pullback.fst (pullback.snd g i₂) u ≫ pullback.fst g i₂ ≫ g ≫ sX)
      (sT' := pullback.fst g (u ≫ i₂) ≫ g ≫ sX) a _ (pullbackLeftPullbackSndIso g i₂ u).inv
      (pullback.snd g (u ≫ i₂) ≫ u) (by simp) ?_ (by simp) (k - q)
      (c.cap (u ≫ i₂) k (chowGroupCongr C (Category.assoc u i₂ sX).symm k α)) _ ?_ _ ?_
    · simp [pullback.condition_assoc]
    · exact (chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _)
    · exact (chowGroupCongr_heq C _ _ _).symm
  intro T t _ k α
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C sX i₁ i₂ (i₂ ≫ sX) rfl hcover t k α
  rw [closedCoverSum_apply]
  simp only [map_add]
  congr 1
  · rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply, closedCoverExtension_cap_first,
      map_zero, map_zero, map_zero, BivariantClass.cap_chowPush_eq c t (pullback.snd i₁ t) _ rfl,
      properChowPushforward_chowGroupCongr C rfl (Category.assoc _ _ _).symm _ _
        (by simp [bivariantBaseChangeMap]) _ _ (properPushforwardDescends C _ _ _ _ _),
      (isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover
        ha).capVanishesOver (pullback.fst g t ≫ g) (bivariantBaseChangeMap g t (pullback.snd i₁ t))
        (pullback.snd g (pullback.snd i₁ t ≫ t) ≫ pullback.fst i₁ t)
        (by simp [bivariantBaseChangeMap, pullback.condition]),
      map_zero]
  · have hs : (pullback.snd g (pullback.snd i₂ t ≫ t) ≫ pullback.fst i₂ t) ≫ (i₂ ≫ sX) =
        pullback.fst g (pullback.snd i₂ t ≫ t) ≫ (g ≫ sX) := by
      simp only [Category.assoc]
      rw [pullback.condition_assoc (f := g), pullback.condition_assoc (f := i₂)]
      simp only [Category.assoc]
    have hm₂i : (pullback.snd g (pullback.snd i₂ t ≫ t) ≫ pullback.fst i₂ t) ≫ i₂ =
        bivariantBaseChangeMap g t (pullback.snd i₂ t) ≫ pullback.fst g t ≫ g := by
      simp [bivariantBaseChangeMap, pullback.condition]
    rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply, closedCoverExtension_cap_second,
      BivariantClass.cap_chowPush_eq c t (pullback.snd i₂ t) _
        (sB := (pullback.snd g (pullback.snd i₂ t ≫ t) ≫ pullback.fst i₂ t) ≫ (i₂ ≫ sX))
        hs.symm,
      properChowPushforward_chowGroupCongr C rfl (Category.assoc _ _ _).symm _ _
        (by rw [← Category.assoc, ← hm₂i, Category.assoc]) _ _
        (properPushforwardDescends C _ _ _ _ _),
      (isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover
        ha).cap_chowPush_second (pullback.fst g t ≫ g)
        (bivariantBaseChangeMap g t (pullback.snd i₂ t))
        (pullback.snd g (pullback.snd i₂ t ≫ t) ≫ pullback.fst i₂ t) hm₂i]
    have hK₂ := hK (pullback.fst i₂ t) (pullback.snd i₂ t ≫ t) pullback.condition k α₂
    refine eq_of_heq ?_
    rw [chowPushforwardOfIso_chowPush]
    case huv =>
      rw [Category.assoc, commuteComparisonHom_fst_assoc, pullback.lift_snd_assoc]
      simp [bivariantBaseChangeMap, pullback.condition_assoc]
    refine (chowPush_heq C _ _ ?_ hs rfl rfl (chowGroupCongr_heq C hs _ _).symm).trans ?_
    · rw [Category.assoc, commuteComparisonHom_fst_assoc, pullback.lift_snd_assoc, ← hs]
      simp [bivariantBaseChangeMap, pullback.condition_assoc]
    refine HEq.symm (((chowGroupCongr_heq C _ _ _).symm.trans
      (heq_of_eq (chowPush_id_eq_chowGroupCongr C _ _ (Category.id_comp _) _ _).symm)).trans
      (chowPush_pullback_heq_of_test_eq C (sZ := g ≫ sX)
        (sB := pullback.fst g (pullback.fst i₂ t ≫ i₂) ≫ g ≫ sX) g pullback.condition _ _
        _ _ ?_ (k - q - p) ?_))
    · refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;>
        simp only [pullback.congrHom_hom, Category.assoc, commuteComparisonHom_fst,
          commuteComparisonHom_snd_fst, commuteComparisonHom_snd_snd, pullback.lift_fst,
          pullback.lift_snd, pullback.lift_snd_assoc,
          bivariantBaseChangeMap, pullback.map, Category.comp_id, Category.id_comp]
    refine HEq.symm (HEq.trans ?_ (hK₂.symm.trans ((BivariantClass.cap_heq_of_eq c
      pullback.condition.symm (k - p) ((chowGroupCongr_heq C _ _ _).trans
        (chowGroupCongr_heq C _ _ _).symm)).trans (chowGroupDegreeEquiv_heq C _ _ _).symm)))
    refine (chowGroupCongr_heq C _ _ _).trans ?_
    refine IdentityCapRule.heq_congr C (i₂ ≫ sX)
      (a.idRule C (i₂ ≫ sX) (gysinSystemOfInvertible C)) rfl rfl ?_
    exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
      (chowGroupCongr_heq C _ _ _).symm)

end Commute

/-! ### The classes of Stacks 0F9H -/

section BabyCase

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)
  (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {Y : Scheme.{u}} (f : Y ⟶ X)
  [LocallyOfFiniteType f]

/-- **`P'_p(E₂)` commutes with every bivariant class**, in the sense of Stacks 0FA2. -/
theorem closedCoverPowerSum_commutesWithEveryClass
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    (closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hzero).CommutesWithEveryClass :=
  closedCoverExtension_commutesWithEveryClass C sX i₁ i₂ _
    (isBivariantCentral_perfectPowerSumClass hE₂ p) hcover
    (vanishesOver_perfectPowerSumClass_of_isZero C (i₂ ≫ sX) (pullback.snd i₁ i₂) hE₂ p hzero)

/-- **`c'_p(E₂)` commutes with every bivariant class**, in the sense of Stacks 0FA2. -/
theorem closedCoverChernClass_commutesWithEveryClass
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hrank).CommutesWithEveryClass :=
  closedCoverExtension_commutesWithEveryClass C sX i₁ i₂ _
    (isBivariantCentral_perfectChernClass hE₂ p) hcover
    (vanishesOver_perfectChernClass_of_rankLT C (i₂ ≫ sX) (pullback.snd i₁ i₂) hE₂ p hrank)

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] [LocallyOfFiniteType f] in
/-- The square comparing `Y₁ ∩ Y₂` with `X₁ ∩ X₂` for the base change `Yᵢ = Xᵢ ×_X Y` of a closed
cover along `f : Y ⟶ X`. -/
theorem pullbackLift_comp_pullbackSnd_eq_pullbackSnd_comp_pullbackFst :
    pullback.lift (pullback.fst (pullback.snd i₁ f) (pullback.snd i₂ f) ≫ pullback.fst i₁ f)
        (pullback.snd (pullback.snd i₁ f) (pullback.snd i₂ f) ≫ pullback.fst i₂ f)
        (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc]) ≫
      pullback.snd i₁ i₂ =
    pullback.snd (pullback.snd i₁ f) (pullback.snd i₂ f) ≫ pullback.fst i₂ f :=
  pullback.lift_snd _ _ _

/-- **The restriction of `P'_p(E₂)` along `f : Y ⟶ X` is `P'_p(Lf₂^*E₂)`** (Stacks 0F9Z and the
generic form of Stacks 0GUG), for the base-changed cover `Y = Y₁ ∪ Y₂`, `Yᵢ = Xᵢ ×_X Y`, and
`f₂ : Y₂ ⟶ X₂` the base change of `f`. -/
theorem bivariantRestriction_closedCoverPowerSum
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    bivariantRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hzero) =
      closedCoverPowerSum C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
        (pullback.fst i₂ f ≫ (i₂ ≫ sX))
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f)
        (hE₂.derivedPullback (pullback.fst i₂ f)) p
        (range_pullbackSnd_union_eq_univ i₁ i₂ hcover f)
        (isZero_derivedPullback_of_isZero_of_comp_eq
          (pullbackLift_comp_pullbackSnd_eq_pullbackSnd_comp_pullbackFst i₁ i₂ f) hzero) := by
  rw [closedCoverPowerSum, bivariantRestriction_closedCoverExtension]
  · unfold closedCoverPowerSum
    congr 1
    exact chowCohomologyRestriction_perfectPowerSumClass hE₂ (pullback.fst i₂ f) p
  · exact vanishesOver_perfectPowerSumClass_of_isZero C _ _ hE₂ p hzero


/-- **The restriction of `c'_p(E₂)` along `f : Y ⟶ X` is `c'_p(Lf₂^*E₂)`** (Stacks 0F9Z and the
generic form of Stacks 0GUG), for the base-changed cover `Y = Y₁ ∪ Y₂`, `Yᵢ = Xᵢ ×_X Y`, and
`f₂ : Y₂ ⟶ X₂` the base change of `f`. -/
theorem bivariantRestriction_closedCoverChernClass
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    bivariantRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hrank) =
      closedCoverChernClass C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
        (pullback.fst i₂ f ≫ (i₂ ≫ sX))
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f)
        (hE₂.derivedPullback (pullback.fst i₂ f)) p
        (range_pullbackSnd_union_eq_univ i₁ i₂ hcover f)
        (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq
          (pullbackLift_comp_pullbackSnd_eq_pullbackSnd_comp_pullbackFst i₁ i₂ f) hrank) := by
  rw [closedCoverChernClass, bivariantRestriction_closedCoverExtension]
  · unfold closedCoverChernClass
    congr 1
    exact chowCohomologyRestriction_perfectChernClass hE₂ (pullback.fst i₂ f) p
  · exact vanishesOver_perfectChernClass_of_rankLT C _ _ hE₂ p hrank

end BabyCase

/-! ### Commuting classes, read on the two composites -/

section Transport

variable {C : ChowSituation.{u}} {X Z₁ Z₂ : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {f₁ : Z₁ ⟶ X} [LocallyOfFiniteType f₁] {f₂ : Z₂ ⟶ X} [LocallyOfFiniteType f₂] {p₁ p₂ : ℤ}
  {c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p₁}
  {c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl p₂}

/-- **Stacks 0FA2, on classes.** If `c₁ ∈ A^{p₁}(Z₁ ⟶ X)` and `c₂ ∈ A^{p₂}(Z₂ ⟶ X)` commute, then

  `res(c₁) ∘ c₂ = res(c₂) ∘ c₁`   in   `A^{p₁+p₂}(Z₂ ×_X Z₁ ⟶ X)`,

the first composite, a class for `Z₁ ×_X Z₂ ⟶ X`, being carried to `Z₂ ×_X Z₁` along the symmetry
of the fibre product (`Stacks.Chow.bivariantTransport`). The degrees `p₁ + p₂` and `p₂ + p₁`
differ, whence the heterogeneous equality. -/
theorem BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq
    (h : BivariantCommute C (gysinSystemOfInvertible C) sX f₁ f₂ p₁ p₂ c₁ c₂) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX))
        (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) sX (pullback.snd f₁ f₂ ≫ f₂)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl)
        (pullback.snd f₂ f₁ ≫ f₁)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl)
        (pullbackSymmetry f₁ f₂) (by simp [pullback.condition]) (p₁ + p₂)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
          (pullback.snd f₁ f₂) f₂
          (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl p₁ p₂
          (bivariantRestriction C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl f₂ p₁
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₁) c₂) ≍
      bivariantCompositeOfInvertible C (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) (f₁ ≫ sX) sX
        (pullback.snd f₂ f₁) f₁
        (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl p₂ p₁
        (bivariantRestriction C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl f₁ p₂
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₂) c₁ := by
  rw [bivariantCommute_iff_cap_eq_of_isBivariantClassComposition C _ sX f₁ f₂ p₁ p₂ c₁ c₂
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (properPushforwardDescends C) _ _
    (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)
    (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)] at h
  refine BivariantClass.heq_of_congrHom_cap_heq rfl (add_comm p₁ p₂) _ _ fun t _ k α ↦ ?_
  refine (chowPushforwardOfIso_congrHom_heq rfl t _ _ _).trans ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply]
  refine HEq.trans ?_ ((heq_of_eq (h t k α)).trans (chowGroupDegreeEquiv_heq C _ _ _))
  rw [chowPushforwardOfIso_congr_apply C _ _ _ (compositeComparisonHom f₁ f₂ t)
    (pullback.hom_ext (by simp [transportPullbackIso, compositeComparisonHom])
      (by simp [transportPullbackIso, compositeComparisonHom]))
    _ (compositeComparisonHom_comp_structureMorphism C sX f₁ f₂ t)]
  exact chowPushforwardOfIso_heq _ _ _ rfl rfl (by ring) (chowGroupDegreeEquiv_heq C _ _ _).symm

/-- **Stacks 0FA2, on nonhomogeneous classes.** If every homogeneous component of
`x ∈ A^*(Z₁ ⟶ X)` commutes with every homogeneous component of `y ∈ A^*(Z₂ ⟶ X)`, then

  `res(x) ∘ y = res(y) ∘ x`   in   `A^*(Z₂ ×_X Z₁ ⟶ X)`,

the first composite, a class for `Z₁ ×_X Z₂ ⟶ X`, being carried to `Z₂ ×_X Z₁` along the symmetry
of the fibre product. This is
`Stacks.Chow.BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq` on each pair
of homogeneous components, the degrees `p₁ + p₂` and `p₂ + p₁` being the same summand of the
direct sum. -/
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute
    (x : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl)
    (y : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl)
    (h : ∀ i j : ℤ,
      BivariantCommute C (gysinSystemOfInvertible C) sX f₁ f₂ i j (x i) (y j)) :
    nonhomogeneousBivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) sX
        (pullback.snd f₁ f₂ ≫ f₂)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl)
        (pullback.snd f₂ f₁ ≫ f₁)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl)
        (pullbackSymmetry f₁ f₂) (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX))
          (f₂ ≫ sX) sX (pullback.snd f₁ f₂) f₂
          (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl
          (nonhomogeneousBivariantRestriction C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl
            f₂ (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) x) y) =
      nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX))
        (f₁ ≫ sX) sX (pullback.snd f₂ f₁) f₁
        (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl
        (nonhomogeneousBivariantRestriction C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl f₁
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) y) x := by
  classical
  rw [← DirectSum.sum_support_of x, ← DirectSum.sum_support_of y]
  simp only [map_sum, AddMonoidHom.finsetSum_apply, nonhomogeneousBivariantRestriction_of,
    nonhomogeneousBivariantCompositeOfInvertible_of_of, nonhomogeneousBivariantTransport_of]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  exact DirectSum.of_eq_of_heq (add_comm j i)
    (BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq (h j i))

/-- A class `c₂` commuting with every bivariant class commutes with every homogeneous component of
the homogeneous class `c₂ ∈ A^*(Z₂ ⟶ X)`, against every homogeneous component of every
`x ∈ A^*(Z₁ ⟶ X)`: the components of `c₂` other than the one of degree `p₂` are zero. -/
theorem BivariantClass.CommutesWithEveryClass.bivariantCommute_apply_of
    (hc₂ : c₂.CommutesWithEveryClass)
    (x : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl)
    (i j : ℤ) :
    BivariantCommute C (gysinSystemOfInvertible C) sX f₁ f₂ i j (x i)
      (DirectSum.of (fun n ↦ BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl n)
        p₂ c₂ j) := by
  by_cases hj : j = p₂
  · subst hj
    rw [DirectSum.of_eq_same]
    exact BivariantCommute.symm _ _ _ _ _ _ _ _ _
      ((BivariantClass.commutesWithEveryClass_iff c₂).1 hc₂ f₁ i (x i))
  · rw [DirectSum.of_eq_of_ne _ _ _ hj]
    exact BivariantCommute.symm _ _ _ _ _ _ _ _ _
      (bivariantCommute_zero_left C _ sX f₂ f₁ j i (x i))

end Transport

/-! ### Stacks 0FAJ -/

section BabyCaseComposite

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)
  (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {Y : Scheme.{u}} (f : Y ⟶ X)
  [LocallyOfFiniteType f] (q : ℤ)
  (c : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl q)

/-- **Stacks 0FAJ for `P'_p`.** Let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions covering
`X`, let `E₂ ∈ D(𝒪_{X₂})` have defined Chern classes and restrict to zero on `X₁ ∩ X₂`, let
`f : Y ⟶ X` be locally of finite type and let `c ∈ A^q(Y ⟶ X)`. Then

  `c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c`   in   `A^{p+q}(Y₂ ⟶ X)`,

where `Y₂ = X₂ ×_X Y`, `f₂ : Y₂ ⟶ X₂` is the base change of `f`, `P'_p(Lf₂^*E₂) ∈ A^p(Y₂ ⟶ Y)` is
the class of Stacks 0F9H for the base-changed cover of `Y`, and `c ∘ P'_p(E₂)` is the composite of
the restriction of `c` to `X₂` with `P'_p(E₂)`, carried from `Y ×_X X₂` to `Y₂`. -/
theorem bivariantTransport_bivariantCompositeOfInvertible_closedCoverPowerSum
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst f i₂ ≫ (f ≫ sX))
        (pullback.fst i₂ f ≫ (i₂ ≫ sX)) sX (pullback.snd f i₂ ≫ i₂)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl)
        (pullback.snd i₂ f ≫ f)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl)
        (pullbackSymmetry f i₂) (by simp [pullback.condition]) (q + p)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C (pullback.fst f i₂ ≫ (f ≫ sX)) (i₂ ≫ sX) sX
          (pullback.snd f i₂) i₂
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl q p
          (bivariantRestriction C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl i₂ q
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
          (closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hzero)) ≍
      bivariantCompositeOfInvertible C (pullback.fst i₂ f ≫ (i₂ ≫ sX)) (f ≫ sX) sX
        (pullback.snd i₂ f) f
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl p q
        (closedCoverPowerSum C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
          (pullback.fst i₂ f ≫ (i₂ ≫ sX))
          (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f)
          (hE₂.derivedPullback (pullback.fst i₂ f)) p
          (range_pullbackSnd_union_eq_univ i₁ i₂ hcover f)
          (isZero_derivedPullback_of_isZero_of_comp_eq
            (pullbackLift_comp_pullbackSnd_eq_pullbackSnd_comp_pullbackFst i₁ i₂ f) hzero)) c := by
  have h : BivariantCommute C (gysinSystemOfInvertible C) sX i₂ f p q
      (closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hzero) c :=
    (BivariantClass.commutesWithEveryClass_iff _).1
      (closedCoverPowerSum_commutesWithEveryClass C sX i₁ i₂ hE₂ p hcover hzero) f q c
  have h' := BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq h.symm
  rw [bivariantRestriction_closedCoverPowerSum] at h'
  exact h'

/-- **Stacks 0FAJ for `c'_p`.** Let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions covering
`X`, let `E₂ ∈ D(𝒪_{X₂})` have defined Chern classes and restrict on `X₁ ∩ X₂` to a finite
locally free module of rank `< p` in degree `0`, let `f : Y ⟶ X` be locally of finite type and
let `c ∈ A^q(Y ⟶ X)`. Then

  `c ∘ c'_p(E₂) = c'_p(Lf₂^*E₂) ∘ c`   in   `A^{p+q}(Y₂ ⟶ X)`,

where `Y₂ = X₂ ×_X Y`, `f₂ : Y₂ ⟶ X₂` is the base change of `f`, `c'_p(Lf₂^*E₂) ∈ A^p(Y₂ ⟶ Y)` is
the class of Stacks 0F9H for the base-changed cover of `Y`, and `c ∘ c'_p(E₂)` is the composite of
the restriction of `c` to `X₂` with `c'_p(E₂)`, carried from `Y ×_X X₂` to `Y₂`. -/
theorem bivariantTransport_bivariantCompositeOfInvertible_closedCoverChernClass
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst f i₂ ≫ (f ≫ sX))
        (pullback.fst i₂ f ≫ (i₂ ≫ sX)) sX (pullback.snd f i₂ ≫ i₂)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl)
        (pullback.snd i₂ f ≫ f)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl)
        (pullbackSymmetry f i₂) (by simp [pullback.condition]) (q + p)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C (pullback.fst f i₂ ≫ (f ≫ sX)) (i₂ ≫ sX) sX
          (pullback.snd f i₂) i₂
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl q p
          (bivariantRestriction C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl i₂ q
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
          (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hrank)) ≍
      bivariantCompositeOfInvertible C (pullback.fst i₂ f ≫ (i₂ ≫ sX)) (f ≫ sX) sX
        (pullback.snd i₂ f) f
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl p q
        (closedCoverChernClass C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
          (pullback.fst i₂ f ≫ (i₂ ≫ sX))
          (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f)
          (hE₂.derivedPullback (pullback.fst i₂ f)) p
          (range_pullbackSnd_union_eq_univ i₁ i₂ hcover f)
          (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq
            (pullbackLift_comp_pullbackSnd_eq_pullbackSnd_comp_pullbackFst i₁ i₂ f) hrank)) c := by
  have h : BivariantCommute C (gysinSystemOfInvertible C) sX i₂ f p q
      (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hrank) c :=
    (BivariantClass.commutesWithEveryClass_iff _).1
      (closedCoverChernClass_commutesWithEveryClass C sX i₁ i₂ hE₂ p hcover hrank) f q c
  have h' := BivariantCommute.bivariantTransport_bivariantCompositeOfInvertible_heq h.symm
  rw [bivariantRestriction_closedCoverChernClass] at h'
  exact h'

/-- Let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions covering `X`, let `E₂ ∈ D(𝒪_{X₂})` have
defined Chern classes and restrict to zero on `X₁ ∩ X₂`, let `f : Y ⟶ X` be locally of finite type
and let `c ∈ A^*(Y ⟶ X)`. Then

  `c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c`   in   `A^*(Y₂ ⟶ X)`,

where `Y₂ = X₂ ×_X Y`, `f₂ : Y₂ ⟶ X₂` is the base change of `f`, `P'_p(Lf₂^*E₂) ∈ A^p(Y₂ ⟶ Y)` is
the class of Stacks 0F9H for the base-changed cover of `Y`, and `c ∘ P'_p(E₂)` is the composite of
the restriction of `c` to `X₂` with `P'_p(E₂)`, carried from `Y ×_X X₂` to `Y₂`. -/
@[stacks 0FAJ "for P'_p: c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c in A^*(Y₂ → X), for every c in \
A^*(Y → X)"]
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_closedCoverPowerSum
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂))
    (c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl) :
    nonhomogeneousBivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst f i₂ ≫ (f ≫ sX)) (pullback.fst i₂ f ≫ (i₂ ≫ sX)) sX
        (pullback.snd f i₂ ≫ i₂)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl)
        (pullback.snd i₂ f ≫ f)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl)
        (pullbackSymmetry f i₂) (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst f i₂ ≫ (f ≫ sX)) (i₂ ≫ sX)
          sX (pullback.snd f i₂) i₂
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl
          (nonhomogeneousBivariantRestriction C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl i₂
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
          (DirectSum.of _ (p : ℤ)
            (closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hzero))) =
      nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst i₂ f ≫ (i₂ ≫ sX)) (f ≫ sX) sX
        (pullback.snd i₂ f) f
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl
        (DirectSum.of _ (p : ℤ)
          (closedCoverPowerSum C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
            (pullback.fst i₂ f ≫ (i₂ ≫ sX))
            (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f)
            (hE₂.derivedPullback (pullback.fst i₂ f)) p
            (range_pullbackSnd_union_eq_univ i₁ i₂ hcover f)
            (isZero_derivedPullback_of_isZero_of_comp_eq
              (pullbackLift_comp_pullbackSnd_eq_pullbackSnd_comp_pullbackFst i₁ i₂ f) hzero)))
        c := by
  have h := nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute c
    (DirectSum.of _ (p : ℤ) (closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hzero))
    ((closedCoverPowerSum_commutesWithEveryClass C sX i₁ i₂ hE₂ p hcover
      hzero).bivariantCommute_apply_of c)
  rw [nonhomogeneousBivariantRestriction_of, bivariantRestriction_closedCoverPowerSum] at h
  exact h

/-- Let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions covering `X`, let `E₂ ∈ D(𝒪_{X₂})` have
defined Chern classes and restrict on `X₁ ∩ X₂` to a finite locally free module of rank `< p` in
degree `0`, let `f : Y ⟶ X` be locally of finite type and let `c ∈ A^*(Y ⟶ X)`. Then

  `c ∘ c'_p(E₂) = c'_p(Lf₂^*E₂) ∘ c`   in   `A^*(Y₂ ⟶ X)`,

where `Y₂ = X₂ ×_X Y`, `f₂ : Y₂ ⟶ X₂` is the base change of `f`, `c'_p(Lf₂^*E₂) ∈ A^p(Y₂ ⟶ Y)` is
the class of Stacks 0F9H for the base-changed cover of `Y`, and `c ∘ c'_p(E₂)` is the composite of
the restriction of `c` to `X₂` with `c'_p(E₂)`, carried from `Y ×_X X₂` to `Y₂`. -/
@[stacks 0FAJ "for c'_p: c ∘ c'_p(E₂) = c'_p(Lf₂^*E₂) ∘ c in A^*(Y₂ → X), for every c in \
A^*(Y → X)"]
theorem nonhomogeneousBivariantTransport_compositeOfInvertible_closedCoverChernClass
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (c : nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl) :
    nonhomogeneousBivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst f i₂ ≫ (f ≫ sX)) (pullback.fst i₂ f ≫ (i₂ ≫ sX)) sX
        (pullback.snd f i₂ ≫ i₂)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl)
        (pullback.snd i₂ f ≫ f)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl)
        (pullbackSymmetry f i₂) (by simp [pullback.condition])
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst f i₂ ≫ (f ≫ sX)) (i₂ ≫ sX)
          sX (pullback.snd f i₂) i₂
          (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl
          (nonhomogeneousBivariantRestriction C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl i₂
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
          (DirectSum.of _ (p : ℤ)
            (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hrank))) =
      nonhomogeneousBivariantCompositeOfInvertible C (pullback.fst i₂ f ≫ (i₂ ≫ sX)) (f ≫ sX) sX
        (pullback.snd i₂ f) f
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl
        (DirectSum.of _ (p : ℤ)
          (closedCoverChernClass C (f ≫ sX) (pullback.snd i₁ f) (pullback.snd i₂ f)
            (pullback.fst i₂ f ≫ (i₂ ≫ sX))
            (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f)
            (hE₂.derivedPullback (pullback.fst i₂ f)) p
            (range_pullbackSnd_union_eq_univ i₁ i₂ hcover f)
            (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq
              (pullbackLift_comp_pullbackSnd_eq_pullbackSnd_comp_pullbackFst i₁ i₂ f) hrank)))
        c := by
  have h := nonhomogeneousBivariantTransport_compositeOfInvertible_eq_of_bivariantCommute c
    (DirectSum.of _ (p : ℤ) (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl hE₂ p hcover hrank))
    ((closedCoverChernClass_commutesWithEveryClass C sX i₁ i₂ hE₂ p hcover
      hrank).bivariantCommute_apply_of c)
  rw [nonhomogeneousBivariantRestriction_of, bivariantRestriction_closedCoverChernClass] at h
  exact h

end BabyCaseComposite

end Stacks.Chow

end
