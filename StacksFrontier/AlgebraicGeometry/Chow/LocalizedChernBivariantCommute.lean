module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChernShrink
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CompositeCommuting
public import StacksCore.Tactic.StacksAttribute

/-!
# A localized class commutes with every bivariant class

Stacks 0FAJ. For a set-theoretic cover `X = X₁ ∪ X₂` by two closed subschemes, a class
`κ ∈ A^p(X₂)` and the localized class `cloc ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H, and a bivariant class
`c ∈ A^r(Y ⟶ X)` for `f : Y ⟶ X` locally of finite type: `cloc` commutes with `c` as soon as `κ`
does.

## Main results

* `Stacks.Chow.bivariantCommute_of_isClosedCoverLocalizedClass` — Stacks 0FAJ: the localized
  class `cloc` commutes with `c` as soon as `κ` does.
* `Stacks.Chow.bivariantCommute_of_integralFundamentalChowClass` — **Stacks 02UC for the
  commuting relation of Stacks 0FA2**, the criterion that reduces that relation to the
  fundamental class of an integral test scheme.
* `Stacks.Chow.localizedClass_bivariantIteratedCap_eq_of_range_fst` and
  `Stacks.Chow.localizedClass_bivariantIteratedCap_eq_of_range_snd` — the two cases of the
  dichotomy that an integral test scheme is filled by the base change of one member of the cover.

## Implementation notes

The commuting relation is `Stacks.Chow.BivariantCommute` of Stacks 0FA2, the identity
`c ∘ P'_p(E₂) = P'_p(Lf₂^*E₂) ∘ c` in the form of
`Stacks.Chow.bivariantCommute_iff_commuteCompositeCap_eq`. The localized class is any class with
the characterizing property `Stacks.Chow.IsClosedCoverLocalizedClass` of Stacks 0F9H, and Stacks
0FAC is the hypothesis `Stacks.Chow.ChowCohomologyCommutesWith`.

## References

* [Stacks Project, Tag 0FAJ](https://stacks.math.columbia.edu/tag/0FAJ)
* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of a bivariant class along an equality of degrees -/

section CongrDeg

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- A bivariant class of degree `p`, read as one of degree `q` along an equality `p = q` of
degrees. -/
def bivariantClassCongrDeg {p q : ℤ} (hpq : p = q) (c : BivariantClass C G sX sY f hf p) :
    BivariantClass C G sX sY f hf q :=
  hpq ▸ c

/-- The class read in the other degree caps as the original does, up to the transport of Chow
groups along the equality of degrees. -/
theorem bivariantClassCongrDeg_cap {p q : ℤ} (hpq : p = q)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (bivariantClassCongrDeg C G sX sY f hf hpq c).cap g k α =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) (by rw [hpq]) (c.cap g k α) := by
  subst hpq
  exact (chowGroupDegreeEquiv_self C (pullback.fst f g ≫ sX) _ _).symm

end CongrDeg

/-! ### The comparison of the two composites as a transport -/

section Comparison

variable {X Z₁ Z₂ : Scheme.{u}} (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X)

/-- The symmetry of the fibre product is an isomorphism over `X` of the two morphisms
`Z₁ ×_X Z₂ ⟶ X` through which the two composites of Stacks 0FA2 are indexed. -/
theorem pullbackSymmetry_hom_comp_compositeMorphism :
    (pullbackSymmetry f₁ f₂).hom ≫ (pullback.snd f₂ f₁ ≫ f₁) = pullback.snd f₁ f₂ ≫ f₂ := by
  rw [← Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.condition]

/-- The comparison isomorphism of the two composites of Stacks 0FA2 at a test scheme is the
isomorphism of base changes induced by the symmetry of the fibre product. -/
theorem transportPullbackIso_hom_eq_compositeComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    (transportPullbackIso (pullback.snd f₁ f₂ ≫ f₂) (pullback.snd f₂ f₁ ≫ f₁)
        (pullbackSymmetry f₁ f₂) (pullbackSymmetry_hom_comp_compositeMorphism f₁ f₂) t).hom =
      compositeComparisonHom f₁ f₂ t := by
  refine pullback.hom_ext ?_ ?_
  · rw [transportPullbackIso_hom_fst, compositeComparisonHom_fst]
  · rw [transportPullbackIso_hom_snd, compositeComparisonHom_snd]

end Comparison

/-! ### Reducing the commuting relation to integral test schemes -/

section Reduction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] (p₁ p₂ : ℤ)
  (c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁)
  (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)
  (hgys : G.IsNaturalUnderBaseChangeIso) (hpp : ProperPushforwardDescends C)

/-- **Stacks 02UC for the commuting relation of Stacks 0FA2.** Two bivariant classes commute as
soon as the two iterated cap operations agree on the fundamental class of every *integral* test
scheme. The two composites `res(c₁) ∘ c₂` and `res(c₂) ∘ c₁` are given as classes `d₁`, `d₂`
satisfying `Stacks.Chow.IsBivariantClassComposition`. -/
theorem bivariantCommute_of_integralFundamentalChowClass
    (d₁ : BivariantClass C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) sX (pullback.snd f₁ f₂ ≫ f₂)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl) (p₁ + p₂))
    (d₂ : BivariantClass C G (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) sX (pullback.snd f₂ f₁ ≫ f₁)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl) (p₂ + p₁))
    (h₁ : IsBivariantClassComposition C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
      (pullback.snd f₁ f₂) f₂
      (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl hpp p₁ p₂
      (bivariantRestriction C G (f₁ ≫ sX) sX f₁ rfl f₂ p₁ hgys c₁) c₂ d₁)
    (h₂ : IsBivariantClassComposition C G (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) (f₁ ≫ sX) sX
      (pullback.snd f₂ f₁) f₁
      (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl hpp p₂ p₁
      (bivariantRestriction C G (f₂ ≫ sX) sX f₂ rfl f₁ p₂ hgys c₂) c₁ d₂)
    (key : ∀ {T : Scheme.{u}} (t : T ⟶ X) (_ : LocallyOfFiniteType t) (_ : IsIntegral T) (k : ℤ),
      chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
          (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) (commuteComparisonHom f₁ f₂ t)
          (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
          (bivariantIteratedCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ t k
            (fundamentalChowClass C (t ≫ sX) k)) =
        chowGroupDegreeEquiv C (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
          (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)
          (bivariantIteratedCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ t k
            (fundamentalChowClass C (t ≫ sX) k))) :
    BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂ := by
  rw [bivariantCommute_iff_cap_eq_of_isBivariantClassComposition C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys
    hpp d₁ d₂ h₁ h₂]
  rw [isBivariantClassComposition_iff] at h₁ h₂
  have hc₁ : ∀ {T : Scheme.{u}} (t : T ⟶ X) (_ : LocallyOfFiniteType t) (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      chowGroupDegreeEquiv C
          (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
          (by ring : k - (p₁ + p₂) = (k - p₂) - p₁) (d₁.cap t k α) =
        commuteCompositeCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys hpp t k α :=
    fun t _ k α ↦ h₁ t k α
  have hc₂ : ∀ {T : Scheme.{u}} (t : T ⟶ X) (_ : LocallyOfFiniteType t) (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      chowGroupDegreeEquiv C
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (by ring : k - (p₂ + p₁) = (k - p₁) - p₂) (d₂.cap t k α) =
        commuteCompositeCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ hgys hpp t k α :=
    fun t _ k α ↦ h₂ t k α
  set e₁ := bivariantTransport C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX))
    (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) sX (pullback.snd f₁ f₂ ≫ f₂)
    (comp_comp_structureMorphism_eq
      (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl)
    (pullback.snd f₂ f₁ ≫ f₁)
    (comp_comp_structureMorphism_eq
      (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl)
    (pullbackSymmetry f₁ f₂) (pullbackSymmetry_hom_comp_compositeMorphism f₁ f₂) (p₂ + p₁) hgys
    (bivariantClassCongrDeg C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) sX (pullback.snd f₁ f₂ ≫ f₂)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl)
      (add_comm p₁ p₂) d₁) with he₁
  have hcape₁ : ∀ {T : Scheme.{u}} (t : T ⟶ X) (_ : LocallyOfFiniteType t) (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      chowGroupDegreeEquiv C
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (by ring : k - (p₂ + p₁) = (k - p₂) - p₁) (e₁.cap t k α) =
        chowPushforwardOfIso C
          (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (compositeComparisonHom f₁ f₂ t)
          (compositeComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
          (chowGroupDegreeEquiv C
            (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
            (by ring : k - (p₁ + p₂) = (k - p₂) - p₁) (d₁.cap t k α)) := by
    intro T t _ k α
    rw [he₁, bivariantTransport_cap, bivariantTransportCap_apply, bivariantClassCongrDeg_cap,
      chowGroupDegreeEquiv_chowPushforwardOfIso, chowGroupDegreeEquiv_chowGroupDegreeEquiv]
    exact chowPushforwardOfIso_congr_apply C _ _ _ _
      (transportPullbackIso_hom_eq_compositeComparisonHom f₁ f₂ t) _ _ ((k - p₂) - p₁) _
  have hzero : d₂ - e₁ = 0 := by
    rw [BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero]
    intro T t _ _ k
    rw [BivariantClass.sub_cap, sub_eq_zero]
    refine (chowGroupDegreeEquiv C
      (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
      (by ring : k - (p₂ + p₁) = (k - p₂) - p₁)).injective ?_
    rw [hcape₁ t inferInstance k _]
    have hcc := (commuteCompositeCap_eq_iff_bivariantIteratedCap_eq C G sX f₁ f₂ p₁ p₂ c₁ c₂
      hgys hpp t inferInstance k (fundamentalChowClass C (t ≫ sX) k)).2
      (key t inferInstance inferInstance k)
    rw [← hc₁ t inferInstance k _, ← hc₂ t inferInstance k _,
      chowGroupDegreeEquiv_chowGroupDegreeEquiv] at hcc
    exact hcc.symm
  have hd₂ : d₂ = e₁ := sub_eq_zero.mp hzero
  intro T t _ k α
  rw [hd₂, hcape₁ t inferInstance k α]

end Reduction

/-! ### Pushing forward along a morphism and back along a retraction -/

/-- Pushing a Chow class forward along a morphism over the base and then along a retraction of
that morphism is the transport along the equality of structure morphisms the retraction forces. -/
theorem chowPushforwardOfIso_properChowPushforward_of_comp_eq_id (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sA' : A ⟶ C.S)
    [LocallyOfFiniteType sA'] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsProper u]
    (w : B ⟶ A) [IsIso w] (huw : u ≫ w = 𝟙 A) (hu : u ≫ sB = sA) (hw : w ≫ sA' = sB) (k : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (x : chowGroup C sA k) :
    chowPushforwardOfIso C sB sA' w hw k (properChowPushforward C sA sB u hu k hfacu x) =
      chowGroupCongr C
        (show sA = sA' by rw [← hu, ← hw, ← Category.assoc, huw, Category.id_comp]) k x := by
  have : IsProper w := inferInstance
  have hAA' : sA = sA' := by rw [← hu, ← hw, ← Category.assoc, huw, Category.id_comp]
  have hid : 𝟙 A ≫ sA' = sA := by rw [Category.id_comp, hAA']
  rw [show chowPushforwardOfIso C sB sA' w hw k =
        properChowPushforward C sB sA' w hw k
          (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sB sA' w hw k) from rfl,
    ← properChowPushforward_comp_apply C sA sB sA' u w (𝟙 A) huw hu hw hid k hfacu
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sB sA' w hw k)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sA' (𝟙 A) hid k) x]
  subst hAA'
  exact congrFun (congrArg DFunLike.coe (properChowPushforward_id C sA k
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sA (𝟙 A) hid k))) x

/-! ### A filling member of a cover stays filling on a test scheme factoring through it -/

/-- If the base change of a closed subscheme `i : Z ⟶ X` along `t : T ⟶ X` is surjective, then so
is its base change along any `g : T' ⟶ X` that factors through `t`: the range of the base change
is the inverse image of the range of `i`. -/
theorem range_pullbackSnd_eq_univ_of_factorsThrough {X Z T T' : Scheme.{u}} (i : Z ⟶ X)
    (t : T ⟶ X) (q : T' ⟶ T) {g : T' ⟶ X} (hg : g = q ≫ t)
    (h : Set.range (pullback.snd i t).base = Set.univ) :
    Set.range (pullback.snd i g).base = Set.univ := by
  subst hg
  rw [Scheme.Pullback.range_snd] at h ⊢
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hx : q.base x ∈ (⇑t ⁻¹' Set.range (⇑i)) := by rw [h]; trivial
  simpa using hx

/-! ### Stacks 0FAJ: the two cover cases -/

section Cases

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X₁ X₂ Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X)
  [IsClosedImmersion i₂] (f : Y ⟶ X) [LocallyOfFiniteType f] (p r : ℤ)
  (κ : chowCohomologyComponent C G (i₂ ≫ sX) p)
  (cloc : BivariantClass C G (i₂ ≫ sX) sX i₂ rfl p)
  (c : BivariantClass C G (f ≫ sX) sX f rfl r)

/-- **The first member of the cover fills the integral test scheme.** If the base change of `i₁`
along an integral test scheme `t : T ⟶ X` is surjective, the two iterated cap operations of
`cloc` and `c` agree on the fundamental class of `T`. -/
theorem localizedClass_bivariantIteratedCap_eq_of_range_fst {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] [IsIntegral T]
    (hloc : IsClosedCoverLocalizedClass C G sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl p κ cloc)
    (h₁ : Set.range (pullback.snd i₁ t).base = Set.univ) (k : ℤ) :
    chowPushforwardOfIso C (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX))
        (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX)) (commuteComparisonHom i₂ f t)
        (commuteComparisonHom_comp_structureMorphism C sX i₂ f t) ((k - r) - p)
        (bivariantIteratedCap C G sX i₂ f p r cloc c t k
          (fundamentalChowClass C (t ≫ sX) k)) =
      chowGroupDegreeEquiv C (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
        (by ring : (k - p) - r = (k - r) - p)
        (bivariantIteratedCap C G sX f i₂ r p c cloc t k
          (fundamentalChowClass C (t ≫ sX) k)) := by
  have hrange : Set.range (pullback.snd i₁ (pullback.fst f t ≫ f)).base = Set.univ :=
    range_pullbackSnd_eq_univ_of_factorsThrough i₁ t (pullback.snd f t) pullback.condition h₁
  have hzero : ∀ {T' : Scheme.{u}} (g : T' ⟶ X) [LocallyOfFiniteType g],
      Set.range (pullback.snd i₁ g).base = Set.univ → ∀ (k : ℤ) x, cloc.cap g k x = 0 :=
    fun g _ hg k x ↦ by
      obtain ⟨α₁, rfl⟩ := surjective_closedCoverPushforward C sX (i₁ ≫ sX) i₁ rfl g hg k x
      exact hloc.1 g k α₁
  have hleft := hzero (pullback.fst f t ≫ f) hrange (k - r)
  have hright := hzero t h₁ k
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply, hleft _, hright _, map_zero, map_zero,
    map_zero, map_zero]

/-! ### The two bracketings of the triple fibre product -/

omit [IsClosedImmersion i₂] [LocallyOfFiniteType f] in
/-- **The comparison isomorphism of the two bracketings of `X₂ ×_X Y ×_X T`, read on the
projection to `Y ×_X T`.** Going from `Y ×_X (T ×_X X₂)` to `X₂ ×_X (Y ×_X T)` and then down to
`Y ×_X T` is the base change along `Y ⟶ X` of the projection `T ×_X X₂ ⟶ T`, presented with the
test morphism `pullback.fst i₂ t ≫ i₂` rather than the composite `pullback.snd i₂ t ≫ t`. -/
theorem commuteComparisonHom_comp_pullbackSnd {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] :
    commuteComparisonHom f i₂ t ≫ pullback.snd i₂ (pullback.fst f t ≫ f) =
      baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂)
        pullback.condition.symm := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, commuteComparisonHom_snd_fst, baseChangeMapOfEq_fst]
  · rw [Category.assoc, commuteComparisonHom_snd_snd, baseChangeMapOfEq_snd]

omit [LocallyOfFiniteType sX] [IsClosedImmersion i₂] [LocallyOfFiniteType f] in
/-- The structure morphism over the base of `Y ×_X W`, for a test scheme `v : W ⟶ X₂`, read
through its projection to `W` and the structure morphism of `X₂`. -/
theorem pullbackFst_comp_structureMorphism_eq_snd_comp {W : Scheme.{u}} (v : W ⟶ X₂) :
    pullback.fst f (v ≫ i₂) ≫ (f ≫ sX) = (pullback.snd f (v ≫ i₂) ≫ v) ≫ (i₂ ≫ sX) := by
  rw [← Category.assoc, pullback.condition]
  simp

/-! ### Stacks 0FAC, as an input -/

/-- **Stacks 0FAC, as a property of the parameters.** The assertion that the class
`κ ∈ A^p(X₂)` commutes with `c ∈ A^r(Y ⟶ X)`: on every test scheme `v : W ⟶ X₂` locally of finite
type and every `γ ∈ CH_k(W)`,

  `c ∩ (κ ∩ γ) = κ ∩ (c ∩ γ)`   in   `CH_{k - r - p}(Y ×_X W)`,

the left side reading `κ` on `W` and `c` at the test morphism `v ≫ i₂`, and the right side
reading `c` at `v ≫ i₂` and then `κ` on `Y ×_X W` through its projection to `W`.

Stacks 0FAC is `c ∘ c_p(E) = c_p(Lg^*E) ∘ c` for a perfect object `E` on `X₂`; with `κ` the Chern
class of `E` and `g : Y ×_X X₂ ⟶ X₂` the base change of `f`, the restriction of `κ` along `g` is
`c_p(Lg^*E)`, and the displayed identity at the test schemes is the tag. -/
def ChowCohomologyCommutesWith : Prop :=
  ∀ {W : Scheme.{u}} (v : W ⟶ X₂) (_ : LocallyOfFiniteType v) (k : ℤ)
      (γ : chowGroup C (v ≫ (i₂ ≫ sX)) k),
    chowGroupDegreeEquiv C (pullback.fst f (v ≫ i₂) ≫ (f ≫ sX))
        (by ring : (k - p) - r = (k - r) - p)
        (c.cap (v ≫ i₂) (k - p)
          (chowGroupCongr C (Category.assoc v i₂ sX).symm (k - p)
            (BivariantClass.toIdentityCapRule C G (i₂ ≫ sX) p κ v k γ))) =
      chowGroupCongr C
          (pullbackFst_comp_structureMorphism_eq_snd_comp C sX i₂ f v).symm ((k - r) - p)
          (BivariantClass.toIdentityCapRule C G (i₂ ≫ sX) p κ
            (pullback.snd f (v ≫ i₂) ≫ v) (k - r)
            (chowGroupCongr C (pullbackFst_comp_structureMorphism_eq_snd_comp C sX i₂ f v) (k - r)
              (c.cap (v ≫ i₂) k (chowGroupCongr C (Category.assoc v i₂ sX).symm k γ))))

/-! ### The second cover case -/

/-- **`c ∩ [T]` is pushed forward from `X₂ ×_X (Y ×_X T)`** when the base change of the second
member of the cover fills the integral test scheme `t : T ⟶ X`: it is the pushforward along the
base change of `i₂` to `Y ×_X T` of the class `c ∩ [X₂ ×_X T]`, carried along the bracketing
isomorphism `Y ×_X (X₂ ×_X T) ≅ X₂ ×_X (Y ×_X T)`. -/
theorem chowGroupCongr_cap_fundamentalChowClass_eq_closedCoverPushforward {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] [IsIntegral T]
    (h₂ : Set.range (pullback.snd i₂ t).base = Set.univ) (k : ℤ) :
    chowGroupCongr C (Category.assoc (pullback.fst f t) f sX).symm (k - r)
        (c.cap t k (fundamentalChowClass C (t ≫ sX) k)) =
      closedCoverPushforward C sX (i₂ ≫ sX) i₂ rfl (pullback.fst f t ≫ f) (k - r)
        (chowPushforwardOfIso C (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
          (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) (commuteComparisonHom f i₂ t)
          (commuteComparisonHom_comp_structureMorphism C sX f i₂ t) (k - r)
          (c.cap (pullback.fst i₂ t ≫ i₂) k
            (chowGroupCongr C (Category.assoc (pullback.fst i₂ t) i₂ sX).symm k
              (fundamentalChowClass C (pullback.fst i₂ t ≫ (i₂ ≫ sX)) k)))) := by
  have hm : pullback.snd i₂ t ≫ t = pullback.fst i₂ t ≫ i₂ := pullback.condition.symm
  have hmb : pullback.snd i₂ t ≫ (t ≫ sX) = (pullback.fst i₂ t ≫ i₂) ≫ sX := by
    rw [← Category.assoc, ← pullback.condition]
  have hsrc : pullback.fst i₂ t ≫ (i₂ ≫ sX) = (pullback.fst i₂ t ≫ i₂) ≫ sX :=
    (Category.assoc (pullback.fst i₂ t) i₂ sX).symm
  have : IsClosedImmersion
      (baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm) :=
    MorphismProperty.of_isPullback
      (isPullback_baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm)
      (P := @IsClosedImmersion) inferInstance
  have hfund := (closedCoverPushforward_fundamentalChowClass C sX (i₂ ≫ sX) i₂ rfl t h₂ k).symm
  have hcong : closedCoverPushforward C sX (i₂ ≫ sX) i₂ rfl t k
        (fundamentalChowClass C (pullback.fst i₂ t ≫ (i₂ ≫ sX)) k) =
      properChowPushforward C ((pullback.fst i₂ t ≫ i₂) ≫ sX) (t ≫ sX) (pullback.snd i₂ t) hmb k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (pullback.snd i₂ t) C ((pullback.fst i₂ t ≫ i₂) ≫ sX) (t ≫ sX) hmb k)
        (chowGroupCongr C hsrc k
          (fundamentalChowClass C (pullback.fst i₂ t ≫ (i₂ ≫ sX)) k)) :=
    (properChowPushforward_congr_source C hsrc (t ≫ sX) (pullback.snd i₂ t)
      (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl t) hmb k
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
        (pullback.snd i₂ t) C (pullback.fst i₂ t ≫ (i₂ ≫ sX)) (t ≫ sX)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl t) k)
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
        (pullback.snd i₂ t) C ((pullback.fst i₂ t ≫ i₂) ≫ sX) (t ≫ sX) hmb k)
      (fundamentalChowClass C (pullback.fst i₂ t ≫ (i₂ ≫ sX)) k)).symm
  have hnat := BivariantClass.proper_naturality_of_test_eq c t (pullback.snd i₂ t)
    (pullback.fst i₂ t ≫ i₂) hm
    (baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm)
    (isPullback_baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm)
    (baseChangeMapOfEq_fst f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm) k hmb
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      (pullback.snd i₂ t) C ((pullback.fst i₂ t ≫ i₂) ≫ sX) (t ≫ sX) hmb k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      (baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm) C
      (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
      (pullback.fst f t ≫ (f ≫ sX)) (by
        rw [← Category.assoc,
          baseChangeMapOfEq_fst f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm]) (k - r))
    (chowGroupCongr C hsrc k (fundamentalChowClass C (pullback.fst i₂ t ≫ (i₂ ≫ sX)) k))
  rw [hfund, hcong, hnat,
    properChowPushforward_chowGroupCongr C rfl (Category.assoc (pullback.fst f t) f sX).symm
      (baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm) _
      (by
        rw [Category.assoc, ← Category.assoc,
          baseChangeMapOfEq_fst f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm]) (k - r) _
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
        (baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm) C
        (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX)) ((pullback.fst f t ≫ f) ≫ sX)
        (by
          rw [Category.assoc, ← Category.assoc,
            baseChangeMapOfEq_fst f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm]) (k - r))
      _,
    properChowPushforward_comp_apply C
      (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
      (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) ((pullback.fst f t ≫ f) ≫ sX)
      (commuteComparisonHom f i₂ t) (pullback.snd i₂ (pullback.fst f t ≫ f))
      (baseChangeMapOfEq f t (pullback.snd i₂ t) (pullback.fst i₂ t ≫ i₂) hm)
      (commuteComparisonHom_comp_pullbackSnd i₂ f t)
      (commuteComparisonHom_comp_structureMorphism C sX f i₂ t)
      (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl (pullback.fst f t ≫ f)) _
      (k - r)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
        (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
        (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) (commuteComparisonHom f i₂ t)
        (commuteComparisonHom_comp_structureMorphism C sX f i₂ t) (k - r))
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
        (pullback.snd i₂ (pullback.fst f t ≫ f)) C
        (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) ((pullback.fst f t ≫ f) ≫ sX)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl (pullback.fst f t ≫ f))
        (k - r)) _ _]
  rfl

/-- **The second member of the cover fills the integral test scheme.** If the base change of `i₂`
along an integral test scheme `t : T ⟶ X` is surjective and `κ` commutes with `c`, the two
iterated cap operations of `cloc` and `c` agree on the fundamental class of `T`. -/
theorem localizedClass_bivariantIteratedCap_eq_of_range_snd {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] [IsIntegral T]
    (hloc : IsClosedCoverLocalizedClass C G sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl p κ cloc)
    (hcomm : ChowCohomologyCommutesWith C G sX i₂ f p r κ c)
    (h₂ : Set.range (pullback.snd i₂ t).base = Set.univ) (k : ℤ) :
    chowPushforwardOfIso C (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX))
        (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX)) (commuteComparisonHom i₂ f t)
        (commuteComparisonHom_comp_structureMorphism C sX i₂ f t) ((k - r) - p)
        (bivariantIteratedCap C G sX i₂ f p r cloc c t k
          (fundamentalChowClass C (t ≫ sX) k)) =
      chowGroupDegreeEquiv C (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
        (by ring : (k - p) - r = (k - r) - p)
        (bivariantIteratedCap C G sX f i₂ r p c cloc t k
          (fundamentalChowClass C (t ≫ sX) k)) := by
  have hbr : commuteComparisonHom f i₂ t ≫ pullback.fst i₂ (pullback.fst f t ≫ f) =
      pullback.snd f (pullback.fst i₂ t ≫ i₂) ≫ pullback.fst i₂ t :=
    commuteComparisonHom_fst f i₂ t
  have hsA : pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX) =
      (commuteComparisonHom f i₂ t ≫ pullback.fst i₂ (pullback.fst f t ≫ f)) ≫ (i₂ ≫ sX) :=
    (commuteComparisonHom_comp_structureMorphism C sX f i₂ t).symm.trans
      (Category.assoc _ _ _).symm
  have hs : (commuteComparisonHom f i₂ t ≫ pullback.fst i₂ (pullback.fst f t ≫ f)) ≫
        (i₂ ≫ sX) =
      (pullback.snd f (pullback.fst i₂ t ≫ i₂) ≫ pullback.fst i₂ t) ≫ (i₂ ≫ sX) :=
    hsA.symm.trans (pullbackFst_comp_structureMorphism_eq_snd_comp C sX i₂ f (pullback.fst i₂ t))
  have hstep1 : ∀ y : chowGroup C (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX)) (k - r),
      chowPushforwardOfIso C (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
          (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) (commuteComparisonHom f i₂ t)
          (commuteComparisonHom_comp_structureMorphism C sX f i₂ t) (k - r) y =
        properChowPushforward C
          ((commuteComparisonHom f i₂ t ≫ pullback.fst i₂ (pullback.fst f t ≫ f)) ≫ (i₂ ≫ sX))
          (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) (commuteComparisonHom f i₂ t)
          (Category.assoc _ _ _).symm (k - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
            ((commuteComparisonHom f i₂ t ≫ pullback.fst i₂ (pullback.fst f t ≫ f)) ≫ (i₂ ≫ sX))
            (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) (commuteComparisonHom f i₂ t)
            (Category.assoc _ _ _).symm (k - r))
          (chowGroupCongr C hsA (k - r) y) := fun y ↦
    (properChowPushforward_congr_source C hsA
      (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) (commuteComparisonHom f i₂ t)
      (commuteComparisonHom_comp_structureMorphism C sX f i₂ t) (Category.assoc _ _ _).symm (k - r)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
        (commuteComparisonHom f i₂ t)
        (commuteComparisonHom_comp_structureMorphism C sX f i₂ t) (k - r))
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
        (commuteComparisonHom f i₂ t) (Category.assoc _ _ _).symm (k - r)) y).symm
  have hstep2 := BivariantClass.toIdentityCapRule_properNaturality C G (i₂ ≫ sX) p κ
    (pullback.fst i₂ (pullback.fst f t ≫ f)) (commuteComparisonHom f i₂ t) (k - r)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
      (commuteComparisonHom f i₂ t) (Category.assoc _ _ _).symm (k - r))
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _
      (commuteComparisonHom f i₂ t) (Category.assoc _ _ _).symm ((k - r) - p))
  simp only [bivariantIteratedCap_apply]
  rw [chowGroupCongr_cap_fundamentalChowClass_eq_closedCoverPushforward C G sX i₂ f r c t h₂ k,
    hloc.2 (pullback.fst f t ≫ f) (k - r),
    (closedCoverPushforward_fundamentalChowClass C sX (i₂ ≫ sX) i₂ rfl t h₂ k).symm,
    hloc.2 t k, hcomm (pullback.fst i₂ t) inferInstance k, hstep1, hstep2,
    chowPushforwardOfIso_properChowPushforward_of_comp_eq_id C
      ((commuteComparisonHom f i₂ t ≫ pullback.fst i₂ (pullback.fst f t ≫ f)) ≫ (i₂ ≫ sX))
      (pullback.fst f (pullback.fst i₂ t ≫ i₂) ≫ (f ≫ sX))
      (pullback.fst i₂ (pullback.fst f t ≫ f) ≫ (i₂ ≫ sX)) (commuteComparisonHom f i₂ t)
      (commuteComparisonHom i₂ f t) (commuteComparisonHom_comp_commuteComparisonHom f i₂ t)
      (Category.assoc _ _ _).symm (commuteComparisonHom_comp_structureMorphism C sX i₂ f t)
      ((k - r) - p) _,
    ← chowGroupCongr_chowGroupCongr C hsA hs (k - r),
    toIdentityCapRule_congr_test C G (i₂ ≫ sX) p κ hbr hs (k - r),
    chowGroupCongr_chowGroupCongr C hs
      (pullbackFst_comp_structureMorphism_eq_snd_comp C sX i₂ f (pullback.fst i₂ t)).symm
      ((k - r) - p)]

/-! ### The proof of Stacks 0FAJ -/

/-- **Stacks 0FAJ.** Let `X = X₁ ∪ X₂` set theoretically for closed immersions `i_j : X_j ⟶ X`,
let `κ ∈ A^p(X₂)` and let `cloc ∈ A^p(X₂ ⟶ X)` be a localized class of `κ` along that cover in the
sense of Stacks 0F9H. Let `f : Y ⟶ X` be locally of finite type and `c ∈ A^r(Y ⟶ X)`. If `κ`
commutes with `c` (Stacks 0FAC, the hypothesis `hcomm`), then `cloc` commutes with `c`. -/
theorem bivariantCommute_of_isClosedCoverLocalizedClass
    (hgys : G.IsNaturalUnderBaseChangeIso) (hpp : ProperPushforwardDescends C)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hloc : IsClosedCoverLocalizedClass C G sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl p κ cloc)
    (hcomm : ChowCohomologyCommutesWith C G sX i₂ f p r κ c)
    (d₁ : BivariantClass C G (pullback.fst i₂ f ≫ (i₂ ≫ sX)) sX (pullback.snd i₂ f ≫ f)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl) (p + r))
    (d₂ : BivariantClass C G (pullback.fst f i₂ ≫ (f ≫ sX)) sX (pullback.snd f i₂ ≫ i₂)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl) (r + p))
    (h₁ : IsBivariantClassComposition C G (pullback.fst i₂ f ≫ (i₂ ≫ sX)) (f ≫ sX) sX
      (pullback.snd i₂ f) f
      (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl f) rfl hpp p r
      (bivariantRestriction C G (i₂ ≫ sX) sX i₂ rfl f p hgys cloc) c d₁)
    (h₂ : IsBivariantClassComposition C G (pullback.fst f i₂ ≫ (f ≫ sX)) (i₂ ≫ sX) sX
      (pullback.snd f i₂) i₂
      (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl i₂) rfl hpp r p
      (bivariantRestriction C G (f ≫ sX) sX f rfl i₂ r hgys c) cloc d₂) :
    BivariantCommute C G sX i₂ f p r cloc c := by
  refine bivariantCommute_of_integralFundamentalChowClass C G sX i₂ f p r cloc c hgys hpp d₁ d₂
    h₁ h₂ ?_
  intro T t _ _ k
  rcases range_pullbackSnd_eq_univ_or i₁ i₂ t hcover with h | h
  · exact localizedClass_bivariantIteratedCap_eq_of_range_fst C G sX i₁ i₂ f p r κ cloc c t hloc
      h k
  · exact localizedClass_bivariantIteratedCap_eq_of_range_snd C G sX i₁ i₂ f p r κ cloc c t hloc
      hcomm h k

end Cases

end Stacks.Chow

end
