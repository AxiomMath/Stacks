module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentGysin
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible

/-!
# Descent of bivariant Chow classes along an envelope

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`, let `g : Y' ⟶ Y` be an envelope
(Stacks 0GU5) and write `X' = X ×_Y Y'`. **Stacks 0GUC**: for `c' ∈ A^p(X' ⟶ Y')` whose two
restrictions `res₁(c') = res₂(c')` in `A^p(X' ×_X X' ⟶ Y' ×_Y Y')` agree, there is a unique
`c ∈ A^p(X ⟶ Y)` with `res(c) = c'`.

## Main definitions

* `Stacks.Chow.envelopeDescentClass` — the descended class, whose cap operation is
  `Stacks.Chow.envelopeDescentCap`.

## Main results

* `Stacks.Chow.isBivariantRestriction_envelopeDescentClass` — the descended class restricts to
  `c'`.
* `Stacks.Chow.existsUnique_bivariantRestriction_eq_of_naturality` — the tag for a Gysin system
  natural under base change isomorphisms, under proper pushforward and under the comparison of
  iterated pullbacks.
* `Stacks.Chow.existsUnique_bivariantRestriction_eq_of_isEnvelope` — **Stacks 0GUC**, for the
  Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class of an invertible
  module.

## Implementation notes

Bivariant classes are stated against a `Stacks.Chow.GysinSystem`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`.
The tag is registered for the Gysin system of
the first Chern class of an invertible module, for which the three naturality properties the
construction uses are theorems: `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward` (Stacks 02TA) and
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`. The first is also
what the restrictions of Stacks 0F9Z in the statement are built from.

The two restrictions `res₁(c')` and `res₂(c')` are `Stacks.Chow.envelopeDescentRes₁` and
`Stacks.Chow.envelopeDescentRes₂`, the restrictions of `c'` along the two projections
`Y' ×_Y Y' ⟶ Y'`, read on `X' ×_X X'` through the identifications of the fibre products of
`X' ⟶ Y'` along the projections with `X' ×_X X'`, as in the proof of the tag.

## References

* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Proper pushforward along the identity between two equal structure morphisms is the transport
between their Chow groups. -/
theorem chowPush_id_eq_chowGroupCongr (C : ChowSituation.{u}) {A : Scheme.{u}}
    (sA sB : A ⟶ C.S) [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] (h : 𝟙 A ≫ sB = sA)
    (k : ℤ) (α : chowGroup C sA k) :
    chowPush C sA sB (𝟙 A) h k α =
      chowGroupCongr C (by rw [← h, Category.id_comp]) k α := by
  have hs : sB = sA := by rw [← h, Category.id_comp]
  subst hs
  exact chowPush_id C sB k α

/-- A proper pushforward followed by a pushforward along an isomorphism is the proper pushforward
along the composite. -/
theorem chowPushforwardOfIso_chowPush (C : ChowSituation.{u}) {A B D : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (u : A ⟶ B) [IsProper u] (v : B ⟶ D) [IsIso v]
    (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (huv : (u ≫ v) ≫ sD = sA) (k : ℤ)
    (α : chowGroup C sA k) :
    chowPushforwardOfIso C sB sD v hv k (chowPush C sA sB u hu k α) =
      chowPush C sA sD (u ≫ v) huv k α :=
  chowPush_comp C sA sB sD u v (u ≫ v) rfl hu hv huv k α

section Existence

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (g : Y' ⟶ Y) [IsProper g] (p : ℤ)
  (c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hres : envelopeDescentRes₁ C G sX sY f hf g p hgys c' =
    envelopeDescentRes₂ C G sX sY f hf g p hgys c')
  (hgE : IsEnvelope g)

/-- **The descended class of Stacks 0GUC.** The bivariant class `c ∈ A^p(X ⟶ Y)` whose cap
operation on a test scheme `T ⟶ Y` is `c ∩ β = h_*(c' ∩ β')` for any lift `β'` of `β` along the
envelope `Y' ×_Y T ⟶ T`. -/
def envelopeDescentClass (hprop : G.IsNaturalUnderProperPushforward)
    (hcomp : G.IsNaturalUnderPullbackCompPushforward) : BivariantClass C G sX sY f hf p where
  cap t _ k := envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE t k
  cap_properPushforward := by
    intro T₀ T₀' g₀ _ w₀ _ w₀' sq₀ hfst₀ k₀ α₀
    exact (envelopeDescentCap_proper_naturality C G sX sY f hf g p c' hgys hres hgE)
      g₀ w₀ w₀' sq₀ hfst₀ k₀ _ _ α₀
  cap_flatPullbackChow := by
    intro T₀ T₀' g₀ _ w₀ _ _ r₀ hr₀ w₀' sq₀ hfst₀ k₀ α₀
    exact (envelopeDescentCap_flat_naturality C G sX sY f hf g p c' hgys hres hgE)
      g₀ w₀ r₀ hr₀ w₀' sq₀ hfst₀ k₀ _ _ _ α₀
  cap_gysin := by
    intro T₀ g₀ _ L₀ _ s₀ k₀ _ _ _ _ ε₀ hε₀ hbase₀ α₀
    exact (envelopeDescentCap_gysin_naturality C G sX sY f hf g p c' hgys hres hgE hprop hcomp)
      g₀ L₀ s₀ k₀ ε₀ hε₀ hbase₀ _ α₀

/-- The descended class restricts to `c'` along the envelope. -/
theorem isBivariantRestriction_envelopeDescentClass (hprop : G.IsNaturalUnderProperPushforward)
    (hcomp : G.IsNaturalUnderPullbackCompPushforward) :
    IsBivariantRestriction C G sX sY f hf g p
      (envelopeDescentClass C G sX sY f hf g p c' hgys hres hgE hprop hcomp) c' := by
  intro V v _ k α
  have hm : v ≫ g = 𝟙 V ≫ (v ≫ g) := (Category.id_comp _).symm
  have hα : chowGroupCongr C (Category.assoc v g sY).symm k α =
      envelopeLiftPush C sY g (v ≫ g) (𝟙 V) v hm k α := by
    rw [chowPush_id_eq_chowGroupCongr]
  change _ = chowPushforwardOfIso C _ _ _ _ (k - p)
    (envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE (v ≫ g) k
      (chowGroupCongr C (Category.assoc v g sY).symm k α))
  rw [hα, envelopeDescentCap_envelopeLiftPush, envelopeDescentPush_apply]
  have hH : envelopeDescentMap f g (v ≫ g) (𝟙 V) v hm ≫ (pullbackLeftPullbackSndIso f g v).inv =
      𝟙 _ := by
    rw [Iso.comp_inv_eq, Category.id_comp]
    refine pullback.hom_ext ?_ ?_ <;> simp
  rw [chowPushforwardOfIso_chowPush C _ _ _ _ _ _ _ (by rw [hH, Category.id_comp]) (k - p),
    chowPush_congr C _ _ hH _ (Category.id_comp _) (k - p), chowPush_id]

include hres hgE in
/-- **Stacks 0GUC for a Gysin system natural under base change isomorphisms, under proper
pushforward and under the comparison of iterated pullbacks.** -/
theorem existsUnique_bivariantRestriction_eq_of_naturality
    (hprop : G.IsNaturalUnderProperPushforward)
    (hcomp : G.IsNaturalUnderPullbackCompPushforward) :
    ∃! c : BivariantClass C G sX sY f hf p,
      bivariantRestriction C G sX sY f hf g p hgys c = c' := by
  refine ⟨envelopeDescentClass C G sX sY f hf g p c' hgys hres hgE hprop hcomp,
    eq_of_isBivariantRestriction C G sX sY f hf g p
      (isBivariantRestriction_bivariantRestriction C G sX sY f hf g p hgys _)
      (isBivariantRestriction_envelopeDescentClass C G sX sY f hf g p c' hgys hres hgE hprop
        hcomp), ?_⟩
  intro d hd
  refine eq_of_isBivariantRestriction_of_isEnvelope' C G sX sY f hf g p hgE
    (c' := c') ?_
    (isBivariantRestriction_envelopeDescentClass C G sX sY f hf g p c' hgys hres hgE hprop hcomp)
  rw [← hd]
  exact isBivariantRestriction_bivariantRestriction C G sX sY f hf g p hgys d

end Existence

/-- **Stacks 0GUC.** Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over the base
of chapter 42, let `g : Y' ⟶ Y` be an envelope and write `X' = X ×_Y Y'`. Let
`c' ∈ A^p(X' ⟶ Y')`. If the two restrictions `res₁(c') = res₂(c')` in
`A^p(X' ×_X X' ⟶ Y' ×_Y Y')` agree, then there is a unique `c ∈ A^p(X ⟶ Y)` whose restriction
`res(c)` along `g` is `c'`.

Bivariant classes are taken against the Gysin system of the first Chern class of an invertible
module. -/
@[stacks 0GUC]
theorem existsUnique_bivariantRestriction_eq_of_isEnvelope (C : ChowSituation.{u})
    {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (comm : f ≫ sY = sX)
    (g : Y' ⟶ Y) (envelope : IsEnvelope g) (p : ℤ) :
    letI : IsProper g := envelope.isProper
    ∀ c' : BivariantClass C (gysinSystemOfInvertible C) (pullback.fst f g ≫ sX) (g ≫ sY)
        (pullback.snd f g) (pullbackSnd_comp_structureMorphism_eq C sX sY f comm g) p,
      envelopeDescentRes₁ C (gysinSystemOfInvertible C) sX sY f comm g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c' =
        envelopeDescentRes₂ C (gysinSystemOfInvertible C) sX sY f comm g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c' →
      ∃! c : BivariantClass C (gysinSystemOfInvertible C) sX sY f comm p,
        bivariantRestriction C (gysinSystemOfInvertible C) sX sY f comm g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = c' := by
  let : IsProper g := envelope.isProper
  intro c' hres
  exact existsUnique_bivariantRestriction_eq_of_naturality C (gysinSystemOfInvertible C) sX sY f
    comm g p c' (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) hres envelope
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

end Stacks.Chow

end
