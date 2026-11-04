module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange

/-!
# Flat pullback commutes with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `f₁ : Z₁ ⟶ X` be flat of relative dimension `r` and let
`f₂ : Z₂ ⟶ X` be locally of finite type. By **Stacks 0B78** flat pullback along the base changes
of `f₁` is a bivariant class `f₁^* ∈ A^{-r}(Z₁ ⟶ X)`. This file proves that `f₁^*` commutes, in
the sense of **Stacks 0FA2**, with an arbitrary bivariant class `c ∈ A^{p}(Z₂ ⟶ X)`:

  `f₁^* ∩ c ∩ α = c ∩ f₁^* ∩ α`   in   `CH_{k + r - p}(Z₁ ×_X Z₂)`,

for every `α ∈ CH_k(T)` and every test scheme `T ⟶ X` locally of finite type.

The mathematical content is the flat-pullback law of **Stacks 0B76 (2)** for `c`, read at the
base change of `f₁` along the test scheme: that law *is* the assertion that capping with `c`
commutes with flat pullback, and `f₁^*` caps by flat pullback. This is what the source of
**Stacks 0FF6** calls "immediate from the definition of a bivariant class".

## Main results

* `Stacks.Chow.bivariantCommute_flatPullbackBivariantClass` — the smooth half of **Stacks 0FF6**:
  the flat-pullback bivariant class of Stacks 0B78 commutes with every bivariant class.

## Implementation notes

### Which half of Stacks 0FF6 this is

Stacks 0FF6 concerns a local complete intersection morphism `f : X ⟶ Y` whose Gysin map `f^!`
exists, and asserts that `res(f^!)` commutes with an arbitrary bivariant class. The source proves
it by factoring `f = i ≫ g` with `g` smooth and `i` a regular immersion, so that `f^!` is the
composite of `g^*` and `i^!`, and treating the two factors separately:

* the `g^*` factor — flat, indeed smooth, pullback — is "immediate from the definition of a
  bivariant class";
* the `i^!` factor is **Stacks 0FBP** (Lemma 42.54.8 of the source).

This file delivers the first factor, in the generality in which this repository has it: not just
for a smooth `g` but for any flat `f₁` of a fixed relative dimension, which is exactly the
hypothesis under which Stacks 0B78 produces a bivariant class. The second factor is **not**
delivered and cannot be: Stacks 0FBP has no carrier in this repository, nor do the tags that
would be needed to construct `f^!` at all (0FBK, 0FBL, 0FBM, 0FBN, 0B79, 02UA). Consequently the
full statement of Stacks 0FF6 — which quantifies over the Gysin map of a local complete
intersection morphism — is not stated here, and the tag attribute below says so.

Parameterizing `f^!` as an arbitrary bivariant class would not rescue the full statement either.
`Stacks.Chow.BivariantClass` has four fields, and every one of them constrains a single class
against proper pushforward, flat pullback or the Gysin map of a divisor; none relates two
classes. So "an arbitrary bivariant class commutes with `c`" is not a theorem, and the only
hypothesis strong enough to prove it is the conclusion of Stacks 0FF6 itself. That is why the
subject here is the *concrete* class of Stacks 0B78: it is a class whose flat-pullback behaviour
is known, so the flat-pullback law of its partner `c` can actually be applied to it.

### How the two sides are compared

The two iterated cap operations land on the two fibre products `Z₁ ×_X (Z₂ ×_X T)` and
`Z₂ ×_X (Z₁ ×_X T)`, and `Stacks.Chow.BivariantCommute` compares them by pushing the first
forward along `Stacks.Chow.commuteComparisonHom`. The flat-pullback law of `c`, applied to the
base change `Z₁ ×_X T ⟶ T` of `f₁` along the test scheme `t : T ⟶ X`, instead produces a class on
a third scheme, `Z₂ ×_X (Z₁ ×_X T)` formed over the test morphism `Z₁ ×_X T ⟶ X` written as
`pullback.snd f₁ t ≫ t` rather than as `pullback.fst f₁ t ≫ f₁`. The two test morphisms are equal
by `pullback.condition` but are not the same term, so the two fibre products are not the same
object; `CategoryTheory.Limits.pullback.congrHom` is the comparison isomorphism, and
`Stacks.Chow.chowPushforwardOfIso_congrHom_cap` is what identifies the cap operations across it.

Moving the flat pullback of `c ∩ α` across the resulting isomorphism uses the isomorphism case of
Stacks 02RG, `Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`, with one leg the identity; that
case is a theorem of this repository, so no form of Stacks 02RG beyond the one already carried by
Stacks 0B78 is needed.

### Degrees

A class of degree `p` sends degree `k` to `k - p`, while flat pullback of relative dimension `r`
sends it to `k + r`; with `p = -r` these are the same integer and not the same term. As in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass` the proof therefore runs through
heterogeneous equality, and the congruence lemmas
`Stacks.Chow.BivariantClass.cap_heq_congr`, `Stacks.Chow.chowPushforwardOfIso_heq_congr` and
`Stacks.Chow.flatPullbackChow_heq_congr_base` move the transports out of the way.

### Hypotheses

Beyond the data of Stacks 0FA2 the statement carries exactly the hypotheses of Stacks 0B78, which
are what it takes to have the subject class at all: `hS1` (Stacks 02S1), `hRG` (Stacks 02RG) and
`h71` (Stacks 0B71, with the identification of Stacks 0B6Y). None of them mentions
`Stacks.Chow.BivariantCommute`, and none asserts that two bivariant classes commute.

## References

* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Congruence lemmas up to heterogeneous equality -/

/-- The cap operation of a bivariant class depends on its degree and its argument only up to
equality and heterogeneous equality. -/
theorem BivariantClass.cap_heq_congr {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    {k k' : ℤ} (hkk' : k = k') (α : chowGroup C (g ≫ sY) k) (α' : chowGroup C (g ≫ sY) k')
    (hαα' : α ≍ α') :
    c.cap g k α ≍ c.cap g k' α' := by
  subst hkk'
  obtain rfl := eq_of_heq hαα'
  rfl

/-- Pushforward along an isomorphism over the base depends on its degree and its argument only up
to equality and heterogeneous equality. -/
theorem chowPushforwardOfIso_heq_congr (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsIso u]
    (hu : u ≫ sB = sA) {k k' : ℤ} (hkk' : k = k') (α : chowGroup C sA k)
    (α' : chowGroup C sA k') (hαα' : α ≍ α') :
    chowPushforwardOfIso C sA sB u hu k α ≍ chowPushforwardOfIso C sA sB u hu k' α' := by
  subst hkk'
  obtain rfl := eq_of_heq hαα'
  rfl

/-- Flat pullback on Chow groups depends on the two structure morphisms over the base, the
morphism, the relative dimension, the degree and the argument only up to equality and
heterogeneous equality. This strengthens `Stacks.Chow.flatPullbackChow_heq_congr` by letting the
two structure morphisms vary: the comparison below meets the same flat pullback written once over
`(v ≫ w) ≫ s` and once over `v ≫ (w ≫ s)`. -/
theorem flatPullbackChow_heq_congr_base (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    {v v' : A ⟶ B} [LocallyOfFiniteType v] [Flat v] [LocallyOfFiniteType v'] [Flat v']
    (hsA : sA = sA') (hsB : sB = sB') (hvv' : v = v') (hv : v ≫ sB = sA) (hv' : v' ≫ sB' = sA')
    {n n' : ℕ} (hnn' : n = n') (hvn : AlgebraicGeometry.RelativeDimension v n)
    (hv'n' : AlgebraicGeometry.RelativeDimension v' n') {k k' : ℤ} (hkk' : k = k')
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv n hvn k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA' sB' v' hv' n' hv'n' k')
    (α : chowGroup C sB k) (α' : chowGroup C sB' k') (hαα' : α ≍ α') :
    flatPullbackChow C sA sB v hv n hvn k hfac α ≍
      flatPullbackChow C sA' sB' v' hv' n' hv'n' k' hfac' α' := by
  subst hsA
  subst hsB
  subst hvv'
  subst hnn'
  subst hkk'
  obtain rfl := eq_of_heq hαα'
  rfl

/-! ### The smooth half of Stacks 0FF6 -/

section Smooth

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] [Flat f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] (r : ℕ) (hfr : AlgebraicGeometry.RelativeDimension f₁ r)
  (hS1 : FlatPullbackDescends C) (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (h71 : G.FlatPullbackNaturality r) (p₂ : ℤ)
  (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)

/-- **The smooth half of Stacks 0FF6.** The flat-pullback bivariant class of Stacks 0B78 for a
flat morphism `f₁ : Z₁ ⟶ X` of relative dimension `r` commutes, in the sense of Stacks 0FA2, with
every bivariant class `c₂ ∈ A^{p₂}(Z₂ ⟶ X)`.

This is the `g^*` half of the factorization `f = i ≫ g` by which the source proves Stacks 0FF6,
and the source's reason is the one used here: it is immediate from the flat-pullback law of
Stacks 0B76 (2) for `c₂`. The `i^!` half is Stacks 0FBP, which has no carrier in this repository;
see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting`. -/
@[stacks 0FF6 "the smooth half only: the flat-pullback bivariant class of Stacks 0B78 commutes \
with an arbitrary bivariant class. The `i^!` half of the factorization `f = i ≫ g` is excluded; \
it is Stacks 0FBP, which has no carrier here, as has every tag needed to build `f^!`"]
theorem bivariantCommute_flatPullbackBivariantClass :
    BivariantCommute C G sX f₁ f₂ (-(r : ℤ)) p₂
      (flatPullbackBivariantClass C G (f₁ ≫ sX) sX f₁ rfl r hfr hS1 hRG h71) c₂ := by
  intro T t _ k α
  -- the test morphism `Z₁ ×_X T ⟶ X` in the two shapes the two sides present it in
  have e : pullback.snd f₁ t ≫ t = pullback.fst f₁ t ≫ f₁ :=
    (pullback.condition (f := f₁) (g := t)).symm
  -- the base change of `f₁` along the test scheme, and the base change of that along `c₂`
  have hrQ : AlgebraicGeometry.RelativeDimension (pullback.snd f₁ t) r :=
    relativeDimension_pullbackSnd f₁ hfr t
  have sqh' : IsPullback (pullback.snd f₂ (pullback.snd f₁ t ≫ t))
      (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) (pullback.snd f₁ t)
      (pullback.snd f₂ t) :=
    isPullback_bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)
  have : LocallyOfFiniteType (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) :=
    MorphismProperty.of_isPullback sqh' (P := @LocallyOfFiniteType) inferInstance
  have : Flat (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) :=
    MorphismProperty.of_isPullback sqh' (P := @Flat) inferInstance
  have hr' : AlgebraicGeometry.RelativeDimension
      (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sqh' hrQ
  have hfsth' : bivariantBaseChangeMap f₂ t (pullback.snd f₁ t) ≫ pullback.fst f₂ t =
      pullback.fst f₂ (pullback.snd f₁ t ≫ t) := by
    simp [bivariantBaseChangeMap]
  -- the two projections of the inverse of the comparison of the two test morphisms
  have hinv_fst : (pullback.congrHom (rfl : f₂ = f₂) e).inv ≫
      pullback.fst f₂ (pullback.snd f₁ t ≫ t) = pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) := by
    simp
  have hinv_snd : (pullback.congrHom (rfl : f₂ = f₂) e).inv ≫
      pullback.snd f₂ (pullback.snd f₁ t ≫ t) = pullback.snd f₂ (pullback.fst f₁ t ≫ f₁) := by
    simp
  have hsnd : bivariantBaseChangeMap f₂ t (pullback.snd f₁ t) ≫ pullback.snd f₂ t =
      pullback.snd f₂ (pullback.snd f₁ t ≫ t) ≫ pullback.snd f₁ t := by
    simp [bivariantBaseChangeMap]
  -- the comparison isomorphism of the goal, factored through the third fibre product
  have hcomp : (commuteComparisonHom f₁ f₂ t ≫ (pullback.congrHom (rfl : f₂ = f₂) e).inv) ≫
      (pullback.congrHom (rfl : f₂ = f₂) e).hom = commuteComparisonHom f₁ f₂ t := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hu₁ : (commuteComparisonHom f₁ f₂ t ≫ (pullback.congrHom (rfl : f₂ = f₂) e).inv) ≫
      (pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX)) =
      pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX) := by
    rw [Category.assoc, ← Category.assoc ((pullback.congrHom (rfl : f₂ = f₂) e).inv), hinv_fst]
    exact commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t
  have hsq : pullback.snd f₁ (pullback.fst f₂ t ≫ f₂) ≫ 𝟙 (pullback f₂ t) =
      (commuteComparisonHom f₁ f₂ t ≫ (pullback.congrHom (rfl : f₂ = f₂) e).inv) ≫
        bivariantBaseChangeMap f₂ t (pullback.snd f₁ t) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, Category.id_comp, hfsth', hinv_fst]
      exact (commuteComparisonHom_fst f₁ f₂ t).symm
    · simp only [Category.assoc, Category.id_comp, hsnd]
      rw [← Category.assoc (pullback.congrHom (rfl : f₂ = f₂) e).inv, hinv_snd]
      exact (commuteComparisonHom_snd_snd f₁ f₂ t).symm
  -- the structure morphisms the three flat pullbacks are taken over
  have hv : bivariantBaseChangeMap f₂ t (pullback.snd f₁ t) ≫
      ((pullback.fst f₂ t ≫ f₂) ≫ sX) =
      pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX) := by
    simp only [← Category.assoc]
    rw [hfsth']
  have hd : pullback.snd f₁ (pullback.fst f₂ t ≫ f₂) ≫ ((pullback.fst f₂ t ≫ f₂) ≫ sX) =
      pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX) :=
    pullbackSnd_comp_structureMorphism (rfl : f₁ ≫ sX = f₁ ≫ sX) (pullback.fst f₂ t ≫ f₂)
  have hdr : AlgebraicGeometry.RelativeDimension
      (pullback.snd f₁ (pullback.fst f₂ t ≫ f₂)) r :=
    relativeDimension_pullbackSnd f₁ hfr (pullback.fst f₂ t ≫ f₂)
  have hQ : pullback.fst f₁ t ≫ (f₁ ≫ sX) = (pullback.snd f₁ t ≫ t) ≫ sX := by
    rw [← Category.assoc, pullback.condition]
  have hvP : bivariantBaseChangeMap f₂ t (pullback.snd f₁ t) ≫
      (pullback.fst f₂ t ≫ (f₂ ≫ sX)) =
      pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX) := by
    rw [← Category.assoc, hfsth']
  have hpsQ : pullback.snd f₁ t ≫ (t ≫ sX) = (pullback.snd f₁ t ≫ t) ≫ sX :=
    (Category.assoc _ _ _).symm
  -- the comparison isomorphism of the two test morphisms, over the base
  have hcongrbase : (pullback.congrHom (rfl : f₂ = f₂) e).hom ≫
      (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) =
      pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX) := by
    simp
  -- the instances of Stacks 02S1 that the three flat pullbacks are read against
  have hfacN := hS1 _ _ _ hpsQ r hrQ k
  have hfacL := hS1 _ _ _ (pullbackSnd_comp_structureMorphism (rfl : f₁ ≫ sX = f₁ ≫ sX) t) r hrQ k
  have hfacP := hS1 _ _ _ hvP r hr' (k - p₂)
  have hfacv := hS1 _ _ _ hv r hr' (k - p₂)
  have hfacd := hS1 _ _ _ hd r hdr (k - p₂)
  -- degrees
  have hk₁ : k - -(r : ℤ) = k + (r : ℤ) := by ring
  have hdeg : (k - p₂) - -(r : ℤ) = (k - p₂) + (r : ℤ) := by ring
  have hdeg₂ : k - -(r : ℤ) - p₂ = k + (r : ℤ) - p₂ := by ring
  have hdeg₃ : k + (r : ℤ) - p₂ = (k - p₂) + (r : ℤ) := by ring
  -- the right-hand side, with the test morphism rewritten through the comparison isomorphism
  have hIV := chowPushforwardOfIso_congrHom_cap C G (f₂ ≫ sX) sX f₂ rfl p₂ c₂ e
    hcongrbase (k - -(r : ℤ))
    ((flatPullbackBivariantClass C G (f₁ ≫ sX) sX f₁ rfl r hfr hS1 hRG h71).cap t k α)
    hQ (Category.assoc (pullback.fst f₁ t) f₁ sX).symm
  -- the flat-pullback law of `c₂` at the base change of `f₁` along the test scheme
  have hIII : c₂.cap (pullback.snd f₁ t ≫ t) (k + (r : ℤ))
        (flatPullbackChow C ((pullback.snd f₁ t ≫ t) ≫ sX) (t ≫ sX) (pullback.snd f₁ t) hpsQ r
          hrQ k hfacN α) ≍
      flatPullbackChow C (pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX))
        (pullback.fst f₂ t ≫ (f₂ ≫ sX)) (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) hvP r
        hr' (k - p₂) hfacP (c₂.cap t k α) :=
    c₂.flat_naturality t (pullback.snd f₁ t) r hrQ
      (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) sqh' hfsth' k hr' hfacN hfacP α
  -- the isomorphism case of Stacks 02RG, moving that flat pullback onto `Z₁ ×_X (Z₂ ×_X T)`
  have hII := flatPullbackChow_chowPushforwardOfIso C ((pullback.fst f₂ t ≫ f₂) ≫ sX)
    (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX)) ((pullback.fst f₂ t ≫ f₂) ≫ sX)
    (pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX)) (𝟙 (pullback f₂ t))
    (Category.id_comp _)
    (commuteComparisonHom f₁ f₂ t ≫ (pullback.congrHom (rfl : f₂ = f₂) e).inv) hu₁
    (pullback.snd f₁ (pullback.fst f₂ t ≫ f₂)) hd
    (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) hv hsq r hdr hr' (k - p₂) hfacd hfacv
    (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂) (c₂.cap t k α))
  rw [chowPushforwardOfIso_id] at hII
  -- `c₁ ∩ α` is the flat pullback of `α`, read over the other shape of the test morphism
  have hcapt : chowGroupCongr C hQ (k - -(r : ℤ))
        ((flatPullbackBivariantClass C G (f₁ ≫ sX) sX f₁ rfl r hfr hS1 hRG h71).cap t k α) ≍
      flatPullbackChow C ((pullback.snd f₁ t ≫ t) ≫ sX) (t ≫ sX) (pullback.snd f₁ t) hpsQ r hrQ
        k hfacN α :=
    (chowGroupCongr_heq C hQ (k - -(r : ℤ)) _).trans
      ((flatPullbackBivariantClass_cap C G (f₁ ≫ sX) sX f₁ rfl r hfr hS1 hRG h71 t k α).trans
        (flatPullbackChow_heq_congr_base C hQ rfl rfl
          (pullbackSnd_comp_structureMorphism (rfl : f₁ ≫ sX = f₁ ≫ sX) t) hpsQ rfl hrQ hrQ rfl
          hfacL hfacN α α HEq.rfl))
  -- the flat pullback of `c₂ ∩ α`, read over the two shapes of the structure morphism of `P`
  have hbase : flatPullbackChow C (pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX))
        (pullback.fst f₂ t ≫ (f₂ ≫ sX)) (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) hvP r
        hr' (k - p₂) hfacP (c₂.cap t k α) ≍
      flatPullbackChow C (pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX))
        ((pullback.fst f₂ t ≫ f₂) ≫ sX) (bivariantBaseChangeMap f₂ t (pullback.snd f₁ t)) hv r
        hr' (k - p₂) hfacv
        (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
          (c₂.cap t k α)) :=
    flatPullbackChow_heq_congr_base C rfl (Category.assoc (pullback.fst f₂ t) f₂ sX).symm rfl
      hvP hv rfl hr' hr' rfl hfacP hfacv _ _
      (chowGroupCongr_heq C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
        (c₂.cap t k α)).symm
  -- the two pushforwards compose to the comparison isomorphism of the goal
  have hstep : ∀ x : chowGroup C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
        ((k - p₂) + (r : ℤ)),
      chowPushforwardOfIso C (pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX))
          (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
          (pullback.congrHom (rfl : f₂ = f₂) e).hom hcongrbase ((k - p₂) + (r : ℤ))
          (chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
            (pullback.fst f₂ (pullback.snd f₁ t ≫ t) ≫ (f₂ ≫ sX))
            (commuteComparisonHom f₁ f₂ t ≫ (pullback.congrHom (rfl : f₂ = f₂) e).inv) hu₁
            ((k - p₂) + (r : ℤ)) x) =
        chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
          (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) (commuteComparisonHom f₁ f₂ t)
          (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) + (r : ℤ)) x := by
    intro x
    rw [chowPushforwardOfIso_comp_apply]
    exact chowPushforwardOfIso_congr_apply C _ _ _ _ hcomp _ _ _ _
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply]
  refine eq_of_heq ?_
  -- assemble: start from the right-hand side and work back to the left
  refine HEq.symm (HEq.trans (chowGroupDegreeEquiv_heq C _ _ _) ?_)
  refine HEq.trans (heq_of_eq hIV.symm) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ hcongrbase hdeg₂ _ _
    (c₂.cap_heq_congr (pullback.snd f₁ t ≫ t) hk₁ _ _ hcapt)) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ hcongrbase hdeg₃ _ _ hIII) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ hcongrbase rfl _ _ hbase) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ hcongrbase rfl _ _
    (heq_of_eq hII)) ?_
  refine HEq.trans (heq_of_eq (hstep _)) ?_
  exact chowPushforwardOfIso_heq_congr C _ _ _
    (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) hdeg.symm _ _
    (flatPullbackBivariantClass_cap C G (f₁ ≫ sX) sX f₁ rfl r hfr hS1 hRG h71
      (pullback.fst f₂ t ≫ f₂) (k - p₂) _).symm

end Smooth

end Stacks.Chow

end
