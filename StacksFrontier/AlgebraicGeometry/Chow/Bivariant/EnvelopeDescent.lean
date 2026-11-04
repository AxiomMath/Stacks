module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.Stability
public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift

/-!
# Uniqueness of the descent of bivariant Chow classes along an envelope

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` and let `g : Y' ⟶ Y` be an envelope
(Stacks 0GU5). Write `X' = X ×_Y Y'`. **Stacks 0GUC** asserts that a class
`c' ∈ A^p(X' ⟶ Y')` whose two restrictions to `A^p(X' ×_X X' ⟶ Y' ×_Y Y')` agree is the
restriction of a unique `c ∈ A^p(X ⟶ Y)`. This file proves the uniqueness: a bivariant class is
determined by its restriction along an envelope. The tag itself, existence and uniqueness
together, is `Stacks.Chow.existsUnique_bivariantRestriction_eq_of_isEnvelope` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentExistence`.

## Main results

* `Stacks.Chow.eq_of_isBivariantRestriction_of_isEnvelope'` — two bivariant classes of degree `p`
  for `f` whose restrictions along an envelope `g : Y' ⟶ Y` agree are equal.
* `Stacks.Chow.eq_of_isBivariantRestriction_of_isEnvelope` — the same statement, carrying the
  bundled Stacks 02S2 statement `Stacks.Chow.ProperPushforwardDescends` as an argument; it
  delegates to the form without it.
* `Stacks.Chow.bivariantRestrictionAddHom_injective_of_isEnvelope'` and
  `Stacks.Chow.bivariantRestrictionAddHom_injective_of_isEnvelope` — the same pair for the
  restriction map of Stacks 0F9Z: restriction along an envelope is injective.
* `Stacks.Chow.cap_eq_of_isBivariantRestriction_of_eq_comp` — two classes with the same
  restriction along `g` cap identically on every test scheme whose structure morphism to `Y`
  factors through `g`.

## Implementation notes

The proof of the tag computes `c ∩ β` for `β ∈ CH_k(Y₁)` by lifting `β` along the base-changed
envelope `Y'₁ = Y' ×_Y Y₁ ⟶ Y₁` and capping with `c'` upstairs. Uniqueness is the half of that
computation which needs no choice: the lift exists by the surjectivity statement of Stacks 0GU8
(`Stacks.Chow.envelope_chow_surjective`), the base change is again an envelope by Stacks 0GU7
(`AlgebraicGeometry.isEnvelope_isStableUnderBaseChange`), the structure morphism of `Y'₁` factors
through `g`, and so the proper-pushforward condition of Stacks 0B76 expresses `c ∩ β` in terms
of the restriction of `c` alone. No hypothesis on the two restrictions of `c'` is used.

Proper pushforward on Chow groups takes the vanishing of Stacks 02S2 as an explicit argument in
this repository; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow`. The argument needs it for the
base-changed envelope and for the base change of that envelope to `X`, at every test scheme and
degree, and takes it from `Stacks.Chow.properPushforwardDescends` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent`.

## References

* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0GU7](https://stacks.math.columbia.edu/tag/0GU7)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The canonical base change of a fibre product -/

/-- The map `T' ×_Y X ⟶ T ×_Y X` induced by `h : T' ⟶ T` is compatible with the projections
to `X`. -/
theorem bivariantBaseChangeMap_fst {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T) :
    bivariantBaseChangeMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
  simp [bivariantBaseChangeMap]

/-- Pushforward on Chow groups along an isomorphism over the base is injective, its inverse
being the pushforward along the inverse isomorphism. -/
theorem chowPushforwardOfIso_injective (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) (k : ℤ) :
    Function.Injective (chowPushforwardOfIso C sA sB u hu k) := by
  have hinv : inv u ≫ sA = sB := by
    rw [← hu, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hleft : ∀ z, chowPushforwardOfIso C sB sA (inv u) hinv k
      (chowPushforwardOfIso C sA sB u hu k z) = z := fun z => by
    rw [chowPushforwardOfIso_comp_apply C sA sB sA u (inv u) hu hinv k z,
      chowPushforwardOfIso_congr_apply C sA sA (u ≫ inv u) (𝟙 A) (by simp) _
        (Category.id_comp sA) k, chowPushforwardOfIso_id]
  intro x y hxy
  rw [← hleft x, ← hleft y, hxy]

/-! ### Uniqueness of a descent along an envelope -/

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (g : Y' ⟶ Y) [LocallyOfFiniteType g] (p : ℤ)

/-- Two bivariant classes of degree `p` for `f : X ⟶ Y` with the same restriction along
`g : Y' ⟶ Y` cap identically on every test scheme whose structure morphism to `Y` factors
through `g`. -/
theorem cap_eq_of_isBivariantRestriction_of_eq_comp
    {c d : BivariantClass C G sX sY f hf p}
    {c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p}
    (hc : IsBivariantRestriction C G sX sY f hf g p c c')
    (hd : IsBivariantRestriction C G sX sY f hf g p d c')
    {W : Scheme.{u}} (u : W ⟶ Y') [LocallyOfFiniteType u] (m : W ⟶ Y) [LocallyOfFiniteType m]
    (hm : m = u ≫ g) (k : ℤ) (β : chowGroup C (m ≫ sY) k) :
    c.cap m k β = d.cap m k β := by
  subst hm
  have hug : u ≫ (g ≫ sY) = (u ≫ g) ≫ sY := (Category.assoc u g sY).symm
  have hcc := hc u k ((chowGroupCongr C hug k).symm β)
  have hdd := hd u k ((chowGroupCongr C hug k).symm β)
  rw [bivariantRestrictionCap_apply] at hcc hdd
  rw [AddEquiv.apply_symm_apply] at hcc hdd
  exact chowPushforwardOfIso_injective C _ _ _ _ (k - p) (hcc.symm.trans hdd)

/-- **Uniqueness in Stacks 0GUC.** A bivariant class of degree `p` for `f : X ⟶ Y` is
determined by its restriction along an envelope `g : Y' ⟶ Y`. -/
theorem eq_of_isBivariantRestriction_of_isEnvelope' (hgE : IsEnvelope g)
    {c d : BivariantClass C G sX sY f hf p}
    {c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p}
    (hc : IsBivariantRestriction C G sX sY f hf g p c c')
    (hd : IsBivariantRestriction C G sX sY f hf g p d c') :
    c = d := by
  have hpp : ProperPushforwardDescends C := properPushforwardDescends C
  refine BivariantClass.ext C G sX sY f hf p ?_
  intro T t _ k β
  have hprop : IsProper g := hgE.isProper
  have henv : IsEnvelope (pullback.snd g t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {A B : Scheme.{u}} (q : A ⟶ B) ↦ IsEnvelope q)
      (IsPullback.of_hasPullback g t) hgE
  have hprop₁ : IsProper (pullback.snd g t) := henv.isProper
  set g₁ : pullback g t ⟶ T := pullback.snd g t
  have hAB : g₁ ≫ (t ≫ sY) = (g₁ ≫ t) ≫ sY := (Category.assoc g₁ t sY).symm
  obtain ⟨β', hβ'⟩ :=
    envelope_chow_surjective C (t ≫ sY) g₁ henv k (hpp (g₁ ≫ (t ≫ sY)) (t ≫ sY) g₁ rfl k) β
  have hfacA := hpp ((g₁ ≫ t) ≫ sY) (t ≫ sY) g₁ hAB k
  have hbridge := properChowPushforward_chowGroupCongr C hAB (rfl : t ≫ sY = t ≫ sY) g₁ rfl hAB k
    (hpp (g₁ ≫ (t ≫ sY)) (t ≫ sY) g₁ rfl k) hfacA β'
  have sq := isPullback_bivariantBaseChangeMap f t g₁
  have hfst := bivariantBaseChangeMap_fst f t g₁
  have hpropX : IsProper (bivariantBaseChangeMap f t g₁) :=
    MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have hfacX := hpp (pullback.fst f (g₁ ≫ t) ≫ sX) (pullback.fst f t ≫ sX)
    (bivariantBaseChangeMap f t g₁) (by rw [← Category.assoc, hfst]) (k - p)
  have hn (e : BivariantClass C G sX sY f hf p) :=
    e.proper_naturality t g₁ (bivariantBaseChangeMap f t g₁) sq hfst k hfacA hfacX
      (chowGroupCongr C hAB k β')
  have hstep := cap_eq_of_isBivariantRestriction_of_eq_comp C G sX sY f hf g p hc hd
    (pullback.fst g t) (g₁ ≫ t) pullback.condition.symm k (chowGroupCongr C hAB k β')
  have hβ : β = properChowPushforward C ((g₁ ≫ t) ≫ sY) (t ≫ sY) g₁ hAB k hfacA
      (chowGroupCongr C hAB k β') := by
    rw [← hbridge, hβ']
    exact (eq_of_heq (chowGroupCongr_heq C rfl k β)).symm
  rw [hβ, hn c, hn d, hstep]

/-- **Uniqueness in Stacks 0GUC**, read with the bundled Stacks 02S2 statement as an argument:
two classes whose restrictions to `A^p(X' ⟶ Y')` along an envelope are both `c'` agree. -/
theorem eq_of_isBivariantRestriction_of_isEnvelope
    (_hpp : ProperPushforwardDescends C) (hgE : IsEnvelope g)
    {c d : BivariantClass C G sX sY f hf p}
    {c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p}
    (hc : IsBivariantRestriction C G sX sY f hf g p c c')
    (hd : IsBivariantRestriction C G sX sY f hf g p d c') :
    c = d :=
  eq_of_isBivariantRestriction_of_isEnvelope' C G sX sY f hf g p hgE hc hd

/-- Restriction of bivariant classes along an envelope is injective: the uniqueness in Stacks
0GUC, read on the restriction map of Stacks 0F9Z. -/
theorem bivariantRestrictionAddHom_injective_of_isEnvelope'
    (hgys : G.IsNaturalUnderBaseChangeIso) (hgE : IsEnvelope g) :
    Function.Injective (bivariantRestrictionAddHom C G sX sY f hf g p hgys) := by
  intro c d hcd
  have hcd' : bivariantRestriction C G sX sY f hf g p hgys c =
    bivariantRestriction C G sX sY f hf g p hgys d := hcd
  refine eq_of_isBivariantRestriction_of_isEnvelope' C G sX sY f hf g p hgE
    (c' := bivariantRestriction C G sX sY f hf g p hgys d) ?_
    (isBivariantRestriction_bivariantRestriction C G sX sY f hf g p hgys d)
  rw [← hcd']
  exact isBivariantRestriction_bivariantRestriction C G sX sY f hf g p hgys c

/-- Restriction of bivariant classes along an envelope is injective, read with the bundled
Stacks 02S2 statement as an argument. -/
theorem bivariantRestrictionAddHom_injective_of_isEnvelope
    (hgys : G.IsNaturalUnderBaseChangeIso) (_hpp : ProperPushforwardDescends C)
    (hgE : IsEnvelope g) :
    Function.Injective (bivariantRestrictionAddHom C G sX sY f hf g p hgys) :=
  bivariantRestrictionAddHom_injective_of_isEnvelope' C G sX sY f hf g p hgys hgE

end Stacks.Chow

end
