module

public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport

/-!
# Chow groups along an isomorphism, and the identity base change

Chapter 42 of the Stacks Project makes proper pushforward on Chow groups available only after
Stacks 02S2, the assertion that proper pushforward of cycles preserves rational equivalence,
which this repository carries as the hypothesis
`Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence`. Along an **isomorphism** that
hypothesis is not needed: an isomorphism is a closed immersion, and
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion` proves
Stacks 02S2 for a closed immersion outright. So pushforward along an isomorphism over the base
is an unconditional homomorphism of Chow groups, and it is in fact an isomorphism of groups,
with inverse the pushforward along the inverse morphism.

This matters for the bivariant classes of Stacks 0B76. A bivariant class for `f : X ⟶ Y` caps
into the Chow group of the chosen categorical pullback `X ×_Y T`; for `f = 𝟙 X` that pullback is
not the test scheme `T` on the nose but only isomorphic to it, through
`pullback.snd (𝟙 X) g`. Every construction of a bivariant class for an identity morphism —
Stacks 0B77 for the first Chern class, Stacks 0B7H for the higher ones — therefore has to
transport an operation defined on `A_*(T)` across that isomorphism. This file provides the
transport once.

## Main definitions

* `Stacks.Chow.chowPushforwardOfIso` — proper pushforward on Chow groups along an isomorphism
  over the base, with no instance of Stacks 02S2 required.
* `Stacks.Chow.chowGroupEquivOfIso` — the same map read as an isomorphism `A_k(A) ≃+ A_k(B)`.
* `Stacks.Chow.identityBaseChangeIso` — the isomorphism `X ×_X T ≅ T` for the identity of `X`.

## Main results

* `Stacks.Chow.properPushforward_id`, `Stacks.Chow.properChowPushforward_id` — pushing forward
  along the identity does nothing, on cycles and on Chow classes.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isIso` — Stacks 02S2 along
  an isomorphism, unconditionally.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_isIso_comp_isIso` — Stacks 02S2
  for a morphism conjugated by isomorphisms, from the instance for the morphism itself. This is
  how the base-change isomorphisms let an instance of Stacks 02S2 upstairs be turned into one
  downstairs.
* `Stacks.Chow.properPushforward_congr`, `Stacks.Chow.properChowPushforward_congr`,
  `Stacks.Chow.chowPushforwardOfIso_congr` — pushforward is unchanged by replacing the morphism
  with an equal one; the properness instance and both `Prop` arguments are proof-irrelevant.
* `Stacks.Chow.identityBaseChangeIso_hom_comp`,
  `Stacks.Chow.identityBaseChangeIso_hom_comp_base`,
  `Stacks.Chow.fst_eq_identityBaseChangeIso_hom` — the identities of the identity base change
  that the bivariant constructions use.

## References

* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB]

/-! ### Pushforward along the identity -/

/-- **Stacks 02R4.** Proper pushforward of cycles along the identity is the identity. -/
@[simp]
theorem properPushforward_id (k : ℤ) (α : CycleGroup C sA k) :
    properPushforward C sA sA (𝟙 A) (Category.id_comp sA) k α = α := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [show (properPushforward C sA sA (𝟙 A) (Category.id_comp sA) k α).1 z = _ from
    properPushforward_apply C sA sA (𝟙 A) (Category.id_comp sA) k α z]
  simp

/-- **Stacks 02R4.** Proper pushforward of cycles is unchanged by replacing the morphism with an
equal one; the properness instance and the compatibility with the base are proof-irrelevant. -/
theorem properPushforward_congr (f g : A ⟶ B) [IsProper f] [IsProper g] (hfg : f = g)
    (hf : f ≫ sB = sA) (hg : g ≫ sB = sA) (k : ℤ) :
    properPushforward C sA sB f hf k = properPushforward C sA sB g hg k := by
  subst hfg
  rfl

/-! ### Stacks 02S2 along an isomorphism -/

/-- **Stacks 02S2 for an isomorphism.** Proper pushforward of `k`-cycles along an isomorphism
over the base factors through rational equivalence. Unlike the general case this needs no
hypothesis: an isomorphism is a closed immersion, where Stacks 02S2 is proved in
`StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport`. -/
theorem properPushforwardFactorsThroughRationalEquivalence_of_isIso (f : A ⟶ B) [IsIso f]
    (hf : f ≫ sB = sA) (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C sA sB f hf k :=
  properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion f C sA sB hf k

/-- Factoring through rational equivalence is unchanged by replacing the morphism with an equal
one. -/
theorem properPushforwardFactorsThroughRationalEquivalence_congr (f g : A ⟶ B) [IsProper f]
    [IsProper g] (hfg : f = g) (hf : f ≫ sB = sA) (hg : g ≫ sB = sA) (k : ℤ)
    (h : ProperPushforwardFactorsThroughRationalEquivalence C sA sB f hf k) :
    ProperPushforwardFactorsThroughRationalEquivalence C sA sB g hg k := by
  subst hfg
  exact h

/-- **Stacks 02S2 for a morphism conjugated by isomorphisms.** If proper pushforward along
`m : A' ⟶ B'` factors through rational equivalence, then so does pushforward along
`u ≫ m ≫ v` for isomorphisms `u` and `v` over the base: Stacks 02S2 is closed under composition
and holds outright for an isomorphism. -/
theorem properPushforwardFactorsThroughRationalEquivalence_isIso_comp_isIso {A' B' : Scheme.{u}}
    (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB']
    (u : A ⟶ A') [IsIso u] (m : A' ⟶ B') [IsProper m] (v : B' ⟶ B) [IsIso v]
    (hu : u ≫ sA' = sA) (hm : m ≫ sB' = sA') (hv : v ≫ sB = sB') (k : ℤ)
    (hm' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' m hm k) :
    ProperPushforwardFactorsThroughRationalEquivalence C sA sB (u ≫ m ≫ v)
      (by rw [Category.assoc, Category.assoc, hv, hm, hu]) k :=
  properPushforwardFactorsThroughRationalEquivalence_comp C sA sA' sB u (m ≫ v) hu
    (by rw [Category.assoc, hv, hm]) k
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sA' u hu k)
    (properPushforwardFactorsThroughRationalEquivalence_comp C sA' sB' sB m v hm hv k hm'
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sB' sB v hv k))

/-- The inverse of an isomorphism over the base is again over the base. -/
private theorem inv_comp_base_eq {S : Scheme.{u}} {p : A ⟶ S} {q : B ⟶ S} (f : A ⟶ B) [IsIso f]
    (hf : f ≫ q = p) : inv f ≫ p = q := by
  rw [IsIso.inv_comp_eq, hf]

/-- **Stacks 0GU8 for an isomorphism.** Proper pushforward on Chow groups along an isomorphism
over the base, `A_k(A) ⟶ A_k(B)`. This takes no instance of Stacks 02S2, which
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isIso` supplies. -/
def chowPushforwardOfIso (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (k : ℤ) :
    chowGroup C sA k →+ chowGroup C sB k :=
  properChowPushforward C sA sB f hf k
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sB f hf k)

/-- On the class of a cycle, pushforward along an isomorphism is the class of the pushed-forward
cycle. -/
@[simp]
theorem chowPushforwardOfIso_mk (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (k : ℤ)
    (α : CycleGroup C sA k) :
    chowPushforwardOfIso C sA sB f hf k
        (QuotientAddGroup.mk' (rationalEquivalences C sA k) α) =
      QuotientAddGroup.mk' (rationalEquivalences C sB k) (properPushforward C sA sB f hf k α) :=
  rfl

/-- Pushforward on Chow groups along an isomorphism is unchanged by replacing the morphism with
an equal one. -/
theorem chowPushforwardOfIso_congr (f g : A ⟶ B) [IsIso f] [IsIso g] (hfg : f = g)
    (hf : f ≫ sB = sA) (hg : g ≫ sB = sA) (k : ℤ) :
    chowPushforwardOfIso C sA sB f hf k = chowPushforwardOfIso C sA sB g hg k := by
  subst hfg
  rfl

/-- **Stacks 0GU8.** Pushforward on Chow groups along the identity is the identity. -/
@[simp]
theorem properChowPushforward_id (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sA (𝟙 A)
      (Category.id_comp sA) k) :
    properChowPushforward C sA sA (𝟙 A) (Category.id_comp sA) k hfac =
      AddMonoidHom.id (chowGroup C sA k) := by
  refine (eq_properChowPushforward C sA sA (𝟙 A) (Category.id_comp sA) k hfac
    (AddMonoidHom.id (chowGroup C sA k)) (AddMonoidHom.ext fun α ↦ ?_)).symm
  change QuotientAddGroup.mk' (rationalEquivalences C sA k) α =
    QuotientAddGroup.mk' (rationalEquivalences C sA k)
      (properPushforwardHom C sA sA (𝟙 A) (Category.id_comp sA) k α)
  rw [properPushforwardHom_apply, properPushforward_id]

/-- **Stacks 02R5, 0GU8.** Pushing forward along an isomorphism and then along its inverse does
nothing. -/
theorem chowPushforwardOfIso_inv_comp (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (k : ℤ)
    (x : chowGroup C sA k) :
    chowPushforwardOfIso C sB sA (inv f) (by rw [IsIso.inv_comp_eq, hf]) k
        (chowPushforwardOfIso C sA sB f hf k x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H α =>
    refine congrArg (QuotientAddGroup.mk' (rationalEquivalences C sA k)) ?_
    refine (congrFun (properPushforward_comp C sA sB sA f (inv f) hf
      (inv_comp_base_eq f hf) k) α).trans ?_
    rw [properPushforward_congr C sA sA (f ≫ inv f) (𝟙 A) (IsIso.hom_inv_id f)
      (by simp) (Category.id_comp sA) k, properPushforward_id]

/-- **Stacks 0GU8.** Pushforward on Chow groups is unchanged by replacing the morphism with an
equal one. -/
theorem properChowPushforward_congr (f g : A ⟶ B) [IsProper f] [IsProper g] (hfg : f = g)
    (hf : f ≫ sB = sA) (hg : g ≫ sB = sA) (k : ℤ)
    (hfacf : ProperPushforwardFactorsThroughRationalEquivalence C sA sB f hf k)
    (hfacg : ProperPushforwardFactorsThroughRationalEquivalence C sA sB g hg k) :
    properChowPushforward C sA sB f hf k hfacf = properChowPushforward C sA sB g hg k hfacg := by
  subst hfg
  rfl

/-- **Stacks 0GU8.** Proper pushforward on Chow groups along an isomorphism over the base is an
isomorphism of groups `A_k(A) ≃+ A_k(B)`, with inverse the pushforward along the inverse
morphism. -/
def chowGroupEquivOfIso (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (k : ℤ) :
    chowGroup C sA k ≃+ chowGroup C sB k where
  toFun := chowPushforwardOfIso C sA sB f hf k
  invFun := chowPushforwardOfIso C sB sA (inv f) (by rw [IsIso.inv_comp_eq, hf]) k
  left_inv x := chowPushforwardOfIso_inv_comp C sA sB f hf k x
  right_inv x := by
    have h := chowPushforwardOfIso_inv_comp C sB sA (inv f)
      (by rw [IsIso.inv_comp_eq, hf]) k x
    rwa [chowPushforwardOfIso_congr C sA sB (inv (inv f)) f (by simp)
      (by rw [IsIso.inv_inv]; exact hf) hf k] at h
  map_add' := map_add _

/-- The isomorphism `chowGroupEquivOfIso` acts as the pushforward `chowPushforwardOfIso` along
`f`. -/
@[simp]
theorem chowGroupEquivOfIso_apply (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (k : ℤ)
    (x : chowGroup C sA k) :
    chowGroupEquivOfIso C sA sB f hf k x = chowPushforwardOfIso C sA sB f hf k x :=
  rfl

/-- The inverse of `chowGroupEquivOfIso` acts as the pushforward `chowPushforwardOfIso` along
`inv f`. -/
@[simp]
theorem chowGroupEquivOfIso_symm_apply (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (k : ℤ)
    (x : chowGroup C sB k) :
    (chowGroupEquivOfIso C sA sB f hf k).symm x =
      chowPushforwardOfIso C sB sA (inv f) (by rw [IsIso.inv_comp_eq, hf]) k x :=
  rfl

end Stacks.Chow

/-! ### The identity base change -/

namespace Stacks.Chow

/-- The isomorphism `X ×_X T ≅ T` identifying the base change of the identity of `X` along
`g : T ⟶ X` with `T` itself. Its forward map is `pullback.snd (𝟙 X) g`. -/
abbrev identityBaseChangeIso {X T : Scheme.{u}} (g : T ⟶ X) : pullback (𝟙 X) g ≅ T :=
  asIso (pullback.snd (𝟙 X) g)

/-- The first projection of the identity base change factors through the isomorphism to the test
scheme: `pullback.fst (𝟙 X) g = (X ×_X T ≅ T) ≫ g`. -/
theorem fst_eq_identityBaseChangeIso_hom {X T : Scheme.{u}} (g : T ⟶ X) :
    pullback.fst (𝟙 X) g = (identityBaseChangeIso g).hom ≫ g := by
  simpa only [asIso_hom, Category.comp_id] using
    (pullback.condition : pullback.fst (𝟙 X) g ≫ 𝟙 X = pullback.snd (𝟙 X) g ≫ g)

/-- The inverse of the identity base change isomorphism is a section of the first projection
read over the base: `(T ≅ X ×_X T) ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX`. -/
theorem identityBaseChangeIso_hom_comp {X T : Scheme.{u}} (C : ChowSituation.{u})
    (sX : X ⟶ C.S) (g : T ⟶ X) :
    (identityBaseChangeIso g).inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX := by
  rw [fst_eq_identityBaseChangeIso_hom g, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The first projection of the identity base change, read over the base, is the pushforward of
`g ≫ sX` along the isomorphism: `(X ×_X T ≅ T) ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX`. -/
theorem identityBaseChangeIso_hom_comp_base {X T : Scheme.{u}} (C : ChowSituation.{u})
    (sX : X ⟶ C.S) (g : T ⟶ X) :
    (identityBaseChangeIso g).hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX := by
  rw [fst_eq_identityBaseChangeIso_hom g, Category.assoc]

end Stacks.Chow

end
