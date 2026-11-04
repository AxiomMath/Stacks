module

public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsCartesian
public import StacksFrontier.Deformation.Examples.Geometric.SchemesRimSchlessinger
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gluing flat schemes across a pushout square, as the Rim-Schlessinger argument consumes it

The Rim-Schlessinger condition for the families of Example [Stacks Project, Tag 0E3T] is proved
by gluing: a cospan of families over a cospan of Artinian local algebras whose second leg is
surjective lies over a pushout square of spectra, and the fibre product of families is
assembled from the pushouts of the sources and of the targets over that square.

Three facts about such a square are needed, and all three are theorems of this repository,
over Mathlib's canonical pushout and in the comma-category language of
`Stacks.Pushout.gluingData`: the two cartesian squares of [Stacks Project, Tag 07RV]
(`Stacks.Pushout.gluing_components_isPullback`), the closing paragraph of
[Stacks Project, Tag 07RX] (`Stacks.Pushout.gluingAdjunction_counit_app_isIso_of_flat`), and
clause (2) of Tag 07RX for the structure morphism of the glued scheme
(`Deformation.Examples.flat_pushoutDesc_of_isFiniteOrderThickening`).

This file names the three in the raw language of `CategoryTheory.IsPullback` and
`CategoryTheory.IsPushout` squares, which is the form the gluing argument uses them in, and
proves that the three are jointly satisfiable.

## Main definitions

* `Deformation.Examples.FlatGluingSquares`: the three gluing facts across one pushout square.

## Main results

* `Deformation.Examples.isPullback_source_toBase`: the source of a morphism of families is
  cartesian over the base, obtained by pasting the source square over the target with the
  target square over the base.
* `Deformation.Examples.flat_glued_of_isPushout`: the `flatGlued` field, proved -- the glued
  scheme is flat over the pushout.
* `Deformation.Examples.exists_flatGluingSquares`: the three facts, and the three standing
  premises under which they are available, all hold simultaneously at the identity square.

## Implementation notes

**Where the three fields come from.**  `flatGlued` is
`Deformation.Examples.flat_glued_of_isPushout` below, proved here: it is
`Deformation.Examples.flat_pushoutDesc_of_isFiniteOrderThickening` transported from Mathlib's
canonical pushout along `CategoryTheory.IsPushout.isoPushout`.  Note that it needs
`Stacks.Thickenings.IsFiniteOrderThickening` -- a closed immersion with nilpotent kernel -- and
not merely `Stacks.Thickenings.IsThickening`, which is the weaker surjective-on-points
condition; `restrict` and `descend` need only the latter, and
`Stacks.Thickenings.IsFiniteOrderThickening.isThickening` converts.  So a provider of all three
fields carries the finite-order hypothesis, used only by `flatGlued`.

**Why `descend` takes the commuting square as a hypothesis.**  Its conclusion
`IsPushout d₂ d₁ e₂ e₁` contains the commutation `d₂ ≫ e₂ = d₁ ≫ e₁`, and that commutation
does *not* follow from the four cartesian squares: replacing `d₂` by `d₂ ≫ α` for an
automorphism `α` of `W₂` over `S₂` preserves every hypothesis while changing the composite
`d₂ ≫ e₂`.  Stating it without that hypothesis therefore yields a predicate satisfied by no
square whatsoever, and any theorem proved from such a predicate asserts nothing while still
typechecking.  `Deformation.Examples.exists_flatGluingSquares` is the guard against
that: it exhibits a square at which the premises and all three facts hold at once.

**The degenerate witness.**  At the identity square every structure morphism in sight is an
isomorphism — a base change along an identity, or a cobase change of one — so each of the three
facts reduces to the statement that a commuting square of isomorphisms is cartesian, or
cocartesian, or carries flatness across. That is weak, and deliberately so: the witness is
there to refute joint unsatisfiability, not to stand in for the general facts.

## References

* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Thickenings

universe u v

namespace Deformation.Examples

/-- The three facts about gluing flat schemes across a pushout square `S₁ ⨿_S S₂ = T`, in the
raw language of cartesian and cocartesian squares. -/
structure FlatGluingSquares {S S₁ S₂ T : Scheme.{v}} (j₂ : S ⟶ S₂) (j₁ : S ⟶ S₁)
    (b₂ : S₂ ⟶ T) (b₁ : S₁ ⟶ T) : Prop where
  /-- The two restrictions of the glued scheme are the schemes it was glued from. -/
  restrict : ∀ {Y Y₁ Y₂ Z : Scheme.{v}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {z : Z ⟶ T}
    {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} {c₁ : Y₁ ⟶ Z} {c₂ : Y₂ ⟶ Z},
    IsPullback g₁ y y₁ j₁ → IsPullback g₂ y y₂ j₂ → IsPushout g₂ g₁ c₂ c₁ →
    c₁ ≫ z = y₁ ≫ b₁ → c₂ ≫ z = y₂ ≫ b₂ →
    IsPullback c₁ y₁ z b₁ ∧ IsPullback c₂ y₂ z b₂
  /-- A flat scheme over the pushout is the pushout of its two restrictions, once the square of
  restrictions is known to commute. -/
  descend : ∀ {W W₀ W₁ W₂ : Scheme.{v}} {w : W ⟶ T} {w₀ : W₀ ⟶ S} {w₁ : W₁ ⟶ S₁}
    {w₂ : W₂ ⟶ S₂} {e₁ : W₁ ⟶ W} {e₂ : W₂ ⟶ W} {d₁ : W₀ ⟶ W₁} {d₂ : W₀ ⟶ W₂},
    Flat w → d₂ ≫ e₂ = d₁ ≫ e₁ → IsPullback e₁ w₁ w b₁ → IsPullback e₂ w₂ w b₂ →
    IsPullback d₁ w₀ w₁ j₁ → IsPullback d₂ w₀ w₂ j₂ →
    IsPushout d₂ d₁ e₂ e₁
  /-- The glued scheme is flat over the pushout. -/
  flatGlued : ∀ {Y Y₁ Y₂ Z : Scheme.{v}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {z : Z ⟶ T}
    {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} {c₁ : Y₁ ⟶ Z} {c₂ : Y₂ ⟶ Z},
    Flat y₁ → Flat y₂ → IsPullback g₁ y y₁ j₁ → IsPullback g₂ y y₂ j₂ →
    IsPushout g₂ g₁ c₂ c₁ → c₁ ≫ z = y₁ ≫ b₁ → c₂ ≫ z = y₂ ≫ b₂ → Flat z

/-- An identity morphism is a thickening of finite order: its kernel ideal sheaf vanishes. -/
theorem isFiniteOrderThickening_id (S : Scheme.{v}) : IsFiniteOrderThickening (𝟙 S) :=
  ⟨inferInstance, 0, by rw [Scheme.Hom.ker_eq_bot_of_isIso (𝟙 S), pow_one]⟩

/-- The degenerate pushout square of identities. -/
theorem isPushout_id (S : Scheme.{v}) : IsPushout (𝟙 S) (𝟙 S) (𝟙 S) (𝟙 S) :=
  IsPushout.of_horiz_isIso ⟨by simp⟩

/-- The three gluing facts hold at the degenerate square of identities, where every structure
morphism in sight is an isomorphism. -/
theorem flatGluingSquares_id (S : Scheme.{v}) :
    FlatGluingSquares (𝟙 S) (𝟙 S) (𝟙 S) (𝟙 S) where
  restrict := by
    intro Y Y₁ Y₂ Z y y₁ y₂ z g₁ g₂ c₁ c₂ hg₁ hg₂ hZ hz₁ hz₂
    have : IsIso g₁ := hg₁.isIso_fst_of_isIso
    have : IsIso g₂ := hg₂.isIso_fst_of_isIso
    have : IsIso c₁ := hZ.isIso_inr_of_isIso
    have : IsIso c₂ := hZ.isIso_inl_of_isIso
    exact ⟨IsPullback.of_horiz_isIso ⟨hz₁⟩, IsPullback.of_horiz_isIso ⟨hz₂⟩⟩
  descend := by
    intro W W₀ W₁ W₂ w w₀ w₁ w₂ e₁ e₂ d₁ d₂ _ hcomm he₁ _ _ hd₂
    have : IsIso e₁ := he₁.isIso_fst_of_isIso
    have : IsIso d₂ := hd₂.isIso_fst_of_isIso
    exact IsPushout.of_horiz_isIso ⟨hcomm⟩
  flatGlued := by
    intro Y Y₁ Y₂ Z y y₁ y₂ z g₁ g₂ c₁ c₂ hy₁ _ hg₁ hg₂ hZ hz₁ _
    have : IsIso g₂ := hg₂.isIso_fst_of_isIso
    have : IsIso c₁ := hZ.isIso_inr_of_isIso
    have := hy₁
    rw [show z = inv c₁ ≫ y₁ by rw [IsIso.eq_inv_comp, hz₁, Category.comp_id]]
    infer_instance

/-- **The three gluing facts are jointly satisfiable, premises included.**  At the identity
square the three standing premises hold and all three facts hold, simultaneously.  This is the
guard against the failure mode of `Deformation.Examples.IsFlatGluing`, whose `descend` clause
is satisfied by no square at all, and which therefore makes every theorem proved from it
vacuous. -/
theorem exists_flatGluingSquares (S : Scheme.{v}) :
    IsFiniteOrderThickening (𝟙 S) ∧ IsAffineHom (𝟙 S) ∧
      IsPushout (𝟙 S) (𝟙 S) (𝟙 S) (𝟙 S) ∧ FlatGluingSquares (𝟙 S) (𝟙 S) (𝟙 S) (𝟙 S) :=
  ⟨isFiniteOrderThickening_id S, inferInstance, isPushout_id S, flatGluingSquares_id S⟩

/-- **The glued scheme is flat over the pushout** -- the `flatGlued` field of
`Deformation.Examples.FlatGluingSquares`, in raw-square form.

This is `Deformation.Examples.flat_pushoutDesc_of_isFiniteOrderThickening`, clause (2) of
[Stacks Project, Tag 07RX], transported off Mathlib's canonical pushout: the given cocone `z` is
identified with the canonical descent map followed by
`CategoryTheory.IsPushout.isoPushout`, and flatness is carried across the two isomorphisms. -/
@[sga "7 VI 4.3" "more general"]
theorem flat_glued_of_isPushout {S S₁ S₂ T : Scheme.{v}} {j₂ : S ⟶ S₂} {j₁ : S ⟶ S₁}
    {b₂ : S₂ ⟶ T} {b₁ : S₁ ⟶ T} (hj₂ : IsFiniteOrderThickening j₂) [IsAffineHom j₁]
    (hpo : IsPushout j₂ j₁ b₂ b₁)
    {Y Y₁ Y₂ Z : Scheme.{v}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {z : Z ⟶ T}
    {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} {c₁ : Y₁ ⟶ Z} {c₂ : Y₂ ⟶ Z}
    (hy₁ : Flat y₁) (hy₂ : Flat y₂)
    (h₁ : IsPullback g₁ y y₁ j₁) (h₂ : IsPullback g₂ y y₂ j₂)
    (hZ : IsPushout g₂ g₁ c₂ c₁)
    (hz₁ : c₁ ≫ z = y₁ ≫ b₁) (hz₂ : c₂ ≫ z = y₂ ≫ b₂) : Flat z := by
  have : HasPushout j₂ j₁ := hpo.hasPushout
  have : HasPushout g₂ g₁ := hZ.hasPushout
  have hw : g₂ ≫ y₂ ≫ Limits.pushout.inl j₂ j₁ = g₁ ≫ y₁ ≫ Limits.pushout.inr j₂ j₁ := by
    rw [reassoc_of% h₂.w, reassoc_of% h₁.w, Limits.pushout.condition]
  have hd := flat_pushoutDesc_of_isFiniteOrderThickening hj₂ h₁ h₂ hy₁ hy₂ hw
  have hcan : IsPushout g₂ g₁ (Limits.pushout.inl g₂ g₁) (Limits.pushout.inr g₂ g₁) :=
    IsPushout.of_hasPushout _ _
  have heq : (hcan.isoIsPushout _ _ hZ).inv ≫
      (IsPushout.of_hasPushout g₂ g₁).desc (y₂ ≫ Limits.pushout.inl j₂ j₁)
        (y₁ ≫ Limits.pushout.inr j₂ j₁) hw = z ≫ hpo.isoPushout.hom := by
    refine hZ.hom_ext ?_ ?_
    · rw [reassoc_of% hcan.inl_isoIsPushout_inv _ _ hZ, (IsPushout.of_hasPushout g₂ g₁).inl_desc,
        reassoc_of% hz₂, hpo.inl_isoPushout_hom]
    · rw [reassoc_of% hcan.inr_isoIsPushout_inv _ _ hZ, (IsPushout.of_hasPushout g₂ g₁).inr_desc,
        reassoc_of% hz₁, hpo.inr_isoPushout_hom]
  have hri : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{v}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hcomp := (MorphismProperty.cancel_left_of_respectsIso (@Flat : MorphismProperty Scheme.{v})
    (hcan.isoIsPushout _ _ hZ).inv _).mpr hd
  rw [heq] at hcomp
  exact (MorphismProperty.cancel_right_of_respectsIso (@Flat : MorphismProperty Scheme.{v}) z
    hpo.isoPushout.hom).mp hcomp

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The source of a morphism of flat families of morphisms of schemes is cartesian over the
base: paste the source square over the target with the target square over the base.  This is
the converse direction to `Deformation.Examples.isPullback_morphism_of_isPullback_toBase`, and
it is what feeds the two gluings -- of the sources and of the targets -- over one base
square. -/
theorem isPullback_source_toBase {P Q : SchemeMorphismFamily.{u, v} Λ k} (f : P ⟶ Q) :
    IsPullback f.source Q.sourceToBase P.sourceToBase (baseSpecMap f.base) := by
  have h := f.source_pullback.paste_horiz f.target_pullback.flip
  rw [Q.over_base, P.over_base] at h
  exact h.flip

end Deformation.Examples

end
