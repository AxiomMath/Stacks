module

public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper pushforward on Chow groups along a closed immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. Proper pushforward on
Chow groups, `Stacks.Chow.properChowPushforward`, takes an instance of
`Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence` — the assertion of Stacks 02S2
that proper pushforward of cycles carries rational equivalences to rational equivalences. That
assertion is a theorem for every proper morphism
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`), but its proof runs
through Stacks 02RU.

Along a **closed immersion** the hypothesis is discharged directly, with no appeal to Stacks
02RU:
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion` proves
Stacks 02S2 outright for a closed immersion, by transporting the principal divisor of a rational
function on an integral closed subscheme `V ⊆ X` to the principal divisor of the corresponding
rational function on its isomorphic image in `Y`. So pushforward on Chow groups along a closed
immersion over the base is an unconditional homomorphism

  `i_* : A_k(X) ⟶ A_k(Y)`,

and this file packages it, with the cycle-representative formula, functoriality, and the
identification with the general `Stacks.Chow.properChowPushforward` against any instance of
Stacks 02S2 whatsoever.

The parallel packaging for an isomorphism is `Stacks.Chow.chowPushforwardOfIso` in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport`; an isomorphism is a closed
immersion, and the two maps agree definitionally.

## Main definitions

* `Stacks.Chow.chowPushforwardOfIsClosedImmersion` — **Stacks 0GU8** for a closed immersion:
  proper pushforward on Chow groups along a closed immersion over the base, taking no instance
  of Stacks 02S2.

## Main results

* `Stacks.Chow.chowPushforwardOfIsClosedImmersion_mk` — on the class of a cycle it is the class
  of the pushed-forward cycle.
* `Stacks.Chow.properChowPushforward_eq_chowPushforwardOfIsClosedImmersion` — against any
  instance of Stacks 02S2 the general map agrees with this one, so nothing is lost by using the
  unconditional form.
* `Stacks.Chow.chowPushforwardOfIsClosedImmersion_comp` — **Stacks 02R5** for closed immersions:
  the composite of the two pushforwards is the pushforward along the composite.
* `Stacks.Chow.chowPushforwardOfIsClosedImmersion_congr` — the map depends only on the morphism,
  not on the closed-immersion instance or on the compatibility proof.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_id` and
  `Stacks.Chow.chowPushforwardOfIsClosedImmersion_cycleAssociatedToClosedSubscheme` — the
  fundamental cycle `[X]_k = [X ⊆ X]_k` of `X` pushes forward along `i : X ⟶ Y` to the cycle
  `[X ⊆ Y]_k` of `X` as a closed subscheme of `Y`, both as cycles and as Chow classes.

## References

* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]

/-- **Stacks 0GU8 for a closed immersion.** Proper pushforward on Chow groups along a closed
immersion `p : X ⟶ Y` over the base, `i_* : A_k(X) ⟶ A_k(Y)`.

This takes no instance of Stacks 02S2:
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion` supplies
one. -/
@[sga "6 XIV 3.2" "more general"]
def chowPushforwardOfIsClosedImmersion (p : X ⟶ Y) [IsClosedImmersion p] (hp : p ≫ sY = sX)
    (k : ℤ) : chowGroup C sX k →+ chowGroup C sY k :=
  properChowPushforward C sX sY p hp k
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion p C sX sY hp k)

/-- **Stacks 0GU8.** On the class of a cycle, pushforward along a closed immersion is the class
of the proper pushforward of that cycle. -/
@[simp]
theorem chowPushforwardOfIsClosedImmersion_mk (p : X ⟶ Y) [IsClosedImmersion p]
    (hp : p ≫ sY = sX) (k : ℤ) (α : CycleGroup C sX k) :
    chowPushforwardOfIsClosedImmersion C sX sY p hp k
        (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) =
      QuotientAddGroup.mk' (rationalEquivalences C sY k) (properPushforward C sX sY p hp k α) :=
  rfl

/-- Against any instance of Stacks 02S2, the general proper pushforward on Chow groups along a
closed immersion is the unconditional one: the instance is a `Prop`, so the two maps are equal
by proof irrelevance. Nothing is therefore lost by stating a closed-immersion pushforward in the
unconditional form. -/
theorem properChowPushforward_eq_chowPushforwardOfIsClosedImmersion (p : X ⟶ Y)
    [IsClosedImmersion p] (hp : p ≫ sY = sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k) :
    properChowPushforward C sX sY p hp k hfac =
      chowPushforwardOfIsClosedImmersion C sX sY p hp k :=
  rfl

/-- Pushforward along a closed immersion is unchanged by replacing the morphism with an equal
one. -/
theorem chowPushforwardOfIsClosedImmersion_congr (p q : X ⟶ Y) [IsClosedImmersion p]
    [IsClosedImmersion q] (hpq : p = q) (hp : p ≫ sY = sX) (hq : q ≫ sY = sX) (k : ℤ) :
    chowPushforwardOfIsClosedImmersion C sX sY p hp k =
      chowPushforwardOfIsClosedImmersion C sX sY q hq k := by
  subst hpq
  rfl

/-- **Stacks 02R5, 0GU8.** Pushforward on Chow groups along closed immersions is functorial. -/
theorem chowPushforwardOfIsClosedImmersion_comp (f : X ⟶ Y) [IsClosedImmersion f] (g : Y ⟶ Z)
    [IsClosedImmersion g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ) :
    (chowPushforwardOfIsClosedImmersion C sY sZ g hg k).comp
        (chowPushforwardOfIsClosedImmersion C sX sY f hf k) =
      chowPushforwardOfIsClosedImmersion C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k :=
  properChowPushforward_comp C sX sY sZ f g hf hg k _ _

/-! ### The fundamental cycle of a closed immersion -/

/-- The cycle `[W ⊆ X]_k` of a closed subscheme depends only on the closed immersion presenting
it: replacing that immersion with an equal one, or its closed-immersion instance with another,
leaves the cycle unchanged. -/
theorem cycleAssociatedToClosedSubscheme_congr {W : Scheme.{u}} (p q : W ⟶ X)
    [IsClosedImmersion p] [IsClosedImmersion q] (hpq : p = q) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sX p k = cycleAssociatedToClosedSubscheme C sX q k := by
  subst hpq
  rfl

/-- The proper pushforward of the fundamental cycle of `X` along a closed immersion
`i : X ⟶ Y` over the base is the cycle associated to `X` as a closed subscheme of `Y`:

  `i_* [X]_k = [X ⊆ Y]_k`.

Here `[X]_k` is realized as the cycle `[X ⊆ X]_k` of `X` as a closed subscheme of itself through
the identity, whose coefficient at the generic point of an irreducible component of
delta-dimension `k` is the multiplicity of that component. This is the case `Z = X`, `i = 𝟙 X` of
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp`. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_id (i : X ⟶ Y) [IsClosedImmersion i]
    (hi : i ≫ sY = sX) (k : ℤ) :
    properPushforward C sX sY i hi k (cycleAssociatedToClosedSubscheme C sX (𝟙 X) k) =
      cycleAssociatedToClosedSubscheme C sY i k :=
  (properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      C sX sY i hi (𝟙 X) k).trans
    (cycleAssociatedToClosedSubscheme_congr C sY (𝟙 X ≫ i) i (Category.id_comp i) k)

/-- On Chow groups, pushforward along a closed immersion `i : X ⟶ Y` carries the fundamental
class of `X` to the class of `X` as a closed subscheme of `Y`:

  `i_* [X]_k = [X ⊆ Y]_k` in `A_k(Y)`.

This is `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_id` read through
`Stacks.Chow.chowPushforwardOfIsClosedImmersion_mk`. -/
theorem chowPushforwardOfIsClosedImmersion_cycleAssociatedToClosedSubscheme (i : X ⟶ Y)
    [IsClosedImmersion i] (hi : i ≫ sY = sX) (k : ℤ) :
    chowPushforwardOfIsClosedImmersion C sX sY i hi k
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sX (𝟙 X) k)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sY i k) := by
  have h := chowPushforwardOfIsClosedImmersion_mk C sX sY i hi k
    (cycleAssociatedToClosedSubscheme C sX (𝟙 X) k)
  rw [properPushforward_cycleAssociatedToClosedSubscheme_id] at h
  exact h

end Stacks.Chow

end
