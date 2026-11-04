module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverDegree
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusRelativeTwist

/-!
# `X^{(1)}/S` as a crystalline situation, and the relative Frobenius over it

[Stacks, Tag 07QB] is stated in the global crystalline situation of [Stacks, Tag 07MF] under the
single extra hypothesis `p ∈ I`: it sets `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` for `S₀ = V(I)`, writes
`F_{X/S₀} : X ⟶ X^{(1)}` for the relative Frobenius, and asserts for `X ⟶ S₀` smooth of relative
dimension `d` that `F_{X/S₀}` is an iterated `α_p`-cover of degree `p ^ d`, so that
[Stacks, Tag 07Q9] and [Stacks, Tag 07QA] apply to it.

This module puts that geometry into the global crystalline situation.  `X^{(1)}` becomes a global
crystalline situation over the *same* divided power base `(S, I, γ)`, the relative Frobenius
becomes a morphism of global crystalline situations `X/S ⟶ X^{(1)}/S` over the identity of `S`,
and the two conclusions of
`StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusAlphaPCover.lean` are read there.  That is
what [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] consume: their hypotheses on `f : X' ⟶ X` are
`AlgebraicGeometry.IsIteratedAlphaPCover` and `AlgebraicGeometry.HasConstantDegree`, for a
morphism of situations over one base.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.frobeniusTwistOver` — `X^{(1)}`, as a scheme over the
  closed fibre `S₀`.
* `Crystalline.GlobalCrystallineSituation.frobeniusTwistSituation` — **`X^{(1)}/S` as a global
  crystalline situation** over the same divided power base.
* `Crystalline.GlobalCrystallineSituation.relativeFrobeniusToTwist` — **`F_{X/S₀} : X ⟶ X^{(1)}`**
  in that situation.

## Main results

* `Crystalline.GlobalCrystallineSituation.isInCharacteristic_closedFiber_of_prime_mem` — the
  closed fibre is in characteristic `p` as soon as `p ∈ I`, which is the hypothesis
  [Stacks, Tag 07QB] adds to the global situation.
* `Crystalline.GlobalCrystallineSituation.toClosedFiber_comp_closedFiberMap_id` — the relative
  Frobenius is a morphism of global crystalline situations over the identity of `S`: it is the
  square over the closed fibre which the functoriality of the crystalline topos asks for.
* `Crystalline.GlobalCrystallineSituation.isIteratedAlphaPCoverOfDegree_relativeFrobeniusToTwist`
  — the conjunction of `...isIteratedAlphaPCover_relativeFrobeniusToTwist` and
  `...hasConstantDegree_relativeFrobeniusToTwist`, **the two
  hypotheses which [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] place on their morphism hold for
  `F_{X/S₀}` with `q = p ^ d`**, when `X ⟶ S₀` is smooth of relative dimension `d`.  This is the
  sentence "hence Lemmas 07Q9 and 07QA apply to this situation" of [Stacks, Tag 07QB].

## Relation to the Frobenius-crystal situation

`StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusRelativeTwist.lean` already builds `X^{(1)}`,
its crystalline situation and the relative Frobenius — but for a
`Crystalline.FCrystalSituation`, which asks for an affine base and a divided power endomorphism
`σ` of it lifting the absolute Frobenius, neither of which [Stacks, Tag 07QB] has.  The
constructions here are the same ones under [Stacks, Tag 07QB]'s own hypothesis `p ∈ I` alone, and
the agreement is machine-checked rather than asserted:
`Crystalline.FCrystalSituation.frobeniusTwistSituation_eq` and
`Crystalline.FCrystalSituation.relativeFrobeniusToTwist_eq` identify the two, by `rfl`.  So an
`F`-crystal situation may use either, and nothing is duplicated except the weakening of the
hypothesis.

## What is and is not proved

Everything here is proved under [Stacks, Tag 07QB]'s own hypotheses: the global situation,
`p ∈ I`, and — for the last two results — smoothness of `X ⟶ S₀` of relative dimension `d`.

`Crystalline.GlobalCrystallineSituation.isIteratedAlphaPCoverOfDegree_relativeFrobeniusToTwist`
is the first sentence of [Stacks, Tag 07QB] — `F_{X/S₀}` is an iterated `α_p`-cover of degree
`p ^ d` — in the source's own setting: the global crystalline situation of [Stacks, Tag 07MF]
with `p ∈ I`, `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` and `F_{X/S₀}` the relative Frobenius.  The tag
itself is registered on the statement of the whole lemma, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AlphaPCoverRelativeFrobenius07QB.lean`.  The
two statements of
`StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusAlphaPCover.lean` it specialises ask only that
the base be a scheme in characteristic `p`.

## References

* [Stacks Project, Lemma 60.26.5, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 0CC9](https://stacks.math.columbia.edu/tag/0CC9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (T : GlobalCrystallineSituation.{u})

/-- `X`, regarded as a scheme over the closed fibre `S₀ = V(I)`.  This is the input of the
Frobenius twist and of the relative Frobenius. -/
abbrev overClosedFiber : Over (DividedPowerScheme.closedFiber T.S) := Over.mk T.toClosedFiber

variable (hp : (T.p : Γ(T.S.scheme, ⊤)) ∈ T.S.ideal.obj (op ⊤))

include hp

/-! ### The closed fibre is in characteristic `p` -/

/-- **The closed fibre `S₀ = V(I)` is a scheme in characteristic `p`** as soon as `p` lies in the
divided power ideal, which is the hypothesis [Stacks, Tag 07QB] adds to the global crystalline
situation: the closed immersion `S₀ ⟶ S` kills every section of `I`, and `p` is one. -/
theorem isInCharacteristic_closedFiber_of_prime_mem :
    IsInCharacteristic (DividedPowerScheme.closedFiber T.S) T.p := by
  have h := (DividedPowerScheme.closedFiberPresentation T.S).app_eq_zero_of_mem ⊤
    (T.p : Γ(T.S.scheme, ⊤)) hp
  rw [map_natCast] at h
  exact h

/-! ### `X^{(1)}` and its crystalline situation -/

/-- **`X^{(1)} = X ×_{S₀, F_{S₀}} S₀`**, the Frobenius twist of `X` over the closed fibre, as a
scheme over `S₀`. -/
abbrev frobeniusTwistOver : Over (DividedPowerScheme.closedFiber T.S) :=
  (frobeniusTwist (DividedPowerScheme.closedFiber T.S) T.p
    (T.isInCharacteristic_closedFiber_of_prime_mem hp)).obj T.overClosedFiber

/-- **The projection `X^{(1)} ⟶ X`**, the first projection of the fibre product defining the
Frobenius twist. -/
def twistProjection : (T.frobeniusTwistOver hp).left ⟶ T.X :=
  pullback.fst T.toClosedFiber
    (absoluteFrobenius (DividedPowerScheme.closedFiber T.S) T.p
      (T.isInCharacteristic_closedFiber_of_prime_mem hp))

/-- **`X^{(1)}/S` as a global crystalline situation [Stacks, Tag 07MF]**, over the same divided
power base `(S, I, γ)` as `X/S`: the scheme is `X^{(1)}` and the structure morphism to the closed
fibre is the second projection.  The prime is locally nilpotent on `X^{(1)}` because it is on `X`
and the projection `X^{(1)} ⟶ X` induces maps of local rings. -/
def frobeniusTwistSituation : GlobalCrystallineSituation.{u} where
  p := T.p
  S := T.S
  X := (T.frobeniusTwistOver hp).left
  toClosedFiber := (T.frobeniusTwistOver hp).hom
  prime_locallyNilpotent x := by
    simpa using (T.prime_locallyNilpotent ((T.twistProjection hp).base x)).map
      ((T.twistProjection hp).stalkMap x).hom

/-- The prime of the situation `X^{(1)}/S` is the prime of `X/S`. -/
@[simp]
theorem frobeniusTwistSituation_p : (T.frobeniusTwistSituation hp).p = T.p := rfl

/-- The divided power base of `X^{(1)}/S` is that of `X/S`. -/
@[simp]
theorem frobeniusTwistSituation_S : (T.frobeniusTwistSituation hp).S = T.S := rfl

/-- The scheme of the situation `X^{(1)}/S` is `X^{(1)}`. -/
@[simp]
theorem frobeniusTwistSituation_X :
    (T.frobeniusTwistSituation hp).X = (T.frobeniusTwistOver hp).left := rfl

/-- The structure morphism of `X^{(1)}/S` to the closed fibre is that of `X^{(1)}` over `S₀`. -/
@[simp]
theorem frobeniusTwistSituation_toClosedFiber :
    (T.frobeniusTwistSituation hp).toClosedFiber = (T.frobeniusTwistOver hp).hom := rfl

/-- **The relative Frobenius `F_{X/S₀} : X ⟶ X^{(1)}`** of [Stacks, Tag 07QB]. -/
def relativeFrobeniusToTwist : T.X ⟶ (T.frobeniusTwistOver hp).left :=
  (relativeFrobenius (DividedPowerScheme.closedFiber T.S) T.p
    (T.isInCharacteristic_closedFiber_of_prime_mem hp) T.overClosedFiber).left

/-- The relative Frobenius is a morphism over `S₀`: followed by the structure morphism of
`X^{(1)}` it is the structure morphism of `X`. -/
theorem relativeFrobeniusToTwist_comp_toClosedFiber :
    T.relativeFrobeniusToTwist hp ≫ (T.frobeniusTwistOver hp).hom = T.toClosedFiber :=
  relativeFrobenius_snd (DividedPowerScheme.closedFiber T.S) T.p
    (T.isInCharacteristic_closedFiber_of_prime_mem hp) T.overClosedFiber

/-- **The relative Frobenius is a morphism of global crystalline situations over the identity of
`S`.**  This is the square over the closed fibre that the functoriality of the crystalline topos
asks for, and it is the hypothesis `hf` of every statement about `f_cris` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AlphaPCoverTriangle.lean`. -/
theorem toClosedFiber_comp_closedFiberMap_id :
    T.toClosedFiber ≫ DividedPowerScheme.closedFiberMap (𝟙 T.S) =
      T.relativeFrobeniusToTwist hp ≫ (T.frobeniusTwistSituation hp).toClosedFiber := by
  show _ = T.relativeFrobeniusToTwist hp ≫ (T.frobeniusTwistOver hp).hom
  rw [DividedPowerScheme.closedFiberMap_id, Category.comp_id,
    T.relativeFrobeniusToTwist_comp_toClosedFiber]

/-! ### The hypotheses of [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] at the relative Frobenius -/

/-- **`F_{X/S₀}` is an iterated `α_p`-cover**, for `X ⟶ S₀` smooth of relative dimension `d`:
the first hypothesis [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] place on their morphism, read in
the global crystalline situation of [Stacks, Tag 07QB].

This is `AlgebraicGeometry.isIteratedAlphaPCover_relativeFrobenius`, whose base is any scheme in
characteristic `p`, at the closed fibre `S₀ = V(I)`. -/
theorem isIteratedAlphaPCover_relativeFrobeniusToTwist (d : ℕ)
    [SmoothOfRelativeDimension d T.toClosedFiber] :
    IsIteratedAlphaPCover T.p (T.relativeFrobeniusToTwist hp) :=
  have : SmoothOfRelativeDimension d T.overClosedFiber.hom := ‹_›
  isIteratedAlphaPCover_relativeFrobenius (DividedPowerScheme.closedFiber T.S) T.p
    (T.isInCharacteristic_closedFiber_of_prime_mem hp) T.overClosedFiber d

/-- **`F_{X/S₀}` has constant degree `p ^ d`**, for `X ⟶ S₀` smooth of relative dimension `d`:
the second hypothesis [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] place on their morphism, with
their `q` equal to `p ^ d`, read in the global crystalline situation of [Stacks, Tag 07QB].

This is `AlgebraicGeometry.hasConstantDegree_relativeFrobenius`, whose base is any scheme in
characteristic `p`, at the closed fibre `S₀ = V(I)`. -/
theorem hasConstantDegree_relativeFrobeniusToTwist (d : ℕ)
    [SmoothOfRelativeDimension d T.toClosedFiber] :
    HasConstantDegree (T.relativeFrobeniusToTwist hp) (T.p ^ d) :=
  have : SmoothOfRelativeDimension d T.overClosedFiber.hom := ‹_›
  hasConstantDegree_relativeFrobenius (DividedPowerScheme.closedFiber T.S) T.p
    (T.isInCharacteristic_closedFiber_of_prime_mem hp) T.overClosedFiber d

/-- **`F_{X/S₀}` is an iterated `α_p`-cover of degree `p ^ d`**, the first sentence of
[Stacks, Lemma 60.26.5, Tag 07QB].  In the global crystalline situation of [Stacks, Tag 07MF]
with `p` in the divided power ideal `I`, let `S₀ = V(I)`, `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` and
`F_{X/S₀} : X ⟶ X^{(1)}` the relative Frobenius.  If `X ⟶ S₀` is smooth of relative dimension
`d`, then `F_{X/S₀}` is an iterated `α_p`-cover and has constant degree `p ^ d`.

These are exactly the two hypotheses [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] place on their
morphism, with their `q` equal to `p ^ d`.  The whole of [Stacks, Tag 07QB], this together with
the bound on crystalline cohomology, is
`...SmallSite.relativeFrobeniusToTwist_isIteratedAlphaPCover_cohomologyBound`.
-/
theorem isIteratedAlphaPCoverOfDegree_relativeFrobeniusToTwist (d : ℕ)
    [SmoothOfRelativeDimension d T.toClosedFiber] :
    IsIteratedAlphaPCover T.p (T.relativeFrobeniusToTwist hp) ∧
      HasConstantDegree (T.relativeFrobeniusToTwist hp) (T.p ^ d) :=
  ⟨T.isIteratedAlphaPCover_relativeFrobeniusToTwist hp d,
    T.hasConstantDegree_relativeFrobeniusToTwist hp d⟩

end Crystalline.GlobalCrystallineSituation

/-! ### Agreement with the Frobenius-crystal situation -/

namespace Crystalline.FCrystalSituation

variable (T : FCrystalSituation.{u})

/-- The Frobenius twist situation of an `F`-crystal situation is the one built here from
`p ∈ I` alone.  An `F`-crystal situation has an affine base and a divided power endomorphism `σ`
of it, and neither is used by either construction. -/
theorem frobeniusTwistSituation_eq :
    T.frobeniusTwistSituation = T.global.frobeniusTwistSituation T.prime_mem := rfl

/-- The relative Frobenius of an `F`-crystal situation is the one built here from `p ∈ I`
alone. -/
theorem relativeFrobeniusToTwist_eq :
    T.relativeFrobeniusToTwist = T.global.relativeFrobeniusToTwist T.prime_mem := rfl

end Crystalline.FCrystalSituation

end

end
