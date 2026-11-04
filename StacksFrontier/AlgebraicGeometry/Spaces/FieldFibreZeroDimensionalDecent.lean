module

public import Mathlib.Order.SetNotation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldFibreTopologicalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDiscreteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreFiniteDecent

/-!
# The zero-dimensional fibre conditions of Stacks 0ACK

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, let `y` be the point
of `|Y|` it represents, let `F = f^{-1}({y}) ⊂ |X|` be the set-theoretic fibre and let
`X_k = X ×_Y Spec(k)` be the field fibre. Stacks 0ACK compares eight conditions on this data.
This file supplies the implications which run *out of* the two Krull-dimension conditions on
those fibres as topological spaces:

* (3) `dim(F) = 0`;
* (6) `dim(|X_k|) = 0`.

`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreConditions.lean` states the conditions, and the
implications among conditions (1), (2), (4), (5), (7) and (8) are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibre.lean`,
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreQuasiFinite.lean`,
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreEquivalences.lean`,
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreFiniteDecent.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreDiscreteDecent.lean`. With those two arrows in
place the tag's two closing clauses follow, and they are proved here too: the six-way
equivalence for a decent target, and that condition (1) implies the rest when `X` and `Y` are
both decent.

Those two arrows are the only false ones in the tag, and what each of them needs is that the
fibre it starts from be Kolmogorov. Every statement here therefore carries `T0Space` on `F` or
on `|X_k|` rather than a decency hypothesis on `f`: `T₀` is strictly weaker, decency of `f`
being one of its sufficient conditions, and `t0Space_points_fieldFibre_of_isDecent` and
`t0Space_setFibre_of_isDecentSpace_source` are the two bridges from decency to it.

## Main definitions

No new definitions are introduced.

## Main results

* `t0Space_points_fieldFibre_of_isDecent` and `t0Space_setFibre_of_isDecentSpace_source`, in
  `AlgebraicGeometry.Space`: the point space of the field fibre of a decent morphism, and the
  set-theoretic fibre of a morphism out of a decent algebraic space, are Kolmogorov.
* `isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space`, in the same
  namespace, is Stacks 0ACK, condition (6) implies condition (5), with the hypothesis on
  `|X_k|` that the source omits.
* `AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints`:
  the same implication for a decent morphism.
* `isZeroDimensionalFieldFibre_of_isZeroDimensionalFieldFibrePoints` and
  `isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibrePoints`, in the same
  namespace: condition (6) implies conditions (7) and (8) for a Kolmogorov `|X_k|`.
* `AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_iff_isZeroDimensionalFieldFibrePoints`
  and
  `AlgebraicGeometry.Space.isZeroDimensionalFieldFibre_iff_isZeroDimensionalFieldFibrePoints`:
  conditions (5), (6) and (7) are equivalent for a Kolmogorov `|X_k|`.
* `AlgebraicGeometry.Space.isDiscreteSetFibre_of_isZeroDimensionalSetFibre` and
  `AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_of_isZeroDimensionalSetFibre`: condition
  (3) implies conditions (2) and (5) for a decent target and a Kolmogorov `F`.
* `AlgebraicGeometry.Space.isDiscreteSetFibre_iff_isZeroDimensionalSetFibre`: conditions (2)
  and (3) are equivalent for a decent target and a Kolmogorov `F`.
* `AlgebraicGeometry.Space.tfae_fibre_conditions_of_isDecentSpace_target`: conditions (2), (5),
  (7) and (8) are equivalent for a decent target, with no further hypothesis on `f`.
* `AlgebraicGeometry.Space.tfae_fibre_conditions`: conditions (2), (3), (5), (6), (7) and (8)
  are equivalent for a decent target with `F` and `|X_k|` Kolmogorov.
* `AlgebraicGeometry.Space.fibre_conditions_of_finite_setFibre_of_isDecent`: condition (1)
  implies all the other conditions when `X` and `Y` are decent.

## Implementation notes

**The source's unrestricted claim that conditions (5) and (6) are equivalent is false, and so
is its claim that conditions (2) and (3) are equivalent for a decent target.** The displayed
diagram of Stacks 0ACK asserts `(5) ⇔ (6) ⇔ (7) ⇔ (8)` with no hypothesis beyond `f` locally of
finite type, and its proof opens by deriving that row from Lemma 0ACA, which compares the same
conditions for an algebraic space locally of finite type over a field. But the arrow of Lemma
0ACA from `dim(|X|) = 0` to discreteness of `|X|` is itself false: the point space of `𝔸¹_k/ℤ`
is the indiscrete topology on infinitely many points, so it has Krull dimension zero without
being discrete, and that space is locally of finite type over `k`. The counterexample is
`Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints`
(`StacksFrontier/Examples/Spaces/ZeroDimensionalPointsNotDiscrete.lean`).

It refutes Stacks 0ACK's `(6) ⇒ (5)` directly, with no extra construction: take `Y = Spec(k)`,
which is a scheme and hence a decent algebraic space, take `X = 𝔸¹_k/ℤ` with its structure
morphism, and take `p` to be the only field-valued point of `Y` there is. Then `X_k = X` and
`F = |X|`, so condition (6) holds and condition (5) fails. The same data refutes the source's
"if `Y` is decent then conditions (2) and (3) are equivalent", since `Y` is decent here. That
refutation is carried out in
`StacksFrontier/Examples/Spaces/FieldFibreZeroDimensionalNotDiscrete.lean`, as
`not_forall_isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints` (in
`AlgebraicGeometry.Space`) and its companions for conditions (7) and (8), each quantified over a
decent target.

What repairs both is exactly `T₀` on the fibre the arrow starts from, which is what the
corrected arrow of Lemma 0ACA,
`AlgebraicGeometry.Space.discreteTopology_points_of_topologicalKrullDim_eq_zero`, asks for.
Decency of `f` is the source's own sufficient condition for it: the field fibre of a decent
morphism is a decent algebraic space (`AlgebraicGeometry.Space.isDecentSpace_fieldFibre`) and
the point space of a decent algebraic space is Kolmogorov by Stacks 03K3
(`AlgebraicGeometry.Space.t0Space_points_of_isDecentSpace`). A morphism whose source is a
decent algebraic space is a decent morphism by the decent case of Stacks 0ABX
(`AlgebraicGeometry.Space.isDecent_of_isDecentSpace_source`), so decency of `f` is in
particular available when `X` is decent — which is a hypothesis the source itself makes, in its
last clause. The statements here carry the `T₀` hypothesis and not the decency, since `T₀` is
the weaker of the two.

The arrows out of condition (3) are the ones the source proves through Lemma 0AC8. Decency of
`Y` supplies a field-valued point `q` representing `y` whose presenting morphism is a
quasi-compact monomorphism, and for that representative Lemma 0AC8 identifies `|X_q|` with `F`
as topological spaces (`AlgebraicGeometry.Space.homeomorphSetFibre`); the Krull dimension of a
topological space is a homeomorphism invariant, so condition (3) for `p` is condition (6) for
`q`, and `T₀` of `F` is `T₀` of `|X_q|`, which is what the repaired `(6) ⇒ (5)` needs at `q`.
Transporting discreteness back across the same homeomorphism gives condition (2) for `p`. This
is why the arrows out of condition (3) carry `T0Space F` rather than `T0Space |X_p|`: the
comparison map `|X_p| → F` is a homeomorphism only for a monomorphic representative, so `T₀`
of `F` is the hypothesis that reaches `q`, and it is implied by `T₀` of `|X|` and so by decency
of `X`.

No nonemptiness hypothesis is attached to the implications out of conditions (3) and (6).
`topologicalKrullDim` lands in `WithBot ℕ∞`, so a space of Krull dimension `0` is already
nonempty — the empty space has dimension `⊥` — and
`AlgebraicGeometry.Space.nonempty_of_topologicalKrullDim_eq_zero` extracts that. It is what
feeds the `= 0` form of the dimension of Tag 04N6 in condition (7). The hypothesis survives
only in the two equivalences whose *other* side is a discreteness condition, since the empty
fibre is discrete while failing conditions (3) and (6), and in the last clause, whose condition
(1) also holds at the empty fibre. The counterexamples of
`StacksFrontier/Examples/Spaces/EmptyFibreNotZeroDimensional.lean` show those hypotheses cannot be
dropped, and the counterexamples of
`StacksFrontier/Examples/Spaces/FieldFibreZeroDimensionalNotDiscrete.lean` are stated with a
nonempty fibre, which shows nonemptiness does not stand in for the `T₀` hypotheses either.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 0ABX](https://stacks.math.columbia.edu/tag/0ABX)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Krull dimension zero forces a point -/

/-- A topological space of Krull dimension zero is nonempty: `topologicalKrullDim` takes values
in `WithBot ℕ∞` and the empty space is the one with value `⊥`. -/
theorem nonempty_of_topologicalKrullDim_eq_zero (T : Type*) [TopologicalSpace T]
    (h : topologicalKrullDim T = (0 : WithBot ℕ∞)) : Nonempty T := by
  rcases isEmpty_or_nonempty T with hT | hT
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty T).mpr hT] at h
    exact absurd h (by simp)
  · exact hT

/-! ### Kolmogorov point spaces from decency -/

/-- **The point space of the field fibre of a decent morphism is Kolmogorov.** The field fibre
of a decent morphism is a decent algebraic space, and the point space of a decent algebraic
space is `T₀` by Stacks 03K3.

This is the source's own sufficient condition for the `T₀` hypothesis that the arrows out of
conditions (3) and (6) need and the source omits. Decency of `f` is available in particular
when `X` is a decent algebraic space, by the decent case of Stacks 0ABX. -/
theorem t0Space_points_fieldFibre_of_isDecent (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hd : IsDecent B S hS f)
    (p : FieldValuedPoint B S hS Y) :
    T0Space (points B S hS (fieldFibre B S hS f p)) :=
  t0Space_points_of_isDecentSpace B S hS (isAlgebraicSpace_fieldFibre hX hY f p)
    (isDecentSpace_fieldFibre B S hS f hd p)

/-- **The set-theoretic fibre of a morphism out of a decent algebraic space is Kolmogorov.**
The point space of a decent algebraic space is `T₀` by Stacks 03K3, and `F` carries the
topology induced from `|X|`, so it is `T₀` as a subspace.

This is the sufficient condition for the `T₀` hypothesis on `F` that the arrows out of
condition (3) need; decency of `X` is a hypothesis the source itself makes, in its last
clause. -/
theorem t0Space_setFibre_of_isDecentSpace_source (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hXdec : IsDecentSpace B S hS X) (p : FieldValuedPoint B S hS Y) :
    T0Space (setFibre B S hS f p) := by
  have := t0Space_points_of_isDecentSpace B S hS hX hXdec
  infer_instance

/-! ### Condition (6) implies condition (5) -/

/-- **Stacks 0ACK, condition (6) implies condition (5), for a Kolmogorov `|X_k|`.** If the
point space of the field fibre `X_k` is `T₀` and has Krull dimension zero, then it is discrete.

This is the corrected arrow of Lemma 0ACA from condition (3) to condition (2),
`AlgebraicGeometry.Space.discreteTopology_points_of_topologicalKrullDim_eq_zero`, applied to
`X_k` over `Spec(k)`: the field fibre is an algebraic space whose structure morphism is a base
change of `f`, hence locally of finite type by Tag 03XH, and whose base is presented by the
field `k` on the nose, so that lemma's presentation hypothesis holds by `rfl`.

**The `T₀` hypothesis is not in the source and cannot be dropped**, so the source's
unrestricted claim that conditions (5) and (6) are equivalent is false; see the implementation
notes of this file for the counterexample. With `T₀` discharged for a decent morphism this is
`AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints`. -/
@[stacks 0ACK "(6) implies (5), corrected: the source omits that |X_k| must be Kolmogorov"]
theorem isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (points B S hS (fieldFibre B S hS f p)))
    (h : IsZeroDimensionalFieldFibrePoints B S hS f p) :
    IsDiscreteFieldFibrePoints B S hS f p :=
  discreteTopology_points_of_topologicalKrullDim_eq_zero B S hS
    (isAlgebraicSpace_fieldFibre hX hY f p) p.contained p.toBase rfl
    (pullback.snd f (yonedaEquiv.symm p.value))
    (isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hft p) ht0 h

/-- **Stacks 0ACK, condition (6) implies condition (5), for a decent morphism.** If `f` is a
decent morphism locally of finite type and the point space of the field fibre `X_k` has Krull
dimension zero, then `|X_k|` is discrete.

The field fibre of a decent morphism is a decent algebraic space, and the point space of a
decent algebraic space is Kolmogorov by Stacks 03K3; that discharges the hypothesis of
`isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space`. Decency of `f` is
available in particular when `X` is a decent algebraic space, by the decent case of
Stacks 0ABX. -/
@[stacks 0ACK "decent morphism: condition (6) implies condition (5)"]
theorem isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (hd : IsDecent B S hS f)
    (p : FieldValuedPoint B S hS Y)
    (h : IsZeroDimensionalFieldFibrePoints B S hS f p) :
    IsDiscreteFieldFibrePoints B S hS f p :=
  isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space B S hS hX hY hft p
    (t0Space_points_fieldFibre_of_isDecent B S hS hX hY f hd p) h

/-! ### Condition (6) implies conditions (7) and (8) -/

/-- **Stacks 0ACK, condition (6) implies condition (7), for a Kolmogorov `|X_k|`.** If the
point space of the field fibre `X_k` is `T₀` and has Krull dimension zero, then `X_k` has
dimension zero as an algebraic space.

Condition (6) gives condition (5), and it also gives a point of `|X_k|`, since a space of Krull
dimension zero is nonempty; those are the two inputs of
`AlgebraicGeometry.Space.isZeroDimensionalFieldFibre_of_isDiscreteFieldFibrePoints`.

**The `T₀` hypothesis is not in the source and cannot be dropped**; see the implementation
notes of this file. It holds in particular when `f` is a decent morphism, by
`AlgebraicGeometry.Space.t0Space_points_fieldFibre_of_isDecent`. -/
@[stacks 0ACK "(6) implies (7), corrected: the source omits that |X_k| must be Kolmogorov"]
theorem isZeroDimensionalFieldFibre_of_isZeroDimensionalFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (points B S hS (fieldFibre B S hS f p)))
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsZeroDimensionalFieldFibrePoints B S hS f p) :
    IsZeroDimensionalFieldFibre B S hS f p hXk :=
  isZeroDimensionalFieldFibre_of_isDiscreteFieldFibrePoints B S hS hX hY hft p hXk
    (isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space B S hS hX hY
      hft p ht0 h)
    (nonempty_of_topologicalKrullDim_eq_zero _ h)

/-- **Stacks 0ACK, condition (6) implies condition (8), for a Kolmogorov `|X_k|`.** If the
point space of the field fibre `X_k` is `T₀` and has Krull dimension zero, then `f` is
quasi-finite at every point of `|X|` above the point represented by `p`.

Condition (6) gives condition (5), which is condition (8) by
`AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint`.

**The `T₀` hypothesis is not in the source and cannot be dropped**; see the implementation
notes of this file. It holds in particular when `f` is a decent morphism, by
`AlgebraicGeometry.Space.t0Space_points_fieldFibre_of_isDecent`. -/
@[stacks 0ACK "(6) implies (8), corrected: the source omits that |X_k| must be Kolmogorov"]
theorem isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (points B S hS (fieldFibre B S hS f p)))
    (h : IsZeroDimensionalFieldFibrePoints B S hS f p) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS f p :=
  (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft p).mp
    (isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space B S hS hX hY
      hft p ht0 h)

/-! ### Conditions (5), (6) and (7) are equivalent for a Kolmogorov `|X_k|` -/

/-- **Stacks 0ACK, conditions (5) and (6).** For a morphism locally of finite type and a
field-valued point of its target with nonempty field fibre whose point space is `T₀`, the point
space `|X_k|` is discrete exactly when it has Krull dimension zero.

The nonemptiness hypothesis is carried by the direction from condition (5) alone, and it cannot
be dropped there: `topologicalKrullDim` lands in `WithBot ℕ∞`, so the empty fibre is discrete
while having dimension `⊥` rather than `0`. The `T₀` hypothesis is carried by the other
direction, is not in the source, and cannot be dropped either; it holds in particular when `f`
is a decent morphism, by `AlgebraicGeometry.Space.t0Space_points_fieldFibre_of_isDecent`. -/
@[stacks 0ACK "conditions (5) and (6), corrected: |X_k| must be Kolmogorov"]
theorem isDiscreteFieldFibrePoints_iff_isZeroDimensionalFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (points B S hS (fieldFibre B S hS f p)))
    (hne : Nonempty (points B S hS (fieldFibre B S hS f p))) :
    IsDiscreteFieldFibrePoints B S hS f p ↔ IsZeroDimensionalFieldFibrePoints B S hS f p :=
  ⟨fun h ↦ isZeroDimensionalFieldFibrePoints_of_isDiscreteFieldFibrePoints B S hS f p h hne,
    isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space B S hS hX hY hft
      p ht0⟩

/-- **Stacks 0ACK, conditions (6) and (7) for a decent morphism.** For a decent morphism
locally of finite type and a field-valued point of its target, the point space `|X_k|` of the
field fibre has Krull dimension zero exactly when `X_k` has dimension zero as an algebraic
space.

Neither direction needs a nonemptiness hypothesis: each of the two conditions is an equation
`… = 0` in `WithBot ℕ∞` for a dimension whose value on the empty fibre is `⊥`, so each already
forces the fibre to have a point. The `T₀` hypothesis is carried by the direction out of
condition (6) alone, is not in the source, and cannot be dropped; it holds in particular when
`f` is a decent morphism, by
`AlgebraicGeometry.Space.t0Space_points_fieldFibre_of_isDecent`. -/
@[stacks 0ACK "conditions (6) and (7), corrected: |X_k| must be Kolmogorov"]
theorem isZeroDimensionalFieldFibre_iff_isZeroDimensionalFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (points B S hS (fieldFibre B S hS f p)))
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p)) :
    IsZeroDimensionalFieldFibre B S hS f p hXk ↔ IsZeroDimensionalFieldFibrePoints B S hS f p :=
  ⟨isZeroDimensionalFieldFibrePoints_of_isZeroDimensionalFieldFibre B S hS hX hY hft p hXk,
    isZeroDimensionalFieldFibre_of_isZeroDimensionalFieldFibrePoints B S hS hX hY hft p ht0 hXk⟩

/-! ### Condition (3) implies conditions (2) and (5), for a decent target -/

/-- **Stacks 0ACK, condition (3) implies condition (2), for a decent target and a Kolmogorov
`F`.** Let `f : X ⟶ Y` be a morphism of algebraic spaces locally of finite type, let `p` be a
field-valued point of a decent `Y`, and suppose the set-theoretic fibre `F = f^{-1}({y})` is
`T₀` and has Krull dimension zero. Then `F` is discrete.

Decency of `Y` supplies a field-valued point `q` representing the same point of `|Y|` whose
presenting morphism is a quasi-compact monomorphism, which is condition (4) of Stacks 03JV. For
that representative Lemma 0AC8 identifies `|X_q|` with `F` as topological spaces
(`AlgebraicGeometry.Space.homeomorphSetFibre`), and `F` is the same set for `q` as for `p` by
`AlgebraicGeometry.Space.setFibre_eq_of_class_eq`. The Krull dimension of a topological space is
a homeomorphism invariant, so condition (3) for `p` is condition (6) for `q`, and both the `T₀`
hypothesis and the resulting discreteness travel across that same homeomorphism.

**The `T₀` hypothesis on `F` is not in the source and cannot be dropped**, so the source's
claim that conditions (2) and (3) are equivalent for a decent target is false; see the
implementation notes of this file. It is weaker than decency of `f`, which gives it through the
homeomorphism above, and it holds in particular when `X` is a decent algebraic space — a
hypothesis the source itself makes, in its last clause — by
`AlgebraicGeometry.Space.t0Space_setFibre_of_isDecentSpace_source`. -/
@[stacks 0ACK "decent target: (3) implies (2), corrected: F must be Kolmogorov"]
theorem isDiscreteSetFibre_of_isZeroDimensionalSetFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (setFibre B S hS f p)) (hYdec : IsDecentSpace B S hS Y)
    (h : IsZeroDimensionalSetFibre B S hS f p) :
    IsDiscreteSetFibre B S hS f p := by
  obtain ⟨q, hqclass, hmono, hqc⟩ := hYdec (p.class B S hS Y)
  have hset : setFibre B S hS f q = setFibre B S hS f p :=
    setFibre_eq_of_class_eq B S hS f p q hqclass
  have hhomeo : points B S hS (fieldFibre B S hS f q) ≃ₜ setFibre B S hS f p :=
    (homeomorphSetFibre B S hS hX hY f q hmono hqc).trans (Homeomorph.setCongr hset)
  have ht0q : T0Space (points B S hS (fieldFibre B S hS f q)) := hhomeo.symm.t0Space
  have hdq : DiscreteTopology (points B S hS (fieldFibre B S hS f q)) :=
    isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibrePoints_of_t0Space B S hS hX hY hft
      q ht0q ((IsHomeomorph.topologicalKrullDim_eq _ hhomeo.isHomeomorph).trans h)
  exact hhomeo.discreteTopology

/-- **Stacks 0ACK, condition (3) implies condition (5), for a decent target and a Kolmogorov
`F`.** If the set-theoretic fibre `F` is `T₀` and has Krull dimension zero, `Y` is decent and
`f` is locally of finite type, then the point space `|X_k|` of the field fibre is discrete.

Condition (3) gives condition (2), and conditions (2) and (5) are equivalent for a decent
target by
`AlgebraicGeometry.Space.discreteTopology_setFibre_iff_discreteTopology_points_fieldFibre`. -/
@[stacks 0ACK "decent target: (3) implies (5), corrected: F must be Kolmogorov"]
theorem isDiscreteFieldFibrePoints_of_isZeroDimensionalSetFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (setFibre B S hS f p)) (hYdec : IsDecentSpace B S hS Y)
    (h : IsZeroDimensionalSetFibre B S hS f p) :
    IsDiscreteFieldFibrePoints B S hS f p :=
  (discreteTopology_setFibre_iff_discreteTopology_points_fieldFibre B S hS hX hY f p hft
    hYdec).mp (isDiscreteSetFibre_of_isZeroDimensionalSetFibre B S hS hX hY hft p ht0 hYdec h)

/-- **Stacks 0ACK, conditions (2) and (3) for a decent target and a Kolmogorov `F`.** For a
morphism locally of finite type into a decent algebraic space, and a field-valued point of the
target whose set-theoretic fibre `F` is nonempty and `T₀`, the fibre `F` is discrete exactly
when it has Krull dimension zero.

The nonemptiness hypothesis is carried by the direction from condition (2) alone, where it
cannot be dropped: the empty fibre is discrete while having Krull dimension `⊥`. The `T₀`
hypothesis is carried by the other direction, is not in the source, and cannot be dropped
either. -/
@[stacks 0ACK "decent target: conditions (2) and (3), corrected: F must be Kolmogorov"]
theorem isDiscreteSetFibre_iff_isZeroDimensionalSetFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0 : T0Space (setFibre B S hS f p)) (hYdec : IsDecentSpace B S hS Y)
    (hne : (setFibre B S hS f p).Nonempty) :
    IsDiscreteSetFibre B S hS f p ↔ IsZeroDimensionalSetFibre B S hS f p :=
  ⟨fun h ↦ isZeroDimensionalSetFibre_of_isDiscreteSetFibre B S hS f p h hne,
    isDiscreteSetFibre_of_isZeroDimensionalSetFibre B S hS hX hY hft p ht0 hYdec⟩

/-! ### The decency-free part of the source's decent-target clause -/

/-- **Stacks 0ACK, conditions (2), (5), (7) and (8) for a decent target.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces locally of finite type, let `Y` be a decent algebraic space and let
`p` be a field-valued point of `Y` with nonempty set-theoretic fibre `F`. Then the following are
equivalent: `F` is discrete; `|X_k|` is discrete; `dim(X_k) = 0`; and `f` is quasi-finite at
every point of `|X|` above the point `p` represents.

These are the four conditions of the source's decent-target clause whose equivalence holds at
the hypotheses the source states, with no decency hypothesis on `f`. The two it omits are the
Krull-dimension conditions (3) and (6), whose arrows to the others are false in that
generality. -/
@[stacks 0ACK "decent target: conditions (2), (5), (7) and (8)"]
theorem tfae_fibre_conditions_of_isDecentSpace_target
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) (hne : (setFibre B S hS f p).Nonempty) :
    [IsDiscreteSetFibre B S hS f p, IsDiscreteFieldFibrePoints B S hS f p,
      IsZeroDimensionalFieldFibre B S hS f p (isAlgebraicSpace_fieldFibre hX hY f p),
      IsQuasiFiniteAboveFieldValuedPoint B S hS f p].TFAE := by
  have hnef : Nonempty (points B S hS (fieldFibre B S hS f p)) :=
    (nonempty_points_fieldFibre_iff B S hS f p).mpr hne
  tfae_have 1 ↔ 2 :=
    discreteTopology_setFibre_iff_discreteTopology_points_fieldFibre B S hS hX hY f p hft hYdec
  tfae_have 2 ↔ 4 :=
    isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft p
  tfae_have 3 → 4 :=
    isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibre B S hS hX hY hft p _
  tfae_have 4 → 3 := fun h ↦
    isZeroDimensionalFieldFibre_of_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft p _ h hnef
  tfae_finish

/-! ### The six conditions of the source's decent-target clause -/

/-- **Stacks 0ACK, conditions (2), (3), (5), (6), (7) and (8) for a decent target and
Kolmogorov fibres.** Let `f : X ⟶ Y` be a morphism of algebraic spaces locally of finite type,
let `Y` be a decent algebraic space and let `p` be a field-valued point of `Y` whose
set-theoretic fibre `F` is nonempty, with `F` and `|X_k|` both `T₀`. Then the following are
equivalent: `F` is discrete; `dim(F) = 0`; `|X_k|` is discrete; `dim(|X_k|) = 0`;
`dim(X_k) = 0`; and `f` is quasi-finite at every point of `|X|` above the point `p` represents.

This is the source's clause "if `Y` is decent, then conditions (2) and (3) are equivalent to
each other and to conditions (5), (6), (7) and (8)", with the two Kolmogorov hypotheses that
the clause needs and does not state, and with the nonemptiness that the `= 0` form of the two
dimension conditions needs; see the implementation notes of this file. The `T₀` hypothesis on
`F` is used only by the arrow out of condition (3) and the one on `|X_k|` only by the arrow out
of condition (6), which are exactly the two arrows the counterexample kills. Both are weaker
than decency of `f`, which gives them by
`AlgebraicGeometry.Space.t0Space_points_fieldFibre_of_isDecent` and the homeomorphism of
Lemma 0AC8. -/
@[stacks 0ACK "decent target: conditions (2), (3), (5), (6), (7) and (8), Kolmogorov fibres"]
theorem tfae_fibre_conditions
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (ht0F : T0Space (setFibre B S hS f p))
    (ht0k : T0Space (points B S hS (fieldFibre B S hS f p)))
    (hYdec : IsDecentSpace B S hS Y) (hne : (setFibre B S hS f p).Nonempty) :
    [IsDiscreteSetFibre B S hS f p, IsZeroDimensionalSetFibre B S hS f p,
      IsDiscreteFieldFibrePoints B S hS f p, IsZeroDimensionalFieldFibrePoints B S hS f p,
      IsZeroDimensionalFieldFibre B S hS f p (isAlgebraicSpace_fieldFibre hX hY f p),
      IsQuasiFiniteAboveFieldValuedPoint B S hS f p].TFAE := by
  have hnef : Nonempty (points B S hS (fieldFibre B S hS f p)) :=
    (nonempty_points_fieldFibre_iff B S hS f p).mpr hne
  tfae_have 1 ↔ 2 :=
    isDiscreteSetFibre_iff_isZeroDimensionalSetFibre B S hS hX hY hft p ht0F hYdec hne
  tfae_have 1 ↔ 3 :=
    discreteTopology_setFibre_iff_discreteTopology_points_fieldFibre B S hS hX hY f p hft hYdec
  tfae_have 3 ↔ 4 :=
    isDiscreteFieldFibrePoints_iff_isZeroDimensionalFieldFibrePoints B S hS hX hY hft p ht0k
      hnef
  tfae_have 5 ↔ 4 :=
    isZeroDimensionalFieldFibre_iff_isZeroDimensionalFieldFibrePoints B S hS hX hY hft p ht0k _
  tfae_have 3 ↔ 6 :=
    isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft p
  tfae_finish

/-! ### Condition (1) implies the other conditions, for decent spaces -/

/-- **Stacks 0ACK, condition (1) implies all the other conditions, for decent spaces.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces locally of finite type with `X` and `Y` both
decent, and let `p` be a field-valued point of `Y` whose set-theoretic fibre `F` is finite and
nonempty. Then `|X_k|` is finite, `F` is discrete, `dim(F) = 0`, `|X_k|` is discrete,
`dim(|X_k|) = 0`, `dim(X_k) = 0`, and `f` is quasi-finite at every point of `|X|` above the
point `p` represents — conditions (4), (2), (3), (5), (6), (7) and (8) of the tag.

Condition (4) is
`AlgebraicGeometry.Space.finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent`. A
morphism out of a decent algebraic space is a decent morphism by the decent case of Stacks
0ABX, so condition (4) gives condition (5) by
`AlgebraicGeometry.Space.discreteTopology_points_fieldFibre_of_finite_of_isDecent`, and the
remaining five conditions are condition (5) read through
`AlgebraicGeometry.Space.tfae_fibre_conditions`.

The nonemptiness hypothesis is the one the two Krull-dimension conditions and condition (7)
need: the empty fibre is finite and discrete while every `… = 0` among the conditions reads
`⊥ = 0` on it. It cannot be dropped, by
`AlgebraicGeometry.Space.not_forall_isZeroDimensionalSetFibre_of_finite_setFibre`, which
refutes this clause in the form the source states it, with both `X` and `Y` decent and no
hypothesis on the fibre. -/
@[stacks 0ACK "decent spaces: condition (1) implies the other seven conditions"]
theorem fibre_conditions_of_finite_setFibre_of_isDecent
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (hne : (setFibre B S hS f p).Nonempty) (hfinite : (setFibre B S hS f p).Finite) :
    (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite ∧
      IsDiscreteSetFibre B S hS f p ∧ IsZeroDimensionalSetFibre B S hS f p ∧
      IsDiscreteFieldFibrePoints B S hS f p ∧
      IsZeroDimensionalFieldFibrePoints B S hS f p ∧
      IsZeroDimensionalFieldFibre B S hS f p (isAlgebraicSpace_fieldFibre hX hY f p) ∧
      IsQuasiFiniteAboveFieldValuedPoint B S hS f p := by
  have hd : IsDecent B S hS f := isDecent_of_isDecentSpace_source B S hS hX hY f hXdec
  have h4 : (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite :=
    finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent B S hS hX hY f p hft hXdec
      hYdec hfinite
  have h5 : IsDiscreteFieldFibrePoints B S hS f p :=
    discreteTopology_points_fieldFibre_of_finite_of_isDecent B S hS hX hY f p hft hd h4
  have htfae := tfae_fibre_conditions B S hS hX hY hft p
    (t0Space_setFibre_of_isDecentSpace_source B S hS hX f hXdec p)
    (t0Space_points_fieldFibre_of_isDecent B S hS hX hY f hd p) hYdec hne
  exact ⟨h4, (htfae.out 3 1).mp h5, (htfae.out 3 2).mp h5, h5, (htfae.out 3 4).mp h5,
    (htfae.out 3 5).mp h5, (htfae.out 3 6).mp h5⟩

end AlgebraicGeometry.Space

end
