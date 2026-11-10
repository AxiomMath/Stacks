module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers

/-!
# Reading depth one off the strict `(1, 1 + d)`-inequalities

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`, and let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`
satisfying the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3]. At a point `y ∈ U ∩ Y`
whose distance to `Z` is exactly one, and at a prime `𝔭 ⊆ 𝒪_{X,y}^∧` not containing
`I𝒪_{X,y}^∧` whose quotient has dimension at most `d`, those inequalities force

`depth((ℱ_y^∧)_𝔭) ≥ 1`.

With `α = depth((ℱ_y^∧)_𝔭)`, `β = dim(𝒪_{X,y}^∧/𝔭)` and `γ = δ^Y_Z(y) = 1`, the strict
inequalities say `α + γ > 1` or `α + β + γ > 1 + d`. Were `α = 0` the first alternative would
read `1 > 1` and the second `β + 1 > 1 + d`, contradicting `β ≤ d`. That is the whole argument,
and it is the closing sentence — "now we read off the conclusion from the inequalities given to
us" — of the source's proof of [Stacks, Tag 0EJ5]; the same arithmetic, contrapositively, is
the step "the assumption implies that `dim(𝒪_{W, y}) > d`" in the proofs of
[Stacks, Tag 0EJ6] and [Stacks, Tag 0EJ8].

## Main results

* `Stacks.Algebraization.one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities` — the
  depth-one bound.
* `Stacks.Algebraization.lt_krullDimToEInt_of_completedStalkDepth_eq_zero` — its contrapositive:
  at a prime where the formal stalk has depth zero the quotient has dimension more than `d`.

## Implementation notes

### No `@[stacks 0EJ5]`, `@[stacks 0EJ6]` or `@[stacks 0EJ8]` attribute, and none may be placed
here

What is proved here is arithmetic in the extended integers at one point `y` of `U ∩ Y` and one
prime `𝔭` of `𝒪_{X,y}^∧`, both *given*. Each of the three tags above needs, in addition, the
geometry that produces that point and that prime from a hypothesis about the closed fibre:

* [Stacks, Tag 0EJ5] starts from a point `x` of `U` whose closure `W` meets `Y` in components
  lying on both sides of `Z`, decomposes `W ∩ Y` into irreducible components, observes that
  removing the intersection of the two groups disconnects it, and applies
  [Stacks, Tag 0EG5] — `Stacks.Algebraization.eq_empty_or_isConnected_zeroLocus_sdiff` — to
  `A/𝔭_x` to obtain a point `z` of `W ∩ Z` with `dim(𝒪_{W, z}) ≤ d + 1`; it then takes an
  immediate specialization `y ⤳ z` with `y ∈ W ∩ Y`, `y ∉ Z`, which is where
  [Stacks, Tag 02IM] enters, and finally identifies `depth(ℱ_x)` with `depth((ℱ_y^∧)_{𝔭'})`
  for `𝔭'` a minimal prime over `𝔭_x 𝒪_{X,y}^∧`, by [Stacks, Tag 0338] and
  [Stacks, Tag 0EHW].
* [Stacks, Tag 0EJ6] and [Stacks, Tag 0EJ8] consume [Stacks, Tag 0EJ5] itself.

None of that is here. Attaching any of those three tags to the statements below would register
them on a hypothesis-laden special case — the point, the prime, the distance and the dimension
bound all supplied — rather than on their own content, so no attribute is placed. See the
report accompanying this file for the exact statements the chain still lacks.

### Why the hypothesis is `δ^Y_Z(y) = 1` and not `1 ≤ δ^Y_Z(y)`

The distance is at least one at every point of `U ∩ Y`
(`Stacks.Algebraization.AlgebraizationSituation.one_le_distanceToZ`), but a larger value does
not suffice: at `δ^Y_Z(y) = 2` the first alternative `α + γ > 1` holds with `α = 0`. The
source's `y` is an immediate specialization of a point of `Y ∖ Z`, for which it records
`δ^Y_Z(y) = 1` on the nose, and that is the hypothesis taken here.

### The extended integers

Depth takes values in `ℕ∞` and Krull dimension in `WithBot ℕ∞`, and both are placed in `EInt`
by `Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt` before being
compared with the integer bounds, exactly as in the definition of the inequalities. The
argument is run as a refutation of `α = 0` rather than as a cancellation, so no hypothesis
`β ≠ ⊥` is needed: the only facts used are that `((0 : ℤ) : EInt)` is a left unit for addition
and that addition is monotone.

## References

* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5), whose closing
  arithmetic this is.
* [Stacks Project, Tag 0EJ6](https://stacks.math.columbia.edu/tag/0EJ6)
* [Stacks Project, Tag 0EJ8](https://stacks.math.columbia.edu/tag/0EJ8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- The image in the extended integers of the extended natural number zero. -/
private theorem enatToEInt_zero : enatToEInt (0 : ℕ∞) = ((0 : ℤ) : EInt) := rfl

/-- `((0 : ℤ) : EInt)` is a left unit for addition. -/
private theorem intCast_zero_add (x : EInt) : ((0 : ℤ) : EInt) + x = x := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe x =>
    induction x using WithTop.recTopCoe with
    | top => rfl
    | coe x =>
      change ((((0 : ℤ) + x : ℤ) : WithTop ℤ) : EInt) = ((x : WithTop ℤ) : EInt)
      rw [zero_add]

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **The depth-one bound read off the strict `(1, 1 + d)`-inequalities.** Let `(ℱ_n)` be an
object of `Coh(U, I𝒪_U)` satisfying the strict `(1, 1 + d)`-inequalities of
[Stacks, Tag 0EJ3]. Let `y ∈ U ∩ Y` be at distance exactly one from `Z` and let
`𝔭 ⊆ 𝒪_{X,y}^∧` be a prime not containing `I𝒪_{X,y}^∧` with `dim(𝒪_{X,y}^∧/𝔭) ≤ d`. Then
`depth((ℱ_y^∧)_𝔭) ≥ 1`.

Of the two alternatives the inequalities offer, the first reads `depth + 1 > 1` and the second
`depth + dim + 1 > 1 + d`; with `dim ≤ d` each forces the depth to be nonzero. -/
public theorem one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities
    (d : ℤ) (hstrict : SatisfiesStrictDepthInequalities S F 1 (1 + d))
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (hdist : S.distanceToZ z = 1)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal)
    (hdim : krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) ≤
      ((d : ℤ) : EInt)) :
    1 ≤ completedStalkDepth (idealOnOpen S) F y p := by
  rw [Order.one_le_iff_ne_zero]
  intro hzero
  have hγ : enatToEInt (S.distanceToZ z) = ((1 : ℤ) : EInt) :=
    (congrArg enatToEInt hdist).trans rfl
  have hα : enatToEInt (completedStalkDepth (idealOnOpen S) F y p) = ((0 : ℤ) : EInt) := by
    rw [hzero, enatToEInt_zero]
  have hda : depthAddDistance S F y z p = ((1 : ℤ) : EInt) := by
    change enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
      enatToEInt (S.distanceToZ z) = ((1 : ℤ) : EInt)
    rw [hα, hγ, intCast_zero_add]
  have hdd : depthAddDimAddDistance S F y z p ≤ ((1 + d : ℤ) : EInt) := by
    change enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
        krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
        enatToEInt (S.distanceToZ z) ≤ ((1 + d : ℤ) : EInt)
    rw [hα, hγ, intCast_zero_add, Stacks.Chow.coe_add_coe_eq_coe_add, add_comm ((1 : ℤ) : EInt)]
    exact add_le_add hdim le_rfl
  rcases hstrict y z hyz p hp with hcase | hcase
  · rw [hda] at hcase
    exact lt_irrefl _ hcase
  · exact lt_irrefl _ (hcase.trans_le hdd)

/-- **The contrapositive of the depth-one bound.** In the situation of
`Stacks.Algebraization.one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities`, if the
formal stalk has depth zero at `𝔭` then `dim(𝒪_{X,y}^∧/𝔭) > d`.

This is the shape in which the step is used in the proofs of [Stacks, Tag 0EJ6] and
[Stacks, Tag 0EJ8], where `𝔭` comes from an associated point of `ℱ` and the depth is therefore
zero. -/
public theorem lt_krullDimToEInt_of_completedStalkDepth_eq_zero
    (d : ℤ) (hstrict : SatisfiesStrictDepthInequalities S F 1 (1 + d))
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (hdist : S.distanceToZ z = 1)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal)
    (hzero : completedStalkDepth (idealOnOpen S) F y p = 0) :
    ((d : ℤ) : EInt) <
      krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) := by
  refine not_le.mp fun hdim => ?_
  simpa [hzero] using one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities S F d
    hstrict y z hyz hdist p hp hdim

end Stacks.Algebraization

end
