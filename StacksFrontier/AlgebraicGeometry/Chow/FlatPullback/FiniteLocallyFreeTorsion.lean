module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFreeFibreDegree
public import
  StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.RationalEquivalenceUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# A cycle killed by flat pullback along a finite locally free morphism has torsion class

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
schemes locally of finite type over `S` and let `π : X ⟶ Y` be finite locally free of degree `d`.
If the flat pullback `π^* z` of a `k`-cycle `z` on `Y` is rationally equivalent to zero, then the
class of `z` in `CH_k(Y)` is killed by `d`.

This is the whole use the proof of Stacks 0FH8 makes of Stacks 02RH: pushing the rational
equivalence forward along `π`, which is proper, leaves a rational equivalence by Stacks 02S2, and
the pushforward of the pullback is `d z` by Stacks 02RH.

## Main results

* `Stacks.Chow.nsmul_cycleClass_eq_zero_of_isRationallyEquivalentToZero_flatPullback` — the class
  of `z` in `CH_k(Y)` is killed by `d` when `π^* z` is rationally equivalent to zero.

## Implementation notes

Flat pullback along `π` raises the delta-dimension index by the relative dimension `0` of `π`, so
the pullback of a `k`-cycle is a `k + 0`-cycle and the pushforward of that is a `k + 0`-cycle on
`Y`. The index `k + 0` is not syntactically `k`, so the statement of Stacks 02RH transports the
composite along the equality `k + 0 = k`; `Stacks.Chow.mem_rationalEquivalences_of_degree_eq`
transports membership in the subgroup of cycles rationally equivalent to zero the same way, which
is all that is needed to read the two off each other.

## References

* [Stacks Project, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0FH8](https://stacks.math.columbia.edu/tag/0FH8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Membership in the subgroup of cycles rationally equivalent to zero transports along an
equality of delta-dimension indices. -/
theorem mem_rationalEquivalences_of_degree_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {i j : ℤ} (h : i = j) (z : CycleGroup C p i)
    (hz : z ∈ rationalEquivalences C p i) :
    (h ▸ z : CycleGroup C p j) ∈ rationalEquivalences C p j := by
  subst h
  exact hz

/-- **A cycle whose flat pullback along a finite locally free morphism of degree `d` is rationally
equivalent to zero has a class killed by `d`.**

Proper pushforward along `π` carries the rational equivalence to a rational equivalence by
Stacks 02S2, and it carries `π^* z` to `d z` by Stacks 02RH; so `d z` is rationally equivalent to
zero, which is exactly `d` killing the class of `z`. -/
theorem nsmul_cycleClass_eq_zero_of_isRationallyEquivalentToZero_flatPullback
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d] (hbase : π ≫ sY = sX) (k : ℤ)
    (z : CycleGroup C sY k)
    (hz : letI : LocallyOfFiniteType π :=
            Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank π d
          letI : Flat π := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank π d
          IsRationallyEquivalentToZero C sX (k + ((0 : ℕ) : ℤ))
            (flatPullback C sX sY π hbase 0
              (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) k z)) :
    d • (QuotientAddGroup.mk' (rationalEquivalences C sY k) z) = 0 := by
  have hlft : LocallyOfFiniteType π :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank π d
  have hflat : Flat π := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank π d
  have hproper : IsProper π := Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank π d
  have hcast : k + ((0 : ℕ) : ℤ) = k := by simp
  have hre : RationallyEquivalent C sX (k + ((0 : ℕ) : ℤ))
      (flatPullback C sX sY π hbase 0
        (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) k z) 0 := by
    have h : flatPullback C sX sY π hbase 0
          (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) k z - 0 ∈
        rationalEquivalences C sX (k + ((0 : ℕ) : ℤ)) := by
      rw [sub_zero]
      exact hz
    exact h
  have hpush := properPushforward_rationallyEquivalent_of_isProper C sX sY π hbase
    (k + ((0 : ℕ) : ℤ)) hre
  have hmem0 : properPushforward C sX sY π hbase (k + ((0 : ℕ) : ℤ))
      (flatPullback C sX sY π hbase 0
        (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) k z) ∈
      rationalEquivalences C sY (k + ((0 : ℕ) : ℤ)) := by
    have h : properPushforward C sX sY π hbase (k + ((0 : ℕ) : ℤ))
          (flatPullback C sX sY π hbase 0
            (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) k z) -
          properPushforward C sX sY π hbase (k + ((0 : ℕ) : ℤ)) 0 ∈
        rationalEquivalences C sY (k + ((0 : ℕ) : ℤ)) := hpush
    rw [properPushforward_zero, sub_zero] at h
    exact h
  have hmem := mem_rationalEquivalences_of_degree_eq C sY hcast
    (properPushforward C sX sY π hbase (k + ((0 : ℕ) : ℤ))
      (flatPullback C sX sY π hbase 0
        (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) k z)) hmem0
  rw [properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank C sX sY π d hbase k hcast z]
    at hmem
  have hzero : (QuotientAddGroup.mk' (rationalEquivalences C sY k) ((d : ℤ) • z)) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hmem
  rw [map_zsmul] at hzero
  rwa [← natCast_zsmul]

end Stacks.Chow

end
