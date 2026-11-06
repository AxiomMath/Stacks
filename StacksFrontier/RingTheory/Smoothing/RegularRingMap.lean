module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Regular ring maps of Noetherian rings

A ring map `R → Λ` is *regular* when it is flat and its fibres are geometrically regular: for
every prime `p` of `R` and every finite extension `k'` of the residue field `κ(p)`, the ring
`k' ⊗_R Λ` is Noetherian and regular. This file records that condition and the standing
situation of Stacks 16.8.1, a regular ring map between Noetherian rings.

## Main definitions

* `Stacks.Smoothing.IsRegularRingMap`: the regularity condition on a ring map.
* `Stacks.Smoothing.RegularRingMapSituation`: the standing data of Stacks 16.8.1, a regular
  ring map of Noetherian rings.

## Implementation notes

Geometric regularity is stated in the algebraic form the source uses: a condition on the base
changes of `Λ` to the finite extensions of the residue fields of `R`. The residue field is
`Ideal.ResidueField`, and the `R`-algebra structure on `k'` is the composite
`R → κ(p) → k'`.

## References

* [Stacks Project, Tag 07F2](https://stacks.math.columbia.edu/tag/07F2)
-/

open scoped TensorProduct

@[expose] public section

namespace Stacks.Smoothing

universe u v

/-- A flat ring map with geometrically regular Noetherian fibres. -/
def IsRegularRingMap (R : Type u) (Λ : Type v)
    [CommRing R] [CommRing Λ] [Algebra R Λ] : Prop :=
  Module.Flat R Λ ∧
    ∀ (p : Ideal R) [p.IsPrime]
      (k' : Type u) [Field k'] [Algebra p.ResidueField k']
      [Module.Finite p.ResidueField k'],
      letI : Algebra R k' :=
        ((algebraMap p.ResidueField k').comp
          (algebraMap R p.ResidueField)).toAlgebra
      IsNoetherianRing (k' ⊗[R] Λ) ∧ IsRegularRing (k' ⊗[R] Λ)

/-- The standing data of Stacks 16.8.1: a regular ring map between Noetherian rings. -/
-- Stacks 07F2 is a Situation: its content is the conjunction of its standing hypotheses, and
-- the faithful formalization of that content is exactly a structure bundling them, which is
-- what this is. Its fields are the source's data and nothing more: two Noetherian commutative
-- rings, the algebra map, and its regularity. No extra hypothesis, so the tag is not weakened.
@[stacks 07F2]
structure RegularRingMapSituation where
  /-- The base ring. -/
  R : Type u
  /-- The target ring. -/
  Λ : Type v
  /-- The commutative-ring structure on the base. -/
  [commRingR : CommRing R]
  /-- The commutative-ring structure on the target. -/
  [commRingΛ : CommRing Λ]
  /-- The ring map `R → Λ`. -/
  [algebra : Algebra R Λ]
  /-- The base ring is Noetherian. -/
  [noetherianR : IsNoetherianRing R]
  /-- The target ring is Noetherian. -/
  [noetherianΛ : IsNoetherianRing Λ]
  /-- The ring map is regular. -/
  regular : IsRegularRingMap R Λ

end Stacks.Smoothing

end
