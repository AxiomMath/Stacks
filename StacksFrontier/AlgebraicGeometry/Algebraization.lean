module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.RingTheory.AdicCompletion.Basic

/-!
# Adic thickenings and adic base change

Let `A` be a ring and `I ⊆ A` an ideal. The positive-order infinitesimal thickenings
attached to `I` are the affine schemes `Spec (A / I ^ (n + 1))`, which sit inside one
another along the canonical surjections `A / I ^ (n + 2) → A / I ^ (n + 1)` and map to
`Spec A`. Base changing a scheme over `Spec A` along these thickenings produces the
system of adic reductions of that scheme, and base changing a morphism over `Spec A`
produces a compatible system of morphisms between the reductions.

Positive powers are indexed by natural numbers starting with `I ^ (n + 1)`, and
compatibility is expressed with the canonical maps from the reduction modulo `I ^ (n + 1)`
to that modulo `I ^ (n + 2)`.

## Main definitions

* `AlgebraicGeometry.adicThickening`: `Spec (A / I ^ (n + 1))`, with structure morphism
  `AlgebraicGeometry.adicThickeningι` to `Spec A` and the closed immersion
  `AlgebraicGeometry.adicThickeningSucc` into the next thickening.
* `AlgebraicGeometry.adicBaseChange`: the base change of a scheme over `Spec A` to an
  adic thickening, with transition map `AlgebraicGeometry.adicBaseChangeSucc`.
* `AlgebraicGeometry.adicBaseChangeMap`: the base change of a morphism over `Spec A`.

## Main results

* `AlgebraicGeometry.adicThickeningSucc_ι`: the transition maps between thickenings are
  morphisms over `Spec A`.

## References

* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The `n`-th positive-order infinitesimal thickening associated to `I`; its ring is
`A / I ^ (n + 1)`. -/
public abbrev adicThickening (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    Scheme.{u} := Spec (.of (A ⧸ I ^ (n + 1)))

/-- The structure morphism from an adic thickening to `Spec A`. -/
public def adicThickeningι (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    adicThickening A I n ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

/-- The canonical closed immersion from the `n`-th thickening into the next thickening. -/
public def adicThickeningSucc (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    adicThickening A I n ⟶ adicThickening A I (n + 1) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- The transition maps between consecutive adic thickenings are morphisms over
`Spec A`. -/
@[reassoc]
public lemma adicThickeningSucc_ι (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    adicThickeningSucc A I n ≫ adicThickeningι A I (n + 1) =
      adicThickeningι A I n := by
  rw [adicThickeningSucc, adicThickeningι, adicThickeningι, ← Spec.map_comp]
  congr 2

/-- Base change of a scheme over `Spec A` to the `n`-th adic thickening. -/
public abbrev adicBaseChange (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (n : ℕ) : Scheme.{u} :=
  pullback f (adicThickeningι A I n)

/-- The canonical map between two consecutive adic base changes. -/
public def adicBaseChangeSucc (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (n : ℕ) :
    adicBaseChange A I f n ⟶ adicBaseChange A I f (n + 1) :=
  pullback.lift (pullback.fst f (adicThickeningι A I n))
    (pullback.snd f (adicThickeningι A I n) ≫ adicThickeningSucc A I n) (by
      rw [Category.assoc, adicThickeningSucc_ι, pullback.condition])

/-- Base change of a morphism over `Spec A` to an adic thickening. -/
public def adicBaseChangeMap (A : Type u) [CommRing A] (I : Ideal A)
    {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of A)} {fY : Y ⟶ Spec (.of A)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ) :
    adicBaseChange A I fX n ⟶ adicBaseChange A I fY n :=
  pullback.lift (pullback.fst fX (adicThickeningι A I n) ≫ g)
    (pullback.snd fX (adicThickeningι A I n)) (by
      rw [Category.assoc, hg, pullback.condition])

end AlgebraicGeometry

end
