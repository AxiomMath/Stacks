module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableExample
public import StacksFrontier.RingTheory.Rig.AdicBasic

/-!
# The chart rings of the non-algebraizable example are charts of `Spec(A/t^nA)`

For `A = k[x,y][[t]]` the ring `A_r/t^nA_r` of
`Stacks.Algebraization.NonAlgebraizableExample.chartRing` is presented as the quotient of `A_r` by
the span of `(algebraMap t) ^ n`. This file identifies that ideal with the extension of
`I ^ n = (t^n)` along `A → A_r` and deduces from `Rig.isLocalization_away_quotient` that the chart
ring is the localization of the level ring `A/t^nA` away from the image of `r`. So the chart rings
are the rings of sections of `O` on the basic opens `D(x)`, `D(y)` and `D(xy)` of `Spec(A/t^nA)`,
which is the cover the two-chart gluing of [Stacks, Tag 0EHE] is carried out over.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.levelToChart` — the restriction map
  `A/t^nA → A_r/t^nA_r`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.span_algebraMap_tVar_pow` — the ideal cutting out
  the chart ring is the extension of `(t^n)`.
* `Stacks.Algebraization.NonAlgebraizableExample.isLocalization_away_levelToChart` — the chart
  ring is the localization of `A/t^nA` away from the image of `r`.

## Implementation notes

`Rig.isLocalization_away_quotient` is stated for `A_r ⧸ I.map (algebraMap A A_r)` with the algebra
structure over `A ⧸ I` supplied by `letI`. The transport to `chartRing` is an `AlgEquiv` over the
level ring built from `Ideal.quotEquivOfEq`; its compatibility with the two algebra maps is checked
on a representative, both maps being `Ideal.quotientMap` of the same `algebraMap`. No second
localization statement is proved: the only new input is the equality of ideals.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- The ideal cutting out the chart ring `A_r/t^nA_r` is the extension of `I^n = (t^n)`. -/
public lemma span_algebraMap_tVar_pow (r : AmbientRing k) (n : ℕ) :
    Ideal.span {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n} =
      ((idealT k) ^ n).map (algebraMap (AmbientRing k) (Localization.Away r)) := by
  rw [idealT, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]

/-- The ring map `A/t^nA → A_r/t^nA_r` restricting a function to the chart `D(r)`. -/
public def levelToChart (r : AmbientRing k) (n : ℕ) : levelRing k n →+* chartRing k r n :=
  Ideal.quotientMap _ (algebraMap (AmbientRing k) (Localization.Away r)) fun x hx => by
    rw [Ideal.mem_comap, span_algebraMap_tVar_pow]
    exact Ideal.mem_map_of_mem _ hx

/-- `levelToChart` sends the class of `x ∈ A` to the class of its image in `A_r`. -/
@[simp]
public lemma levelToChart_mk (r : AmbientRing k) (n : ℕ) (x : AmbientRing k) :
    levelToChart k r n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (AmbientRing k) (Localization.Away r) x) :=
  Ideal.quotientMap_mk

/-- **Stacks Project, Tag 0EHE (the chart rings).** The chart ring `A_r/t^nA_r` is the
localization of the level ring `A/t^nA` away from the image of `r`, so it is the ring of sections
of `O` on the basic open `D(r)` of `Spec(A/t^nA)`. -/
@[stacks 0EHE "A_r/t^n A_r is the localization of A/t^n A away from the image of r"]
public theorem isLocalization_away_levelToChart (r : AmbientRing k) (n : ℕ) :
    letI : Algebra (levelRing k n) (chartRing k r n) := (levelToChart k r n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk ((idealT k) ^ n) r) (chartRing k r n) := by
  let L := Localization.Away r
  let Iₗ := ((idealT k) ^ n).map (algebraMap (AmbientRing k) L)
  let i : levelRing k n →+* L ⧸ Iₗ :=
    Ideal.quotientMap Iₗ (algebraMap (AmbientRing k) L) fun _ hx => Ideal.mem_map_of_mem _ hx
  let : Algebra (levelRing k n) (L ⧸ Iₗ) := i.toAlgebra
  let : Algebra (levelRing k n) (chartRing k r n) := (levelToChart k r n).toAlgebra
  have : IsLocalization.Away (Ideal.Quotient.mk ((idealT k) ^ n) r) (L ⧸ Iₗ) :=
    Rig.isLocalization_away_quotient ((idealT k) ^ n) r
  refine IsLocalization.isLocalization_of_algEquiv (R := levelRing k n) _
    (AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (span_algebraMap_tVar_pow k r n).symm)
      fun z => ?_)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  show Ideal.quotEquivOfEq (span_algebraMap_tVar_pow k r n).symm
      (i (Ideal.Quotient.mk _ x)) = levelToChart k r n (Ideal.Quotient.mk _ x)
  rw [levelToChart_mk]
  show Ideal.quotEquivOfEq (span_algebraMap_tVar_pow k r n).symm
      (Ideal.Quotient.mk _ (algebraMap (AmbientRing k) L x)) = _
  exact Ideal.quotEquivOfEq_mk _ _

end Stacks.Algebraization.NonAlgebraizableExample

end
