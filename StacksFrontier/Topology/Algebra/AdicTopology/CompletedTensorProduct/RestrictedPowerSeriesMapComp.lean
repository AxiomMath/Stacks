module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RestrictedPowerSeries.IdealTransport
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeriesMap

/-!
# Coefficient reduction of restricted power series is transitive

For a tower `A → B → C` of commutative rings and an ideal `I` of `A`, reducing coefficients from
`A` to `B` and then from `B` to `C` is reducing them from `A` to `C`.  The two sides do not have
the same type on the nose: the composite lands in the restricted power series ring for the
two-step ideal `(I · B) · C` and the direct map in the one for `I · C`, and those ideals are
equal but not syntactically so.  `RestrictedPowerSeries.congrEquiv` reconciles them, and the
statement here is that it does so compatibly with the two maps.

This is the naturality that makes a square of restricted power series rings out of a square of
coefficient rings.  The fourth paragraph of the proof of Stacks 0GGR needs exactly that: the
square
```
A{σ} ⟶ B{σ}
 ↓       ↓
A_{\{f\}}{σ} ⟶ B_{\{f\}}{σ}
```
has both legs of the form "reduce coefficients twice", along `A → B → B_{\{f\}}` and along
`A → A_{\{f\}} → B_{\{f\}}`, and commutes because both composites are the single reduction
`A → B_{\{f\}}`.

## Main results

* `TopologicalRing.congrEquiv_restrictedPowerSeriesMap_comp`: the composite of the two
  coefficient reductions of a tower is the reduction of the composite.
* `TopologicalRing.restrictedPowerSeriesMap_square`: hence two towers with the same composite
  give the same map of restricted power series rings.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
-/

@[expose] public section

namespace TopologicalRing

section

universe u v

open RestrictedPowerSeries

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- The two-step extension of an ideal along a tower is its one-step extension. -/
public theorem map_algebraMap_tower_eq [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (I : Ideal A) :
    (I.map (algebraMap A B)).map (algebraMap B C) = I.map (algebraMap A C) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C]

/-- **Coefficient reduction of restricted power series is transitive.**  For a tower
`A → B → C` and an ideal `I` of `A`, reducing coefficients from `A` to `B` and then from `B` to
`C` is reducing them from `A` to `C`, once the two spellings of the coefficient ideal of the
target are identified by `RestrictedPowerSeries.congrEquiv`. -/
public theorem congrEquiv_restrictedPowerSeriesMap_comp [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] (I : Ideal A) (σ : Type v) :
    (congrEquiv (map_algebraMap_tower_eq (A := A) (B := B) (C := C) I) σ).toRingHom.comp
        ((restrictedPowerSeriesMap (B := C) (I.map (algebraMap A B)) σ).comp
          (restrictedPowerSeriesMap (B := B) I σ)) =
      restrictedPowerSeriesMap (B := C) I σ := by
  refine RingHom.ext fun x => RestrictedPowerSeries.idealSystem_ext fun n => ?_
  change MvPolynomial.map _ (MvPolynomial.map _ (MvPolynomial.map _
    (coefficientProjection I σ n x))) = MvPolynomial.map _ (coefficientProjection I σ n x)
  have hlevel :
      (((Ideal.quotEquivOfEq (congrArg (· ^ n)
              (map_algebraMap_tower_eq (A := A) (B := B) (C := C) I)) :
            C ⧸ ((I.map (algebraMap A B)).map (algebraMap B C)) ^ n ≃+*
              C ⧸ (I.map (algebraMap A C)) ^ n) :
          C ⧸ ((I.map (algebraMap A B)).map (algebraMap B C)) ^ n →+*
            C ⧸ (I.map (algebraMap A C)) ^ n).comp
          (coefficientQuotientMap (B := C) (I.map (algebraMap A B)) n)).comp
        (coefficientQuotientMap (B := B) I n) =
      coefficientQuotientMap (B := C) I n :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
      change Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n)
          (algebraMap B C (algebraMap A B a)) =
        Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (algebraMap A C a)
      rw [IsScalarTower.algebraMap_apply A B C])
  rw [MvPolynomial.map_map, MvPolynomial.map_map, hlevel]

/-- **Two towers with the same composite give the same map of restricted power series
rings.**  For towers `A → B → C` and `A → B' → C` whose composites `A → C` agree, the two
twice-reduced maps `A{σ} → C{σ}` agree after the coefficient ideals of their targets are
identified. -/
public theorem restrictedPowerSeriesMap_square {B' : Type u} [CommRing B']
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra A B'] [Algebra B' C] [IsScalarTower A B' C] (I : Ideal A) (σ : Type v) :
    (congrEquiv (map_algebraMap_tower_eq (A := A) (B := B) (C := C) I) σ).toRingHom.comp
        ((restrictedPowerSeriesMap (B := C) (I.map (algebraMap A B)) σ).comp
          (restrictedPowerSeriesMap (B := B) I σ)) =
      (congrEquiv (map_algebraMap_tower_eq (A := A) (B := B') (C := C) I) σ).toRingHom.comp
        ((restrictedPowerSeriesMap (B := C) (I.map (algebraMap A B')) σ).comp
          (restrictedPowerSeriesMap (B := B') I σ)) :=
  (congrEquiv_restrictedPowerSeriesMap_comp (B := B) I σ).trans
    (congrEquiv_restrictedPowerSeriesMap_comp (B := B') I σ).symm

end

end TopologicalRing

end
