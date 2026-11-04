module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrChowSituation
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FibrePointDimension

/-!
# Fibre dimensions over a discrete valuation ring

Let `R` be a discrete valuation ring and let `V` be a scheme locally of finite type over
`Spec R`. The spectrum of `R` has two points, and the dimension function of the base situation
`Stacks.Chow.dvrChowSituation R` takes the value `1` at the generic point and `0` at the closed
point. So the relative dimension over `Spec R` of a point of a fibre is its dimension computed
inside that fibre, shifted by `1` on the generic fibre and not at all on the special fibre.

When `V` is irreducible and its generic point lies on the generic fibre, where it has dimension
`r`, this computes the delta-dimension of `V` over `R` to be `r + 1`: the generic fibre
contributes `r`, and the base contributes the one dimension of `Spec R`. Feeding that value into
the codimension-one criterion of Stacks 02RK then says that a point of the special fibre is the
generic point of a prime divisor of `V` exactly when it has dimension `r` in that fibre — the
special fibre has the same dimension as the generic fibre at a codimension-one point, which is
the shape in which the criterion is used for specialization of cycles.

## Main results

* `Stacks.Chow.relativeDimension_dvrChowSituation_closedPoint`,
  `Stacks.Chow.relativeDimension_dvrChowSituation_genericPoint` — the relative dimension over
  `Spec R` of a point of the special, respectively generic, fibre.
* `Stacks.Chow.schemeDeltaDimension_dvrChowSituation` — the delta-dimension of an irreducible
  `V` whose generic point has dimension `r` on the generic fibre is `r + 1`.
* `Stacks.Chow.coheight_fiberι_closedPoint_eq_one_iff` — the codimension-one criterion on the
  special fibre.

## Implementation notes

All four statements are the single computation
`Stacks.Chow.relativeDimension_fiberι` specialised to the two points of `Spec R`, whose values
of the dimension function are `Stacks.Chow.dvrChowSituation_dimensionFunction_closedPoint` and
`Stacks.Chow.dvrChowSituation_dimensionFunction_genericPoint`. Since `dvrChowSituation` is an
`abbrev`, its base scheme is reducibly `Spec R` and a morphism `V ⟶ Spec R` is accepted directly
where a morphism to the base scheme of the situation is expected.

The hypothesis on the generic point is phrased as a point `ξ` of the generic fibre together with
an equation `(sV.fiberι η).base ξ = genericPoint V`, rather than as a nonemptiness statement
about the generic fibre, because the dimension `r` has to be measured at that specific point.

## References

* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {V : Scheme.{u}}
  (sV : V ⟶ Spec (.of R)) [LocallyOfFiniteType sV]

/-- The relative dimension over `Spec R` of a point of the special fibre of `V` is its dimension
inside that fibre: the dimension function of `Stacks.Chow.dvrChowSituation` vanishes at the
closed point. -/
theorem relativeDimension_dvrChowSituation_closedPoint
    (v : sV.fiber (IsLocalRing.closedPoint R)) :
    relativeDimension (dvrChowSituation R).dimensionFunction sV
        ((sV.fiberι (IsLocalRing.closedPoint R)).base v) =
      fiberPointDimension sV (IsLocalRing.closedPoint R) v := by
  have h := relativeDimension_fiberι (dvrChowSituation R).dimensionFunction sV
    (IsLocalRing.closedPoint R) v
  rwa [dvrChowSituation_dimensionFunction_closedPoint, zero_add] at h

/-- The relative dimension over `Spec R` of a point of the generic fibre of `V` is one more than
its dimension inside that fibre: the dimension function of `Stacks.Chow.dvrChowSituation` is `1`
at the generic point. -/
theorem relativeDimension_dvrChowSituation_genericPoint
    (ξ : sV.fiber (genericPoint (Spec (.of R)))) :
    relativeDimension (dvrChowSituation R).dimensionFunction sV
        ((sV.fiberι (genericPoint (Spec (.of R)))).base ξ) =
      1 + fiberPointDimension sV (genericPoint (Spec (.of R))) ξ := by
  rw [relativeDimension_fiberι, dvrChowSituation_dimensionFunction_genericPoint]

/-- The delta-dimension over `R` of an irreducible scheme `V` whose generic point lies on the
generic fibre, with dimension `r` there, is `r + 1`. -/
theorem schemeDeltaDimension_dvrChowSituation [IrreducibleSpace V] {r : ℕ}
    (ξ : sV.fiber (genericPoint (Spec (.of R))))
    (hξ : (sV.fiberι (genericPoint (Spec (.of R)))).base ξ = genericPoint V)
    (hdim : fiberPointDimension sV (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    schemeDeltaDimension (dvrChowSituation R) sV = (((r : ℤ) + 1 : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint, ← hξ,
    relativeDimension_dvrChowSituation_genericPoint, hdim]
  exact congrArg (fun z : ℤ => (z : EInt)) (add_comm 1 (r : ℤ))

/-- **The codimension-one criterion on the special fibre.** Let `V` be integral and locally of
finite type over a discrete valuation ring `R`, with generic point lying on the generic fibre
and of dimension `r` there. A point of the special fibre is the generic point of a prime divisor
of `V`, that is has codimension one, exactly when its dimension inside the special fibre is
`r`. -/
theorem coheight_fiberι_closedPoint_eq_one_iff [IsIntegral V] {r : ℕ}
    (ξ : sV.fiber (genericPoint (Spec (.of R))))
    (hξ : (sV.fiberι (genericPoint (Spec (.of R)))).base ξ = genericPoint V)
    (hdim : fiberPointDimension sV (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (v : sV.fiber (IsLocalRing.closedPoint R)) :
    Order.coheight ((sV.fiberι (IsLocalRing.closedPoint R)).base v) = 1 ↔
      fiberPointDimension sV (IsLocalRing.closedPoint R) v = (r : ℤ) := by
  rw [← relativeDimension_eq_sub_one_iff_coheight_eq_one (dvrChowSituation R) sV
      (schemeDeltaDimension_dvrChowSituation sV ξ hξ hdim),
    relativeDimension_dvrChowSituation_closedPoint]
  constructor <;> intro h <;> omega

end Stacks.Chow

end
