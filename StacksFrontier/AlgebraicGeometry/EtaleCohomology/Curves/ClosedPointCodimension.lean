module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Every non-generic point of a curve has codimension one

The second map of the divisor sequence of Stacks 03RM,
`j_* 𝐆_{m,K} ⟶ ⨁_x i_{x,*} ℤ`,
is the order of vanishing at the closed points. Mathlib's order of vanishing,
`AlgebraicGeometry.Scheme.ord`, is defined on the function field of a locally Noetherian integral
scheme and is meaningful exactly at the points `z` with `Order.coheight z = 1` — the points of
codimension one, where the stalk has Krull dimension one. This file supplies that hypothesis on a
curve: on a curve *every* point other than the generic point has codimension one, so the order of
vanishing is available at all of them, and in particular at every closed point.

The two halves of the equality `coheight x = 1` are elementary once the order on the points of a
scheme is identified. That order is the specialization preorder with `a ≤ b ↔ b ⤳ a`
(`AlgebraicGeometry.le_iff_specializes`), so the generic point is the greatest element and
`coheight` counts chains of generalizations, i.e. codimension.

* `coheight x ≤ 1`: the Krull dimension of the points of a scheme, ordered by specialization,
  agrees with the topological Krull dimension of its space, because the irreducible closed subsets
  of a sober T0 space are order-isomorphic to its points
  (`TopologicalSpace.irreducibleSetEquivPoints`); and a curve has topological Krull dimension one.
* `1 ≤ coheight x`: the generic point is a strictly greater point, and a point with something
  strictly above it does not have coheight zero.

## Main results

* `AlgebraicGeometry.coheight_le_topologicalKrullDim`: the codimension of a point of a scheme is
  at most the topological Krull dimension of the scheme.
* `AlgebraicGeometry.lt_genericPoint`: on an irreducible scheme every point other than the
  generic point is strictly below it in the specialization order.
* `AlgebraicGeometry.IsCurve.coheight_eq_one`: **every non-generic point of a curve has
  codimension one.**
* `AlgebraicGeometry.IsCurve.krullDimLE_stalk`: the local ring of a curve at a non-generic point
  has Krull dimension at most one.
* `AlgebraicGeometry.IsCurve.ordHom`: the order of vanishing at a non-generic point of a locally
  Noetherian curve, as a multiplicative map on the function field, with
  `AlgebraicGeometry.IsCurve.ordHom_of_isUnit`.

## Implementation notes

`AlgebraicGeometry.coheight_le_topologicalKrullDim` holds for an arbitrary scheme; only
`AlgebraicGeometry.IsCurve.coheight_eq_one` uses the curve hypothesis, and it uses nothing from it
but integrality and the dimension. Local Noetherianity is an explicit hypothesis on the
order-of-vanishing statement rather than deduced from finite type over the field: this library has
no instance carrying Stacks 01T6, that a scheme of finite type over a Noetherian scheme is locally
Noetherian. Nothing here produces an `IsDiscreteValuationRing` stalk: that needs the stalk to be
regular, i.e. the curve to be smooth, and regularity of a smooth scheme over a field is not
available in this library.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the divisor sequence,
  whose second map is the order of vanishing at the closed points.
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23): curves.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace WithZero
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

/-- **The codimension of a point of a scheme is at most the topological Krull dimension of the
scheme.** The points of a scheme, ordered by specialization, are order-isomorphic to the
irreducible closed subsets of its space, whose Krull dimension is by definition the topological
Krull dimension. -/
theorem coheight_le_topologicalKrullDim {X : Scheme.{u}} (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (X : Type u)))]
  exact Order.coheight_le_krullDim x

/-- **On an irreducible scheme the generic point is strictly above every other point.** The
generic point is a generalization of every point, and the only generalization of the generic
point is itself. -/
theorem lt_genericPoint {X : Scheme.{u}} [IrreducibleSpace X] {x : X}
    (hx : x ≠ genericPoint X) : x < genericPoint X :=
  ⟨genericPoint_specializes x,
    fun h => hx (Stacks.EtaleCohomology.eq_genericPoint_of_specializes X h)⟩

namespace IsCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]

/-- **Every point of a curve other than the generic point has codimension one.** The dimension of
the curve bounds the codimension above, and the generic point lies strictly above the point, which
bounds it below.

This is the hypothesis under which `AlgebraicGeometry.Scheme.ord` is the order of vanishing at a
point, and hence the input to the second map of the divisor sequence of Stacks 03RM: on a curve
the order of vanishing is defined at every closed point. -/
theorem coheight_eq_one {x : X} (hx : x ≠ genericPoint X) : coheight x = 1 := by
  refine le_antisymm ?_ ?_
  · have h := (coheight_le_topologicalKrullDim x).trans_eq
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))
    exact_mod_cast h
  · rw [Order.one_le_iff_ne_zero, ← Nat.cast_zero, ← Nat.cast_zero]
    intro h
    exact absurd (Order.coheight_le_coe_iff.1 h.le _ (lt_genericPoint hx)) (by simp)

/-- **The local ring of a curve at a non-generic point has Krull dimension at most one.** This is
as far as the dimension of the curve alone takes one towards discrete valuations: upgrading
`Ring.KrullDimLE 1` to `IsDiscreteValuationRing` needs the stalk to be regular, which is
smoothness of the curve and is not part of `AlgebraicGeometry.IsCurve`. -/
theorem krullDimLE_stalk {x : X} (hx : x ≠ genericPoint X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
  krullDimLE_of_coheight_le (coheight_eq_one f hx).le

/-- **The order of vanishing at a non-generic point of a locally Noetherian curve**, as a
multiplicative map `K → ℤᵐ⁰` on the function field. It is Mathlib's
`AlgebraicGeometry.Scheme.ordHom` at the codimension-one witness `IsCurve.coheight_eq_one`, which
is what makes it available at *every* point of a curve other than the generic one, and in
particular at every closed point.

This is the map whose values are the coefficients of the divisor of a rational function, hence the
local content of the second map `j_* 𝐆_{m,K} ⟶ ⨁_x i_{x,*} ℤ` of the divisor sequence of
Stacks 03RM. -/
def ordHom [IsLocallyNoetherian X] {x : X} (hx : x ≠ genericPoint X) :
    X.functionField →*₀ ℤᵐ⁰ :=
  X.ordHom x (coheight_eq_one f hx)

/-- **The order of vanishing at a non-generic point of a curve is trivial on functions that are
invertible near that point.** The function is a section `a` of the structure sheaf on an open `U`
containing `x`, and its image in the function field is the germ at `x` carried along the
specialization of the generic point to `x`.

Phrasing the image this way rather than as `Scheme.germToFunctionField U a` is what lets the
statement name only the data it uses: the restriction map to the function field is defined on
`Γ(X, U)` only for a *nonempty* `U`, so stating the equation with it would force a `Nonempty U`
hypothesis that `hxU` already contains. Here the nonemptiness is derived inside the proof, and
`Scheme.algebraMap_germ_eq_germToFunctionField` — a `simp` lemma — rewrites the left-hand side
into the `germToFunctionField` form for any consumer that does have the instance. -/
theorem ordHom_of_isUnit [IsLocallyNoetherian X] {x : X} (hx : x ≠ genericPoint X) {U : X.Opens}
    (hxU : x ∈ U) {a : Γ(X, U)} (ha : IsUnit a) :
    ordHom f hx (algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ U x hxU a)) = 1 := by
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField _ hxU]
  exact Scheme.ordHom_of_isUnit ha (coheight_eq_one f hx) hxU

end IsCurve

end AlgebraicGeometry

end
