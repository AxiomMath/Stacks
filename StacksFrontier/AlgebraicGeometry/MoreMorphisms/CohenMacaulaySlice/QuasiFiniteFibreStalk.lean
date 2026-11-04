module

public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiberSequence
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.SmoothPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring of a fibre at a quasi-finite point, and at a point of a smooth morphism

Two local computations feed the slicing construction of **Stacks 06MF**, both read on the local
ring `𝒪_{X_y, p}` of a scheme-theoretic fibre, which
`AlgebraicGeometry.quotientStalkEquivFiberStalk` presents as the quotient
`𝒪_{X, x} / 𝔪_y·𝒪_{X, x}`.

* If `f` is quasi-finite at `x` then that quotient is **zero-dimensional**: the point of the
  fibre is isolated (**Stacks 0397**), and an isolated point of a scheme has no proper
  generalization, so the coheight computing the dimension of its local ring vanishes.
* If `f` is **smooth** then that quotient is a **regular** local ring, hence Cohen–Macaulay, and
  Noetherian.

The two together are the hypotheses of **Stacks 06LC** in the form
`Stacks.CohenMacaulay.exists_isRegular_map_mem_maximalIdeal_of_ringKrullDim_quotient_eq_zero`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_isIsolatedPoint`: the local ring of a scheme
  at an isolated point is zero-dimensional.
* `AlgebraicGeometry.ringKrullDim_fiberStalk_eq_zero_of_quasiFiniteAt`: the local ring of the
  fibre at a point of quasi-finiteness is zero-dimensional.
* `AlgebraicGeometry.ringKrullDim_quotient_stalkFibreIdeal_eq_zero_of_isIsolatedPoint` and
  `AlgebraicGeometry.ringKrullDim_quotient_stalkFibreIdeal_eq_zero_of_quasiFiniteAt`: the same
  read on `𝒪_{X, x} / 𝔪_{f x}·𝒪_{X, x}`.
* `AlgebraicGeometry.isRegularLocalRing_fiberStalk_of_smooth`,
  `AlgebraicGeometry.isCohenMacaulayLocalRing_fiberStalk_of_smooth` and
  `AlgebraicGeometry.isNoetherianRing_fiberStalk_of_locallyOfFiniteType`: the local ring of a
  fibre of a smooth morphism is a regular, hence Cohen–Macaulay, Noetherian local ring.

## Implementation notes

The dimension of a local ring of a scheme is the coheight of the point in the specialization
order (`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`), whose maximal elements are the
generic points; so it suffices that the isolated point admit no proper generalization, and that
holds because an open set meeting the closure of `{y}` meets `{y}`.

Regularity of the fibre at a point of a smooth morphism is
`AlgebraicGeometry.isRegularLocalRing_closedFibre_of_smooth`, which states it for the quotient
presentation; `AlgebraicGeometry.quotientStalkEquivFiberStalk` carries it to the fibre and back.
No separability hypothesis on residue fields enters: the route is through
`Algebra.isRegularRing_of_smooth`, which has none, and not through
`AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk`, which does.

No `@[stacks]` attribute is claimed: **Stacks 0397** is registered on
`AlgebraicGeometry.quasiFiniteAt_iff_fiberDimensionAt_eq_zero` and **Stacks 07NF** on
`Algebra.isRegularRing_of_smooth`; these are the two read on the local ring of a fibre.

## References

* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
* [Stacks Project, Tag 06LC](https://stacks.math.columbia.edu/tag/06LC)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 07NF](https://stacks.math.columbia.edu/tag/07NF)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **An isolated point of a scheme has a zero-dimensional local ring.**  A point whose
singleton is open admits no proper generalization — an open set meeting `closure {y}` meets
`{y}` — so it is maximal in the specialization order, and the coheight computing the dimension of
its local ring is zero. -/
@[sga "3 VIB 5.2" "For discrete S"]
theorem ringKrullDim_stalk_eq_zero_of_isIsolatedPoint {X : Scheme.{u}} {x : X}
    (hx : IsIsolatedPoint x) : ringKrullDim (X.presheaf.stalk x) = 0 := by
  have hmax : IsMax x := by
    intro y hxy
    have hyx : y ⤳ x := hxy
    have : y = x := by
      have hmem : y ∈ ({x} : Set X) :=
        (hyx.mem_open hx (Set.mem_singleton x))
      exact hmem
    exact this ▸ le_rfl
  rw [ringKrullDim_stalk_eq_coheight]
  simpa only [WithBot.coe_zero] using
    congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) (Order.coheight_eq_zero.mpr hmax)

/-- **The local ring of a fibre of a morphism locally of finite type is Noetherian**, the fibre
being a locally Noetherian scheme. -/
theorem isNoetherianRing_fiberStalk_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) (z : f.fiber y) :
    IsNoetherianRing ((f.fiber y).presheaf.stalk z) :=
  have _ : IsLocallyNoetherian (f.fiber y) :=
    Stacks.AlgebraicGeometry.isLocallyNoetherian_fiber f y
  inferInstance

/-- **The local ring of a fibre at a point of quasi-finiteness is zero-dimensional.**  By
**Stacks 0397** quasi-finiteness at `x` says that the local dimension of the fibre at the
corresponding point is zero, which in a locally Noetherian scheme means the point is
isolated. -/
theorem ringKrullDim_fiberStalk_eq_zero_of_quasiFiniteAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) (hx : quasiFiniteAt f x) :
    ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = 0 :=
  have _ : IsLocallyNoetherian (f.fiber (f x)) :=
    Stacks.AlgebraicGeometry.isLocallyNoetherian_fiber f (f x)
  ringKrullDim_stalk_eq_zero_of_isIsolatedPoint
    ((topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint _ _).mp
      ((quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mp hx))

/-- **The closed fibre of the stalk map at an isolated point of the fibre is
zero-dimensional.**  This is `AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_isIsolatedPoint`
on the fibre, transported by `AlgebraicGeometry.quotientStalkEquivFiberStalk`, which identifies
the local ring of the fibre with `𝒪_{X, x} / 𝔪_{f x}·𝒪_{X, x}`.

No finiteness hypothesis on `f` is needed, which is what makes this applicable to a morphism
factoring through a scheme-theoretic fibre. -/
theorem ringKrullDim_quotient_stalkFibreIdeal_eq_zero_of_isIsolatedPoint {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (hx : IsIsolatedPoint (f.asFiber x)) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
        Ideal.map (f.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (f x)))) = 0 :=
  ((quotientStalkEquivFiberStalk f x).ringKrullDim).trans
    (ringKrullDim_stalk_eq_zero_of_isIsolatedPoint hx)

/-- **The closed fibre of the stalk map at a point of quasi-finiteness is zero-dimensional.**
This is `AlgebraicGeometry.ringKrullDim_fiberStalk_eq_zero_of_quasiFiniteAt` transported by
`AlgebraicGeometry.quotientStalkEquivFiberStalk`, which identifies the local ring of the fibre
with `𝒪_{X, x} / 𝔪_{f x}·𝒪_{X, x}`. -/
@[ega "0 7.4.4" "(i)"]
theorem ringKrullDim_quotient_stalkFibreIdeal_eq_zero_of_quasiFiniteAt {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (hx : quasiFiniteAt f x) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
        Ideal.map (f.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (f x)))) = 0 :=
  ((quotientStalkEquivFiberStalk f x).ringKrullDim).trans
    (ringKrullDim_fiberStalk_eq_zero_of_quasiFiniteAt f x hx)

/-- **The local ring of a fibre of a smooth morphism is a regular local ring.**  The fibre is
smooth over the residue field of its base point, hence a regular scheme;
`AlgebraicGeometry.isRegularLocalRing_closedFibre_of_smooth` states that for the quotient
presentation of the local ring of the fibre, and
`AlgebraicGeometry.quotientStalkEquivFiberStalk` carries it to the fibre itself. -/
@[ega "IV 17.5.8" "(iii), special case", sga "1 II 5.3" "special case"]
theorem isRegularLocalRing_fiberStalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : IsRegularLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  have h := isRegularLocalRing_closedFibre_of_smooth f x
  exact IsRegularLocalRing.of_ringEquiv (quotientStalkEquivFiberStalk f x)

/-- **The local ring of a fibre of a smooth morphism is Cohen–Macaulay**, being a regular local
ring. -/
theorem isCohenMacaulayLocalRing_fiberStalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) :
    letI := isNoetherianRing_fiberStalk_of_locallyOfFiniteType f (f x) (f.asFiber x)
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  let := isNoetherianRing_fiberStalk_of_locallyOfFiniteType f (f x) (f.asFiber x)
  have := isRegularLocalRing_fiberStalk_of_smooth f x
  exact IsRegularLocalRing.isCohenMacaulayLocalRing _

end AlgebraicGeometry

end
