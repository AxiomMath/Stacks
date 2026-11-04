module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence

/-!
# Exterior products of cycles rationally equivalent to zero

Let `X` and `Y` be schemes locally of finite type over the spectrum of a field, let `α` be an
`r`-cycle on `X` and let `β` be an `s`-cycle on `Y`. Stacks 0B0S says that if either of `α` and
`β` is rationally equivalent to zero, then so is the exterior product `α × β`:

  `α ∼_rat 0` or `β ∼_rat 0`  implies  `α × β ∼_rat 0`.

The two one-sided statements are
`Stacks.Chow.exteriorProduct_mem_rationalEquivalences_left` and
`Stacks.Chow.exteriorProduct_mem_rationalEquivalences_right`, proved in
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence` as the two
well-definedness clauses of Stacks 0FBV. The source states the two cases together as one
disjunction, and that disjunction is what this file records, together with the congruence form
it is used for: replacing either factor by a rationally equivalent cycle leaves the exterior
product in the same rational equivalence class.

## Main results

* `Stacks.Chow.exteriorProduct_rationallyEquivalentToZero` — **Stacks 0B0S**: the exterior
  product of two cycles is rationally equivalent to zero as soon as one of the two factors is.
* `Stacks.Chow.rationallyEquivalent_exteriorProduct` — the congruence form: exterior products of
  rationally equivalent cycles are rationally equivalent. It follows from the disjunctive
  statement applied to `(α - α') × β` and to `α' × (β - β')`.

## Implementation notes

The base field is carried exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence`: `Subsingleton C.S`,
`IsIntegral C.S` and `JacobsonSpace C.S` together with the vanishing of the dimension function
at closed points. An integral scheme with one point is the spectrum of a field, and this is the
form in which flatness of an arbitrary morphism to such a base is available; varieties over a
field live over such a situation, so the statement below covers the source's setting and is
stated for arbitrary schemes locally of finite type over the base.

Nothing is assumed beyond the base. Stacks 02S1, the compatibility of flat pullback with
rational equivalence, holds in this repository for an arbitrary flat morphism of fixed relative
dimension, as `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`; the instances
it is needed at here are the projections `closure {x} ×_k Y ⟶ Y` of the products with a point
closure, which are flat by `Stacks.Chow.flat_pointClosurePullback_snd`, and the two together are
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds`. That is
what the two one-sided statements use internally, for `X ×_k Y` and for the product taken in the
opposite order, so neither of them — and hence neither statement below — carries an instance of
Stacks 02S1 as a hypothesis. Stacks 02S2 is needed only along closed immersions, where it is a
theorem in this repository, and so is not assumed either.

The conclusion is phrased with `Stacks.Chow.IsRationallyEquivalentToZero`, the Stacks 02RW
predicate spelling the source's `∼_rat 0`, rather than with membership in
`Stacks.Chow.rationalEquivalences`; the two agree by `Stacks.Chow.mem_rationalEquivalences`.

## References

* [Stacks Project, Tag 0B0S](https://stacks.math.columbia.edu/tag/0B0S)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 0B0S.** Let `X` and `Y` be schemes locally of finite type over the spectrum of a
field, let `α` be an `r`-cycle on `X` and let `β` be an `s`-cycle on `Y`. If `α` is rationally
equivalent to zero, or `β` is, then the exterior product `α × β` is rationally equivalent to
zero.

Each of the two cases is the corresponding well-definedness clause of Stacks 0FBV. The instances
of Stacks 02S1 along the projections of the products with a point closure that those clauses use
are supplied internally by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds`, so nothing
is assumed here. -/
@[stacks 0B0S "over a field, unconditionally"]
theorem exteriorProduct_rationallyEquivalentToZero (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ t : C.S, IsClosed ({t} : Set C.S) → C.dimensionFunction t = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (r s : ℤ)
    (α : CycleGroup C f r) (β : CycleGroup C g s)
    (h : IsRationallyEquivalentToZero C f r α ∨ IsRationallyEquivalentToZero C g s β) :
    IsRationallyEquivalentToZero C (pullback.fst f g ≫ f) (r + s)
      (exteriorProduct C f g r s α β) := by
  refine (mem_rationalEquivalences C (pullback.fst f g ≫ f) (r + s) _).1 ?_
  rcases h with hα | hβ
  · exact exteriorProduct_mem_rationalEquivalences_left C hδ f g r s
      ((mem_rationalEquivalences C f r α).2 hα) β
  · exact exteriorProduct_mem_rationalEquivalences_right C hδ f g r s α
      ((mem_rationalEquivalences C g s β).2 hβ)

/-- Exterior products of rationally equivalent cycles are rationally equivalent: the difference
`α × β - α' × β'` is the sum of `(α - α') × β` and `α' × (β - β')`, and each of those two is
rationally equivalent to zero by Stacks 0B0S. -/
theorem rationallyEquivalent_exteriorProduct (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ t : C.S, IsClosed ({t} : Set C.S) → C.dimensionFunction t = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (r s : ℤ)
    {α α' : CycleGroup C f r} {β β' : CycleGroup C g s}
    (hα : RationallyEquivalent C f r α α') (hβ : RationallyEquivalent C g s β β') :
    RationallyEquivalent C (pullback.fst f g ≫ f) (r + s)
      (exteriorProduct C f g r s α β) (exteriorProduct C f g r s α' β') := by
  have hfirst : exteriorProduct C f g r s (α - α') β =
      exteriorProduct C f g r s α β - exteriorProduct C f g r s α' β := by
    rw [map_sub (exteriorProduct C f g r s) α α', AddMonoidHom.sub_apply]
  have hsecond : exteriorProduct C f g r s α' (β - β') =
      exteriorProduct C f g r s α' β - exteriorProduct C f g r s α' β' :=
    map_sub (exteriorProduct C f g r s α') β β'
  have hsplit : exteriorProduct C f g r s (α - α') β +
      exteriorProduct C f g r s α' (β - β') =
      exteriorProduct C f g r s α β - exteriorProduct C f g r s α' β' := by
    rw [hfirst, hsecond, sub_add_sub_cancel]
  rw [RationallyEquivalent, ← hsplit]
  exact add_mem (exteriorProduct_mem_rationalEquivalences_left C hδ f g r s hα β)
    (exteriorProduct_mem_rationalEquivalences_right C hδ f g r s α' hβ)

end Stacks.Chow

end
