module

public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria

/-!
# Finite fibres of a morphism locally of finite type

Let `f : X ⟶ S` be locally of finite type and let `s : S` be a point whose set-theoretic fibre
`f ⁻¹' {s}` is finite. Then the scheme-theoretic fibre `f.fiber s` is a finite discrete space,
and `f` is quasi-finite at every point of `X` lying over `s`.

The fibre is locally of finite type over `Spec κ(s)`, hence a Jacobson space, and a finite
Jacobson space is discrete. Quasi-finiteness at a point of the fibre is then isolation of that
point, which is automatic in a discrete space.

Globally, finiteness of all the fibres is what distinguishes a quasi-finite morphism among the
quasi-compact morphisms locally of finite type.

## Main results

* `AlgebraicGeometry.finite_fiber_of_finite_preimage`: the scheme-theoretic fibre is finite.
* `AlgebraicGeometry.discreteTopology_fiber_of_finite_preimage`: it is discrete.
* `AlgebraicGeometry.quasiFiniteAt_of_finite_preimage`: `f` is quasi-finite at every point over
  `s`.

Together these are **Stacks Project, Tag 02NG**.

* `AlgebraicGeometry.quasiFinite_conditions_iff_finite_fibers`: a morphism is quasi-finite
  exactly when it is locally of finite type, quasi-compact and has finite fibres.

## Implementation notes

Finiteness of the scheme-theoretic fibre is transported from finiteness of the set-theoretic
fibre along `AlgebraicGeometry.Scheme.Hom.fiberHomeo`, the homeomorphism `f.fiber s ≃ₜ f ⁻¹' {s}`;
the two notions of fibre are genuinely different objects, and the tagged statements of this area
use the set-theoretic one.

`JacobsonSpace (f.fiber s)` is already an instance in Mathlib for `f` locally of finite type, and
`DiscreteTopology` then follows from Mathlib's instance for a finite Jacobson space, so the
Jacobson step of the source (Tags 02J6 and 07JU) needs no repo-local input.

The quasi-finiteness statement is phrased with a point `x : X` together with `hx : f x = s`
rather than with a point of `f.fiber s`, because `AlgebraicGeometry.quasiFiniteAt` is a predicate
on points of the source. The proof substitutes `s := f x`, which avoids transporting
`f.asFiber x : f.fiber (f x)` across the equality of base points. The equivalence between
quasi-finiteness at `x` and isolation of `f.asFiber x` is item 1 ↔ item 2 of
`AlgebraicGeometry.quasiFiniteAt_tfae`, whose `List.TFAE.out` indices are one-based on this pin.

As in `AlgebraicGeometry.QuasiFinite.Defs`, quasi-finiteness of a morphism is the conjunction of
the three typeclasses `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`
and `AlgebraicGeometry.LocallyQuasiFinite`, so the global characterization is stated as an
equivalence of conjunctions in which the first two conditions are common to both sides.

## References

* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
* [Stacks Project, Tag 02NH](https://stacks.math.columbia.edu/tag/02NH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02NG.** If the set-theoretic fibre of `f` over `s` is finite, then so
is the scheme-theoretic fibre: the two are homeomorphic. -/
@[stacks 02NG "the fibre is finite"]
theorem finite_fiber_of_finite_preimage {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (hfin : (f ⁻¹' {s}).Finite) : Finite (f.fiber s) :=
  have : Finite (f ⁻¹' {s}) := hfin.to_subtype
  Finite.of_equiv _ (f.fiberHomeo s).toEquiv.symm

/-- **Stacks Project, Tag 02NG.** A fibre of a morphism locally of finite type that is finite as
a set is a discrete topological space: it is locally of finite type over the residue field at the
base point, hence Jacobson, and a finite Jacobson space is discrete. -/
@[stacks 02NG "the fibre is discrete"]
theorem discreteTopology_fiber_of_finite_preimage {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) (hfin : (f ⁻¹' {s}).Finite) :
    DiscreteTopology (f.fiber s) :=
  have : Finite (f.fiber s) := finite_fiber_of_finite_preimage f s hfin
  inferInstance

/-- **Stacks Project, Tag 02NG.** A morphism locally of finite type with finite fibre over `s` is
quasi-finite at every point lying over `s`: the point is isolated in the fibre, because the fibre
is discrete. -/
@[stacks 02NG "quasi-finite at every point over the base point"]
theorem quasiFiniteAt_of_finite_preimage {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (hfin : (f ⁻¹' {s}).Finite) (x : X) (hx : f x = s) : quasiFiniteAt f x := by
  subst hx
  have := discreteTopology_fiber_of_finite_preimage f (f x) hfin
  exact ((quasiFiniteAt_tfae f x).out 2 1).mp (isOpen_discrete _)

/-- **Stacks Project, Tag 02NH.** A morphism of schemes is quasi-finite exactly when it is
locally of finite type, quasi-compact and all of its set-theoretic fibres are finite. -/
@[stacks 02NH]
theorem quasiFinite_conditions_iff_finite_fibers {X S : Scheme.{u}} (f : X ⟶ S) :
    ((LocallyOfFiniteType f ∧ QuasiCompact f) ∧ LocallyQuasiFinite f) ↔
      ((LocallyOfFiniteType f ∧ QuasiCompact f) ∧ ∀ s, (f ⁻¹' {s}).Finite) := by
  constructor <;> rintro ⟨⟨hft, hqc⟩, h⟩ <;> let _ := hft <;> let _ := hqc
  · exact ⟨⟨hft, hqc⟩, locallyQuasiFinite_iff_finite_preimage_singleton.mp h⟩
  · exact ⟨⟨hft, hqc⟩, locallyQuasiFinite_iff_finite_preimage_singleton.mpr h⟩

end AlgebraicGeometry

end
