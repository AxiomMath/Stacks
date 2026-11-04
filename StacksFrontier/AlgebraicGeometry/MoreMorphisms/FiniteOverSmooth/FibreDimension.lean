module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# The local dimension of a fibre is a natural number

A scheme of finite type over a field has finite local dimension at every point, so the local
dimension of a fibre of a finite-type morphism at a point of the source is a natural number.
This is what lets Stacks 052E be applied inside the proof of Stacks 057K, the former taking the
relative dimension as a natural number together with the equation identifying it.

## Main results

* `AlgebraicGeometry.exists_topologicalKrullDimAt_fiber_eq_nat`: the local dimension of the
  fibre of a locally finite-type morphism at a point of the source is a natural number.

## Implementation notes

Finiteness of the dimension comes from the bound by `ringKrullDim Γ(Z, V)` on an affine open `V`
containing the point, which is finite because `Γ(Z, V)` is a finite-type algebra over the base
field and therefore a quotient of a polynomial ring in finitely many variables. Nonnegativity
comes from `Order.krullDim_nonneg` applied to the nonempty poset of irreducible closed subsets
of such a `V`.

## References

* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme of finite type over a field has a natural-number local dimension at each of its
points. -/
private theorem exists_topologicalKrullDimAt_eq_nat (Z : Scheme.{u}) (k : Type u) [Field k]
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] (z : Z) :
    ∃ n : ℕ, topologicalKrullDimAt Z z = n := by
  obtain ⟨N, hN⟩ := exists_topologicalKrullDimAt_le Z k g z
  have htop : topologicalKrullDimAt Z z ≠ ⊤ := ne_top_of_le_ne_top (natCast_ne_top_withBot N) hN
  obtain ⟨⟨U, hzU, hU, hEq⟩, -⟩ := topologicalKrullDimAt_isLeast Z z
  have h0 : 0 ≤ topologicalKrullDimAt Z z := by
    rw [hEq]
    have : Nonempty (IrreducibleCloseds ↥U) :=
      ⟨⟨closure {⟨z, hzU⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  generalize hd : topologicalKrullDimAt Z z = d at h0 htop
  cases d with
  | bot => exact False.elim (by simp at h0)
  | coe d =>
    cases d with
    | top => exact False.elim (htop rfl)
    | coe n => exact ⟨n, by simp⟩

/-- The local dimension of the fibre of a locally finite-type morphism, at the point of the fibre
determined by a point of the source, is a natural number. -/
theorem exists_topologicalKrullDimAt_fiber_eq_nat {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    ∃ n : ℕ, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))) inferInstance
  exact exists_topologicalKrullDimAt_eq_nat (f.fiber (f x)) (S.residueField (f x))
    (f.fiberToSpecResidueField (f x)) (f.asFiber x)

end AlgebraicGeometry

end
