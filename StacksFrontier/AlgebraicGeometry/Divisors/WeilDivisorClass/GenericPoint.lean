module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishingInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisor

/-!
# Prime divisors and their generic points

A prime divisor of a scheme `X` is an integral closed subscheme of codimension one, and is
therefore determined by its generic point, which is a point of `X` of coheight one. The support
of a prime divisor is the closure of its generic point, distinct prime divisors have distinct
generic points, the generic point has coheight one, and every point of coheight one is the
generic point of a prime divisor.

As a consequence, the local finiteness condition defining a Weil divisor, which is about the
supports, can be checked on generic points:
`AlgebraicGeometry.mem_weilDivisor_of_forall_exists_open` recognises a coefficient family as a
Weil divisor as soon as every point has an open neighbourhood containing only finitely many
generic points of prime divisors with nonzero coefficient.

## Main definitions

* `AlgebraicGeometry.PrimeDivisor.ofCoheightOne` — the prime divisor whose generic point is a
  given point of coheight one.

## Main results

* `AlgebraicGeometry.PrimeDivisor.support_eq_closure` — the support of a prime divisor is the
  closure of its generic point.
* `AlgebraicGeometry.PrimeDivisor.genericPoint_injective` — a prime divisor is determined by
  its generic point.
* `AlgebraicGeometry.PrimeDivisor.coheight_genericPoint` — the generic point of a prime divisor
  has coheight one.
* `AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne` — conversely, every point of
  coheight one is the generic point of a prime divisor.
* `AlgebraicGeometry.mem_weilDivisor_of_forall_exists_open` — a sufficient criterion, phrased
  on generic points, for a coefficient family to be a Weil divisor.

## Implementation notes

The bijection between integral closed subschemes of `X` and points of `X` is
`Stacks.Chow.integralComponentAt` and `Stacks.Chow.genericPointOf`, and
`AlgebraicGeometry.PrimeDivisor.genericPoint` is definitionally `Stacks.Chow.genericPointOf` of
the underlying ideal sheaf. The codimension condition transports through
`AlgebraicGeometry.coheight_eq_codimension_closureSingleton`.

## References

* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
-/

@[expose] public noncomputable section

open Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

namespace PrimeDivisor

/-- The support of a prime divisor is the closure of its generic point. -/
theorem support_eq_closure (Z : PrimeDivisor X) :
    Z.support = closure ({Z.genericPoint} : Set X) :=
  Stacks.Chow.support_eq_closure_genericPointOf Z.idealSheaf Z.integral

/-- A prime divisor is determined by its generic point. -/
theorem genericPoint_injective : Function.Injective (genericPoint (X := X)) := by
  intro Z W h
  have hI : Z.idealSheaf = W.idealSheaf := by
    rw [← Stacks.Chow.integralComponentAt_genericPointOf Z.idealSheaf Z.integral,
      ← Stacks.Chow.integralComponentAt_genericPointOf W.idealSheaf W.integral]
    exact congrArg Stacks.Chow.integralComponentAt h
  cases Z with | mk IZ hIZ hcodZ =>
  cases W with | mk IW hIW hcodW =>
  cases hI
  rfl

/-- The generic point of a prime divisor has coheight one. -/
theorem coheight_genericPoint (Z : PrimeDivisor X) : coheight Z.genericPoint = 1 :=
  (coheight_eq_codimension_closureSingleton _).trans Z.codimension_closureSingleton_genericPoint

/-- The prime divisor attached to a point of coheight one: the integral closed subscheme
`Stacks.Chow.integralComponentAt` of which it is the generic point. Together with
`AlgebraicGeometry.PrimeDivisor.genericPoint_injective` this says that the prime divisors of `X`
are its points of coheight one.

**Stacks 02RO**, read on prime divisors. -/
def ofCoheightOne (x : X) (hx : coheight x = 1) : PrimeDivisor X where
  idealSheaf := Stacks.Chow.integralComponentAt x
  integral := Stacks.Chow.isIntegral_integralComponentAt x
  codimension_one := by
    have := Stacks.Chow.isIntegral_integralComponentAt x
    rw [show (Stacks.Chow.integralComponentAt x).subschemeι
          (_root_.genericPoint (Stacks.Chow.integralComponentAt x).subscheme) = x from
        Stacks.Chow.genericPointOf_integralComponentAt x,
      ← coheight_eq_codimension_closureSingleton]
    exact hx

/-- Every point of coheight one is the generic point of a prime divisor, namely of
`AlgebraicGeometry.PrimeDivisor.ofCoheightOne`. -/
@[simp]
theorem genericPoint_ofCoheightOne (x : X) (hx : coheight x = 1) :
    (ofCoheightOne x hx).genericPoint = x :=
  Stacks.Chow.genericPointOf_integralComponentAt x

end PrimeDivisor

/-- A coefficient family on the prime divisors of `X` is a Weil divisor as soon as every point
has an **open** neighbourhood containing only finitely many generic points of prime divisors
with nonzero coefficient. -/
theorem mem_weilDivisor_of_forall_exists_open {D : PrimeDivisor X → ℤ}
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      {Z : PrimeDivisor X | Z.genericPoint ∈ U ∧ D Z ≠ 0}.Finite) :
    D ∈ WeilDivisor X := by
  intro x
  obtain ⟨U, hUopen, hxU, hfin⟩ := h x
  refine ⟨U, hUopen.mem_nhds hxU, hfin.subset fun Z hZ ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hZ
  have hD : D Z ≠ 0 := by
    by_contra hD
    rw [ite_eq_left hD] at hZ
    exact hZ.ne_empty (Set.empty_inter U)
  rw [ite_eq_right hD] at hZ
  obtain ⟨y, hyZ, hyU⟩ := hZ
  rw [Z.support_eq_closure] at hyZ
  exact ⟨(specializes_iff_mem_closure.mpr hyZ).mem_open hUopen hyU, hD⟩

end AlgebraicGeometry

end
